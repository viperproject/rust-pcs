// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Contains functions for constructing a pointwise EPCS

extern crate im;
use super::epcs::{Borrow, BorrowOracle, BorrowType, Epcs, Place, PlaceBase, RefersTo};

use super::common::{MirAnalysisResult, WorkItem};
use super::fra_builder::FRABuilder;

//use log::{debug, info, info, warn};
use log::info;
use rustc_middle::mir;
use rustc_middle::ty;

// TODO:
// * Centralise borrow expiries - currently it's distributed across many functions
// * Check that the PCS actually works
// * Handle two phase borrows
// * Handle aliasing (ask Vytautas)

pub struct EPCSBuilder<'a, 'tcx: 'a> {
    tcx: ty::TyCtxt<'tcx>,
    mir: &'a mir::Body<'tcx>,

    result: MirAnalysisResult<Epcs>,
    work_queue: Vec<WorkItem>,
    inline_const_counter: usize,
}

pub fn compute_epcs<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    mir: &'tcx mir::Body<'tcx>,
) -> MirAnalysisResult<Epcs> {
    let mut builder = EPCSBuilder::new(tcx, mir);
    builder.initalise_epcs();
    builder.initalise_work_queue();
    builder.run();

    builder.result
}

impl<'a, 'tcx> EPCSBuilder<'a, 'tcx> {
    pub fn new(tcx: ty::TyCtxt<'tcx>, mir: &'tcx mir::Body<'tcx>) -> Self {
        EPCSBuilder {
            tcx,
            mir,

            result: MirAnalysisResult::new(),
            work_queue: Vec::new(),
            inline_const_counter: 0,
        }
    }

    // Next three functions or so based on Prusti MIR liveness code
    pub fn initalise_work_queue(&mut self) {
        info!("[enter] initalise_work_queue");

        let bb = mir::BasicBlock::from_u32(0);
        let mir::BasicBlockData { ref statements, .. } = self.mir[bb];
        for statement_index in 0..statements.len() {
            let location = mir::Location {
                block: bb,
                statement_index,
            };
            self.work_queue
                .push(WorkItem::ApplyStatementEffects(location));
        }
        self.work_queue.push(WorkItem::ApplyTerminatorEffects(bb));
        self.work_queue.reverse();
    }

    pub fn initalise_epcs(&mut self) {
        let mut initial_pcs = Epcs::new();
        for arg in self.mir.args_iter() {
            let arg_place = Place::Concrete(PlaceBase::Local(arg.as_u32()), Vec::new());
            initial_pcs = Epcs::add_place(initial_pcs, arg_place.clone());

            // TODO(ws): Any references in any structs/tuples need to be BlackBoxes
            initial_pcs = match self.mir.local_decls[arg].ty.kind {
                ty::TyKind::Ref(_, _, mir::terminator::Mutability::Mut) => Epcs::add_borrow(
                    initial_pcs,
                    arg_place,
                    Borrow::Mutable(RefersTo::Definite(Place::BlackBox(
                        PlaceBase::Arg(arg.as_u32()),
                        Vec::new(),
                    ))),
                ),
                ty::TyKind::Ref(_, _, mir::terminator::Mutability::Not) => Epcs::add_borrow_new(
                    initial_pcs,
                    arg_place,
                    BorrowType::Shared,
                    Place::WildcardArg,
                ),
                ty::TyKind::FnPtr(_) => unimplemented!("fn ptrs not supported"),
                ty::TyKind::Adt(_, substs) => {
                    assert!(
                        substs.regions().count() == 0,
                        "passing structs with references is not supported"
                    );
                    initial_pcs
                }
                _ => initial_pcs,
            }
        }

        self.result
            .before_block
            .insert(mir::BasicBlock::from_u32(0), initial_pcs);
    }

    /// Run the analysis up to a fix-point.
    pub fn run(&mut self) {
        info!("[enter] run");
        let mut counter = 0; // For debugging.
        while let Some(work_item) = self.work_queue.pop() {
            assert!(
                counter <= 1000000,
                "EPCS analysis (EPCS) does not converge."
            );

            match work_item {
                WorkItem::ApplyStatementEffects(location) => {
                    self.apply_statement_effects(location);
                }
                WorkItem::ApplyTerminatorEffects(bb) => {
                    self.apply_terminator_effects(bb);
                }
                WorkItem::MergeEffects(bb) => {
                    self.apply_merge_effects(bb);
                }
            }
            counter += 1;
        }
    }
}

impl<'a, 'tcx> EPCSBuilder<'a, 'tcx> {
    // Next three functions or so based on Prusti MIR liveness code
    fn apply_statement_effects(&mut self, location: mir::Location) {
        info!("[enter] apply_statement_effects {:?}", location);

        let statement = &self.mir[location.block].statements[location.statement_index];
        let pcs_in = self.tranform_pcs_before(location);

        info!("{:?} {:?}", location, statement);

        let pcs_out = match statement.kind.clone() {
            mir::StatementKind::Assign(assign_val) => {
                let (ref target, ref rhs) = *assign_val;
                self.visit_assign(pcs_in, target, rhs, location)
            }
            mir::StatementKind::AscribeUserType(_, _) => {
                unimplemented!("ascribe user types not implemented")
            }
            mir::StatementKind::SetDiscriminant { place, .. }
                if !pcs_in
                    .places
                    .iter()
                    .any(|p| Place::is_parent(&Place::from_mir(&*place), p)) =>
            {
                // Only here if the enum has no fields
                Epcs::add_place_mir(pcs_in, &*place)
            }
            _ => pcs_in,
        };

        info!("{}\n", pcs_out.clone());
        self.update_pcs_after_statement(location, pcs_out)
    }

    fn apply_terminator_effects(&mut self, bb: mir::BasicBlock) {
        info!("[enter] apply_terminator_effects bb={:?}", bb);
        let mir::BasicBlockData { ref terminator, .. } = self.mir[bb];

        // TODO(ws): clean up unpacking into one statement
        let mut pcs_in = self.get_pcs_before_terminator(bb);
        let packer = super::pack_unpack::PackUnpacker::new(self.tcx, self.mir);

        let out_pcs = if let Some(ref terminator) = *terminator {
            //info!("{:?}", terminator.kind.clone());
            pcs_in = match packer.pack_unpack_terminator(pcs_in, terminator) {
                Ok(pcs) => pcs,
                Err(err) => panic!("could not pack/unpack terminator: {}", err),
            };

            pcs_in = packer.wake_two_phase_borrows_terminator(pcs_in, terminator);
            self.result.before_terminator.insert(bb, pcs_in.clone());

            match terminator.kind.clone() {
                mir::TerminatorKind::Call {
                    ref func,
                    ref args,
                    ref destination,
                    ..
                } => self.visit_func_call(pcs_in, destination, func, args),
                mir::TerminatorKind::Drop { place, .. } => self.visit_drop(pcs_in, &place),
                mir::TerminatorKind::DropAndReplace { place, value, .. } => {
                    self.visit_drop_replace(pcs_in, &place, &value)
                }
                mir::TerminatorKind::SwitchInt { discr, .. } => self.visit_operand_no_target(
                    pcs_in,
                    &discr,
                    mir::Location {
                        block: bb,
                        statement_index: 0,
                    },
                ),
                mir::TerminatorKind::Yield { .. } => unimplemented!("async code not yet supported"),
                _ => pcs_in,
            }
        } else {
            pcs_in
        };

        //info!("{}", out_pcs);
        self.update_pcs_after_terminator(bb, out_pcs);
    }

    /// Merge sets of the incoming basic blocks. If the target
    /// set changed, add the first statement of the block to the
    /// work queue.
    fn apply_merge_effects(&mut self, bb: mir::BasicBlock) {
        info!("[enter] merge_effects bb={:?}", bb);
        let set = {
            let sets = &self.mir.predecessors()[bb];
            info!("    predecessors {:?}", sets);
            let sets = sets.iter();
            let sets =
                sets.filter_map(|predecessor| self.result.after_block.get(&predecessor).clone());
            //info!("{:?}", self.result.after_block);
            sets.cloned()
                .fold_first(|acc, set| {
                    info!("    merging {}", set);
                    Epcs::fp_merge(acc.clone(), set.clone())
                })
                .unwrap_or(Epcs::new())
        };
        let changed = {
            let old_set = self.result.before_block.get(&bb);
            if let Some(old_set) = old_set {
                info!(
                    "    merge_effects bb={:?} old_pcs={} merged_pcs={}",
                    bb, old_set, set
                );
                old_set != &set
            } else {
                true
            }
        };
        if changed {
            self.result.before_block.insert(bb, set.clone());
            let mir::BasicBlockData { ref statements, .. } = self.mir[bb];
            self.work_queue.push(WorkItem::ApplyTerminatorEffects(bb));
            for statement_index in 0..statements.len() {
                let location = mir::Location {
                    block: bb,
                    statement_index: statements.len() - statement_index - 1,
                };
                self.work_queue
                    .push(WorkItem::ApplyStatementEffects(location));
            }
        }
    }

    fn tranform_pcs_before(&mut self, location: mir::Location) -> Epcs {
        let pcs_out = self.get_pcs_before_statement(location);

        //let oracle = BorrowOracle::from_epcs(&pcs_out);
        //assert!(oracle.get_blocking_borrows(borrow_type, target))

        let packer = super::pack_unpack::PackUnpacker::new(self.tcx, self.mir);
        let pcs_in = match packer.pack_unpack_statement(pcs_out, location) {
            Ok(pcs) => pcs,
            Err(err) => panic!("could not pack/unpack statement: {}", err),
        };

        let pcs_in = packer.wake_two_phase_borrows(pcs_in, location);

        self.result
            .before_statement
            .insert(location, pcs_in.clone());

        pcs_in
    }

    fn get_pcs_before_statement(&self, mut location: mir::Location) -> Epcs {
        if location.statement_index == 0 {
            self.result.before_block[&location.block].clone()
        } else {
            location.statement_index -= 1;
            self.result.after_statement[&location].clone()
        }
    }

    /// Return the set before the terminator of the given basic block.
    fn get_pcs_before_terminator(&self, bb: mir::BasicBlock) -> Epcs {
        let mir::BasicBlockData { ref statements, .. } = self.mir[bb];
        if statements.len() == 0 {
            self.result.before_block[&bb].clone()
        } else {
            let location = mir::Location {
                block: bb,
                statement_index: statements.len() - 1,
            };
            self.result.after_statement[&location].clone()
        }
    }

    fn update_pcs_after_statement(&mut self, location: mir::Location, pcs: Epcs) {
        let old_pcs = self.result.after_statement.get(&location);

        if let Some(old_pcs) = old_pcs {
            if old_pcs != &pcs {
                let merged_pcs = Epcs::fp_merge(pcs, old_pcs.clone());
                self.result.after_statement.insert(location, merged_pcs);
            }
        } else {
            self.result.after_statement.insert(location, pcs);
        }
    }

    fn update_pcs_after_terminator(&mut self, bb: mir::BasicBlock, pcs: Epcs) {
        let mir::BasicBlockData { ref terminator, .. } = self.mir[bb];

        //let pcs_ref
        let old_pcs = self.result.after_block.get(&bb);
        if let Some(old_pcs) = old_pcs {
            if old_pcs != &pcs {
                let merged_pcs = Epcs::fp_merge(pcs.clone(), old_pcs.clone());
                self.result.after_block.insert(bb.clone(), merged_pcs);
            }
        } else {
            self.result.after_block.insert(bb.clone(), pcs.clone());
        }

        for successor in terminator.as_ref().unwrap().successors() {
            /*let old_pcs = self.result.before_block.get(successor);
            if let Some(old_pcs) = old_pcs {
                if old_pcs == &pcs {
                    // No need to merge, PCSes are the same
                    continue;
                }

                let merged_pcs = Epcs::merge(pcs.clone(), old_pcs.clone());
                self.result.before_block.insert(successor.clone(), merged_pcs);
            } else {
                self.result.before_block.insert(successor.clone(), pcs.clone());
            }*/

            self.work_queue.push(WorkItem::MergeEffects(*successor));
        }
    }
}

// The mir visitors that actually calculate the PCS.
// TODO(ws): Should this be put elsewhere?
impl<'a, 'tcx> EPCSBuilder<'a, 'tcx> {
    fn visit_assign(
        &self,
        pcs_in: Epcs,
        target: &mir::Place,
        rhs: &mir::Rvalue,
        location: mir::Location,
    ) -> Epcs {
        let pcs_mid = Epcs::add_place(pcs_in, Place::from_mir(target));

        // Expire borrows of target *after* calculating the RHS

        let pcs_mid = match rhs {
            mir::Rvalue::Use(operand) => self.visit_operand(pcs_mid, target, operand, location),

            // [0; N]
            mir::Rvalue::Repeat(_, _) => unimplemented!("repeat"),
            mir::Rvalue::Ref(_, kind, referred) => {
                self.visit_ref(pcs_mid, target, kind, referred, location)
            }
            mir::Rvalue::AddressOf(_, _) => unimplemented!("raw pointers are not yet supported"),
            mir::Rvalue::Cast(_, operand, _) => {
                self.visit_operand(pcs_mid, target, operand, location)
            }
            mir::Rvalue::BinaryOp(_, left_operand, right_operand)
            | mir::Rvalue::CheckedBinaryOp(_, left_operand, right_operand) => {
                let left_pcs = self.visit_operand_no_target(pcs_mid, left_operand, location);

                // TODO(ws): Not sure if this is correct, doesn't it mean after a binary op we don't add anything new to the PCS, just remove?
                // Should it be visit_operand?
                self.visit_operand_no_target(left_pcs, right_operand, location)
            }
            // box
            mir::Rvalue::NullaryOp(_, _) => unimplemented!("nullary ops not implemented"),
            mir::Rvalue::UnaryOp(_, operand) => {
                self.visit_operand_no_target(pcs_mid, operand, location)
            }
            mir::Rvalue::Aggregate(_, _) => {
                unimplemented!("aggregate doesn't exist in optimized mir?")
            }
            _ => pcs_mid,
        };

        let oracle = BorrowOracle::from_epcs(&pcs_mid);
        oracle
            .get_blocking_borrows(&Place::Concrete(
                Place::from_mir(target).base().clone(),
                Vec::new(),
            ))
            .iter()
            .fold(pcs_mid, |pcs, (source, _, _)| {
                Epcs::remove_borrow(Epcs::remove_place(pcs, source.clone()), source)
            })
    }

    fn visit_operand(
        &self,
        pcs_in: Epcs,
        target: &mir::Place,
        operand: &mir::Operand,
        location: mir::Location,
    ) -> Epcs {
        match operand {
            // TODO(ws): Make this and visit-no_target_operand sahre code
            mir::Operand::Move(moved_place) => {
                let pcs_mid = Epcs::move_to_mir(pcs_in, target, moved_place);
                // Expire due to liveness
                let pcs_mid = pcs_mid
                    .clone()
                    .refs
                    .iter()
                    .filter(|(k, _)| Place::is_parent(&Place::from_mir(moved_place), k))
                    .fold(pcs_mid, |acc, (next, _)| {
                        info!("liveness expire {}", next);
                        Epcs::remove_borrow(acc, next)
                    });

                // Expire y if we moved x and y -> x
                let oracle = BorrowOracle::from_epcs(&pcs_mid);
                RefersTo::resolve_dereferences(Place::from_mir(moved_place), &pcs_mid)
                    .places()
                    .iter()
                    .flat_map(|p| oracle.get_blocking_borrows(p).into_iter())
                    .filter(|(_, _, t)| {
                        pcs_mid
                            .places
                            .iter()
                            .find(|p| Place::is_parent(p, t)) // && &s != p)
                            .is_none()
                    }) // Don't kill borrows if they're split!
                    .fold(pcs_mid.clone(), |pcs, (source, b, t)| {
                        info!("expiring {} -{}-> {}", source, b, t);
                        Epcs::expire_borrow(pcs, &source)
                    })
            }
            mir::Operand::Copy(copied_place) => Epcs::copy_mir(pcs_in, target, copied_place),
            mir::Operand::Constant(constant) => {
                let promoted_id = match constant.literal.val {
                    ty::ConstKind::Unevaluated(_, _, Some(promoted)) => promoted.as_u32(),
                    // TODO: Handle &str, it has no promoted id but still needs handling somehow. Add a str placebase.
                    _ => u32::MAX,
                };
                match constant.literal.ty.kind {
                    ty::TyKind::Ref(_, _, mir::terminator::Mutability::Mut) => Epcs::add_borrow(
                        pcs_in,
                        Place::from_mir(target),
                        Borrow::Mutable(RefersTo::Definite(Place::BlackBox(
                            PlaceBase::PromotedConst(promoted_id),
                            Vec::new(),
                        ))),
                    ),
                    ty::TyKind::Ref(_, _, mir::terminator::Mutability::Not) => Epcs::add_borrow(
                        pcs_in,
                        Place::from_mir(target),
                        Borrow::Immutable(RefersTo::Definite(Place::BlackBox(
                            PlaceBase::PromotedConst(promoted_id),
                            Vec::new(),
                        ))),
                    ),
                    _ => pcs_in,
                }
            }
        }
    }

    // If we are moving as part of an operation (BinaryOp etc) we don't want to update the PCS just yet
    // TODO(ws): What about all that borrwing stufff? We need to add
    fn visit_operand_no_target(
        &self,
        pcs_in: Epcs,
        operand: &mir::Operand,
        location: mir::Location,
    ) -> Epcs {
        match operand {
            mir::Operand::Move(moved_place) => {
                // TODO(ws): add some expiry logic here.
                Epcs::move_out_mir(pcs_in, moved_place)
            }
            _ => pcs_in,
        }
    }

    fn visit_ref(
        &self,
        pcs_in: Epcs,
        target: &mir::Place,
        borrow_kind: &mir::BorrowKind,
        referred: &mir::Place,
        location: mir::Location,
    ) -> Epcs {
        assert!(
            target.projection.len() == 0,
            "left hand side of refs has no projections"
        );

        // TODO(ws): The oracle & expiring should be embedded into add borrow, to avoid having invalid intermediate PCSes
        let oracle = BorrowOracle::from_epcs(&pcs_in);

        let post_borrow_pcs = match borrow_kind {
            mir::BorrowKind::Shared => Epcs::add_shared_borrow_mir(pcs_in, target, referred),
            mir::BorrowKind::Mut {
                allow_two_phase_borrow: true,
            } => Epcs::add_borrow_new(
                pcs_in,
                Place::from_mir(target),
                BorrowType::SleepingMutable,
                Place::from_mir(referred),
            ),
            mir::BorrowKind::Mut {
                allow_two_phase_borrow: false,
            } => Epcs::add_mutable_borrow_mir(pcs_in, target, referred),
            _ => unimplemented!("unimplemented borrowkind at {:?}", location),
        };

        let borrow_type = BorrowType::from_mir(borrow_kind.clone());
        let blocking = RefersTo::resolve_dereferences(Place::from_mir(referred), &post_borrow_pcs)
            .places()
            .iter()
            .flat_map(|p| oracle.get_blocking_borrows(p).into_iter())
            .filter(|(_, bt, _)| {
                !(matches!(bt, BorrowType::Shared | BorrowType::SleepingMutable)
                    && matches!(borrow_type, BorrowType::Shared))
            })
            .collect::<im::HashSet<_>>();

        let post_expire_pcs = blocking
            .into_iter()
            .filter(|(s, _, _)| {
                info!(
                    "could expire {}: {}",
                    s,
                    s.clone() != Place::from_mir(target)
                );
                s.clone() != Place::from_mir(target) // Don't expire ourselves
            })
            .filter(|(_, _, t)| {
                Place::is_parent(&Place::from_mir(referred), t) // Split borrow protection
            })
            .filter(|(s, _, _)| {
                post_borrow_pcs
                    .places
                    .iter()
                    .find(|p| Place::is_parent(s, p) && &s != p)
                    .is_none()
            }) // Don't kill borrows if they're split!
            .fold(post_borrow_pcs.clone(), |pcs, (source, b, t)| {
                info!("expiring {} -{}-> {}", source, b, t);
                Epcs::expire_borrow(pcs, &source)
            });

        post_expire_pcs
    }

    fn visit_func_call(
        &self,
        pcs_in: Epcs,
        dest: &Option<(mir::Place, mir::BasicBlock)>,
        func: &mir::Operand,
        args: &Vec<mir::Operand>,
    ) -> Epcs {
        // 1. Get func sig
        // 2. See if we have lifetime constraints between args
        // 3. If we do apply them to the PCS
        // 4. If we don't add the place of the result to the PCS

        let mut pcs_out = pcs_in;

        if let Some((result_place, _)) = dest {
            pcs_out = Epcs::add_place_mir(pcs_out, result_place);
        }

        let (def_id, substs) = match func {
            mir::Operand::Constant(constant) => match **constant {
                mir::Constant {
                    literal:
                        ty::Const {
                            ty:
                                ty::TyS {
                                    kind: ty::TyKind::FnDef(def_id, substs),
                                    ..
                                },
                            val: _,
                        },
                    ..
                } => (def_id, substs),
                _ => unreachable!("function name is not constant!"),
            },
            _ => unreachable!("function name is not constant!"),
        };

        /*info!("Substs: {:?}", substs.clone());
        substs.regions().for_each(|r| info!("substs: {:?}", r));*/

        /*args.iter().for_each(|arg| match self.mir.local_decls[arg.place().unwrap().local_or_deref_local().unwrap()].ty.kind {
            ty::TyKind::Ref(_, ty::TyS{ kind: ty::TyKind::Adt(def, substs), ..}, _) => {
                def.variants.iter().for_each(|var| {
                    var.fields.iter().for_each(|field| {
                        if let ty::TyKind::Ref(region, _, _) = field.ty(self.tcx, substs).kind {
                            info!("Struct region: {:?}", region);
                        }
                    });
                });
                substs.regions().for_each(|r| info!("adt: {:?}", r))
            },
            _ => (),
        });*/

        let fn_sig = self.tcx.fn_sig(*def_id);

        let mut fra_builder = FRABuilder::new(fn_sig, self.tcx, self.mir);
        fra_builder.run();
        pcs_out = fra_builder.apply_to_pcs(
            args.iter()
                .map(|arg| Place::from_mir(&arg.place().unwrap()))
                .collect(),
            dest.map(|x| Place::from_mir(&x.0)),
            pcs_out,
        );
        //info!("{:?}", fn_sig);
        info!("PCS after FRA merge {}", pcs_out);

        pcs_out = args.iter().fold(pcs_out, |acc, operand| {
            self.visit_operand_no_target(
                acc,
                operand,
                mir::Location {
                    block: mir::BasicBlock::MAX,
                    statement_index: 0,
                },
            )
        });

        pcs_out
    }

    fn visit_drop(&self, pcs_in: Epcs, place: &mir::Place) -> Epcs {
        Epcs::move_out_mir(pcs_in, place)
    }

    fn visit_drop_replace(&self, pcs_in: Epcs, place: &mir::Place, value: &mir::Operand) -> Epcs {
        // TODO: Rework out this entire location idea, visiting operands in terminators is difficult
        unimplemented!("visit_drop_replace");
        //self.visit_operand(pcs_in, place, value, mir::Location{block: mir::BasicBlock::MAX{private: 0}, statement_index: 0})
    }
}

/*
/// Checks each live borrow and region against the borrow checker, expiring borrows and/or relaxing
/// regions as necessary
///
/// If a region is no longer live, it is "relaxed" and, if any sub-regions are still alive
/// according to the borrow checker, those sub regions are maintained in the RCS
fn expire_borrows(point: borrowck::Point, epcs: Epcs, bck: &mut BorrowCheckerFacts) -> Epcs {
    let mut new_epcs = epcs.clone();

    for (place, ref_to) in epcs.refs {
        match ref_to {
            RefersTo::Definite(loan, to_place) => {
                if !bck.borrow_live_at(loan.clone(), point) {
                    let (result_epcs, _) = Epcs::remove_ref(new_epcs.clone(), &place);
                    new_epcs = Epcs::add(result_epcs, to_place);
                }
            }
            RefersTo::Indefinite(regions) => {
                let (all_dead, remaining) = regions.iter().fold(
                    (true, BTreeSet::new()),
                    |(all_dead, mut remaining), region| {
                        if !bck.region_live_at(region, point) {
                            (all_dead, remaining)
                        } else {
                            remaining.insert(region.clone());
                            (false, remaining)
                        }
                    },
                );

                let vars_before_drop = borrowck::Region::all_vars_blocked(&regions);
                let vars_after_drop = borrowck::Region::all_vars_blocked(&remaining);
                let vars_to_restore = vars_before_drop.difference(&vars_after_drop);
                for var in vars_to_restore {
                    new_epcs = Epcs::add(
                        new_epcs,
                        Place::ConcretePlace(vec![PlaceElement::from_local(*var)]),
                    );
                }

                if all_dead {
                    let (result_epcs, _) = Epcs::remove_ref(new_epcs.clone(), &place);
                    new_epcs = result_epcs;
                } else {
                    new_epcs =
                        Epcs::add_ref(new_epcs.clone(), place, RefersTo::Indefinite(remaining));
                }
            }
        };
    }
    return new_epcs;
}
*/
/*#[cfg(test)]
mod tests {
    extern crate env_logger;
    // Note this useful idiom: importing names from outer (for mod tests) scope.
    use super::*;
    use borrow_checker_output::Loan;

    #[test]
    fn test_handle_op_move_out() {
        let mir_place = mir::Place {
            local: mir::Local::from_u32(4),
            projection: rustc_middle::ty::List::empty(),
        };

        let place = Place::from_mir(&mir_place);

        let mut epcs = Epcs::new();
        epcs = Epcs::add(epcs, place.clone());

        assert!(
            epcs.places.contains(&place),
            "Precondition for test failed!"
        );
        epcs = handle_op(Dest::Nowhere, &mir::Operand::Move(mir_place), epcs);
        assert!(
            !epcs.places.contains(&place),
            "Move should remove place from PCS"
        );
    }

    #[test]
    fn test_handle_op_move_out_ref() {
        let mir_place_a = mir::Place {
            local: mir::Local::from_u32(4),
            projection: rustc_middle::ty::List::empty(),
        };
        let mir_place_b = mir::Place {
            local: mir::Local::from_u32(5),
            projection: rustc_middle::ty::List::empty(),
        };

        let place_a = Place::from_mir(&mir_place_a);
        let place_b = Place::from_mir(&mir_place_b);

        let loan = Loan {
            uid: "test".to_owned(),
        };
        let refto = RefersTo::Definite(loan, place_b.clone());

        let mut epcs = Epcs::new();
        epcs = Epcs::add(epcs, place_a.clone());
        epcs = Epcs::add_ref(epcs, place_a.clone(), refto.clone());

        epcs = handle_op(
            Dest::Place(place_b.clone()),
            &mir::Operand::Move(mir_place_a),
            epcs,
        );
        assert!(
            epcs.refs.get(&place_b).contains(&(&refto)),
            "Move should remove place from PCS"
        );
    }

    #[test]
    fn test_handle_op_copy_out_ref() {
        let mir_place_a = mir::Place {
            local: mir::Local::from_u32(4),
            projection: rustc_middle::ty::List::empty(),
        };
        let mir_place_b = mir::Place {
            local: mir::Local::from_u32(5),
            projection: rustc_middle::ty::List::empty(),
        };

        let place_a = Place::from_mir(&mir_place_a);
        let place_b = Place::from_mir(&mir_place_b);

        let loan = Loan {
            uid: "test".to_owned(),
        };
        let refto = RefersTo::Definite(loan, place_b.clone());

        let mut epcs = Epcs::new();
        epcs = Epcs::add(epcs, place_a.clone());
        epcs = Epcs::add_ref(epcs, place_a.clone(), refto.clone());

        epcs = handle_op(
            Dest::Place(place_b.clone()),
            &mir::Operand::Copy(mir_place_a),
            epcs,
        );
        assert!(
            epcs.refs.get(&place_b).contains(&(&refto)),
            "Move should remove place from PCS"
        );
    }

    #[test]
    fn test_follow_no_deref() {
        let place_a = Place::ConcretePlace(vec![PlaceElement::Local(4)]);
        let place_b = Place::ConcretePlace(vec![PlaceElement::Local(5)]);

        let loan = Loan {
            uid: "test".to_owned(),
        };
        let refto = RefersTo::Definite(loan, place_b.clone());

        let mut epcs = Epcs::new();
        epcs = Epcs::add_ref(epcs, place_a.clone(), refto.clone());
        assert_eq!(follow(&place_a, &epcs), place_a);
    }

    #[test]
    fn test_follow_deref() {
        let place_a = Place::ConcretePlace(vec![PlaceElement::Local(4)]);
        let place_b = Place::ConcretePlace(vec![PlaceElement::Local(5)]);
        let place_a_deref = place_a.get_extended(PlaceElement::Deref());
        let loan = Loan {
            uid: "test".to_owned(),
        };
        let refto = RefersTo::Definite(loan, place_b.clone());

        let mut epcs = Epcs::new();
        epcs = Epcs::add_ref(epcs, place_a.clone(), refto.clone());
        assert_eq!(follow(&place_a_deref, &epcs), place_b);
    }

    #[test]
    fn test_follow_double_deref() {
        let place_a = Place::ConcretePlace(vec![PlaceElement::Local(4)]);
        let place_b = Place::ConcretePlace(vec![PlaceElement::Local(5)]);
        let place_c = Place::ConcretePlace(vec![PlaceElement::Local(6)]);

        let place_a_double_deref = place_a
            .get_extended(PlaceElement::Deref())
            .get_extended(PlaceElement::Deref());

        let loan = Loan {
            uid: "test".to_owned(),
        };
        let reftob = RefersTo::Definite(loan.clone(), place_b.clone());
        let reftoc = RefersTo::Definite(loan, place_c.clone());

        let mut epcs = Epcs::new();
        epcs = Epcs::add_ref(epcs, place_a.clone(), reftob.clone());
        epcs = Epcs::add_ref(epcs, place_b.clone(), reftoc.clone());
        assert_eq!(follow(&place_a_double_deref, &epcs), place_c);
    }

    #[test]
    fn test_handle_agg() {
        let mir_place_a = mir::Place {
            local: mir::Local::from_u32(4),
            projection: rustc_middle::ty::List::empty(),
        };
        let mir_place_b = mir::Place {
            local: mir::Local::from_u32(5),
            projection: rustc_middle::ty::List::empty(),
        };
        let mir_place_c = mir::Place {
            local: mir::Local::from_u32(6),
            projection: rustc_middle::ty::List::empty(),
        };

        let place_a = Place::from_mir(&mir_place_a);
        let place_b = Place::from_mir(&mir_place_b);
        let place_c = Place::from_mir(&mir_place_c);

        let loan = Loan {
            uid: "test".to_owned(),
        };
        let refto = RefersTo::Definite(loan, place_b.clone());

        let mut epcs = Epcs::new();
        epcs = Epcs::add(epcs, place_a.clone());
        epcs = Epcs::add_ref(epcs, place_a.clone(), refto.clone());
        epcs = Epcs::add_ref(epcs, place_c.clone(), refto.clone());

        let ops = vec![
            mir::Operand::Move(mir_place_a),
            mir::Operand::Move(mir_place_c),
        ];
        let pdest = place_b.clone();

        epcs = handle_aggregate(&AggregateKind::Tuple, &ops, epcs, pdest);
        debug!("{}", epcs);
        assert!(epcs
            .refs
            .get(&place_b.get_extended(PlaceElement::Index(1)))
            .contains(&(&refto)))
    }

    #[test]
    fn test_handle_terminator_propagates_places() {
        let place_a = Place::ConcretePlace(vec![PlaceElement::Local(4)]);
        let epcs = Epcs::add(Epcs::new(), place_a);
        let mut pw_epcs = PointwiseEPCS::new();
        pw_epcs.init_bbno_with(3, epcs);
        debug!("{}", pw_epcs);

        let mut bbds_to_visit = Vec::new();
        let bbno = mir::BasicBlock::from_u32(3);
        let terminator_kind = mir::TerminatorKind::Goto {
            target: mir::BasicBlock::from_u32(4),
        };

        handle_terminator(&mut pw_epcs, bbno, &terminator_kind, &mut bbds_to_visit);
        assert!(pw_epcs.get_last_known_epcs_in_bb(4).places.len() > 0);
        debug!("{}", pw_epcs);
    }

    #[test]
    fn test_handle_terminator_pushes_on_change() {
        let place_a = Place::ConcretePlace(vec![PlaceElement::Local(4)]);
        let epcs = Epcs::add(Epcs::new(), place_a);
        let mut pw_epcs = PointwiseEPCS::new();
        pw_epcs.init_bbno_with(3, epcs);
        debug!("{}", pw_epcs);

        let mut bbds_to_visit = Vec::new();
        let bbno = mir::BasicBlock::from_u32(3);
        let terminator_kind = mir::TerminatorKind::Goto {
            target: mir::BasicBlock::from_u32(4),
        };

        handle_terminator(&mut pw_epcs, bbno, &terminator_kind, &mut bbds_to_visit);
        assert!(bbds_to_visit.len() > 0);
        debug!("{}", pw_epcs);
    }
    #[test]
    fn test_handle_terminator_intersects_places() {
        let place_a = Place::ConcretePlace(vec![PlaceElement::Local(4)]);
        let epcs = Epcs::add(Epcs::new(), place_a);
        let mut pw_epcs = PointwiseEPCS::new();
        pw_epcs.init_bbno_with(3, epcs);
        pw_epcs.init_bbno_with(4, Epcs::new());
        debug!("{}", pw_epcs);

        let mut bbds_to_visit = Vec::new();
        let bbno = mir::BasicBlock::from_u32(3);
        let terminator_kind = mir::TerminatorKind::Goto {
            target: mir::BasicBlock::from_u32(4),
        };

        handle_terminator(&mut pw_epcs, bbno, &terminator_kind, &mut bbds_to_visit);
        assert!(pw_epcs.get_last_known_epcs_in_bb(4).places.len() == 0);
        debug!("{}", pw_epcs);
    }

    #[test]
    fn test_handle_terminator_union_refs() {
        let place_a = Place::ConcretePlace(vec![PlaceElement::Local(4)]);
        let loan = Loan {
            uid: "test".to_owned(),
        };
        let refto = RefersTo::Definite(loan, place_a.clone());

        let epcs = Epcs::add_ref(Epcs::new(), place_a, refto);
        let mut pw_epcs = PointwiseEPCS::new();
        pw_epcs.init_bbno_with(3, epcs);
        pw_epcs.init_bbno_with(4, Epcs::new());
        debug!("{}", pw_epcs);

        let mut bbds_to_visit = Vec::new();
        let bbno = mir::BasicBlock::from_u32(3);
        let terminator_kind = mir::TerminatorKind::Goto {
            target: mir::BasicBlock::from_u32(4),
        };

        /*handle_terminator(&mut pw_epcs, bbno, &terminator_kind, &mut bbds_to_visit);
        assert!(pw_epcs.get_last_known_epcs_in_bb(4).refs.len() == 1);
        debug!("{}", pw_epcs);*/
    }

    #[test]
    fn test_handle_terminator_fixed_point() {
        env_logger::init();

        let place_a = Place::ConcretePlace(vec![PlaceElement::Local(4)]);
        let loan = Loan {
            uid: "test".to_owned(),
        };
        let refto = RefersTo::Definite(loan, place_a.clone());

        let epcs = Epcs::add_ref(Epcs::new(), place_a, refto);
        let mut pw_epcs = PointwiseEPCS::new();
        pw_epcs.init_bbno_with(3, epcs.clone());
        pw_epcs.init_bbno_with(4, epcs);
        debug!("{}", pw_epcs);

        let mut bbds_to_visit = Vec::new();
        let bbno = mir::BasicBlock::from_u32(3);
        let terminator_kind = mir::TerminatorKind::Goto {
            target: mir::BasicBlock::from_u32(4),
        };

        assert!(bbds_to_visit.len() == 0, "Failed precondition");
        handle_terminator(&mut pw_epcs, bbno, &terminator_kind, &mut bbds_to_visit);
        assert!(bbds_to_visit.len() == 0);
        debug!("{}", pw_epcs);
    }
}*/
