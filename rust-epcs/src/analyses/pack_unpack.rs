// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Contains utility methods for pack and unpack operations of the PCS
//!
//! This module is far from complete, but contains some code that might be helpful for a full
//! implementation

// TODO: Rewrite, the actual implementation code is pretty shocking
use super::epcs::{BorrowOracle, BorrowType, Epcs, Place, PlaceBase, PlaceElement};

extern crate im;

use im::hashset::HashSet;
use log::trace;

use rustc_middle::mir;
use rustc_middle::ty;
use rustc_target::abi;

pub struct PackUnpacker<'a, 'tcx: 'a> {
    tcx: ty::TyCtxt<'tcx>,
    mir: &'a mir::Body<'tcx>,
}

impl<'a, 'tcx: 'a> PackUnpacker<'a, 'tcx> {
    pub fn new(tcx: ty::TyCtxt<'tcx>, mir: &'a mir::Body<'tcx>) -> Self {
        PackUnpacker { tcx, mir }
    }

    pub fn pack_unpack_terminator(
        &self,
        pcs_in: Epcs,
        terminator: &mir::terminator::Terminator,
    ) -> Result<Epcs, String> {
        self.terminator_places(terminator.kind.clone())
            .into_iter()
            .try_fold(pcs_in.clone(), |acc, place| {
                trace!("We need {}", place);
                self.transform_pcs_to_include_place(&acc, &place)
            })
    }

    pub fn pack_unpack_statement(
        &self,
        pcs_in: Epcs,
        location: mir::Location,
    ) -> Result<Epcs, String> {
        let statement = &self.mir[location.block].statements[location.statement_index];

        self.statement_places(statement, location)
            .into_iter()
            .try_fold(pcs_in.clone(), |acc, place| {
                //trace!("We need {}", place);
                self.transform_pcs_to_include_place(&acc, &place)
            })
    }

    pub fn wake_two_phase_borrows(&self, pcs_in: Epcs, location: mir::Location) -> Epcs {
        let statement = &self.mir[location.block].statements[location.statement_index];

        let mut pcs_mid = pcs_in;
        for place in self.statement_places(statement, location).iter() {
            pcs_mid.refs = match pcs_mid.refs.get(place) {
                // We're waking up a two phase borrow!
                // TODO(ws): enfornce the mutable rules... (i.e shared references should die)
                Some((BorrowType::SleepingMutable, ref_to)) => pcs_mid
                    .refs
                    .update(place.clone(), (BorrowType::Mutable, ref_to.clone())),
                _ => pcs_mid.refs,
            };
        }

        pcs_mid
    }

    pub fn wake_two_phase_borrows_terminator(
        &self,
        pcs_in: Epcs,
        terminator: &mir::terminator::Terminator,
    ) -> Epcs {
        let mut pcs_mid = pcs_in;
        for place in self.terminator_places(terminator.kind.clone()).iter() {
            pcs_mid.refs = match pcs_mid.refs.get(place) {
                // We're waking up a two phase borrow!
                // TODO(ws): enfornce the mutable rules... (i.e shared references should die)
                Some((BorrowType::SleepingMutable, ref_to)) => pcs_mid
                    .refs
                    .update(place.clone(), (BorrowType::Mutable, ref_to.clone())),
                _ => pcs_mid.refs,
            };
        }

        pcs_mid
    }

    fn statement_places(
        &self,
        statement: &mir::Statement,
        location: mir::Location,
    ) -> HashSet<Place> {
        //trace!("stmt: {:?}", statement);
        match statement.kind.clone() {
            mir::StatementKind::Assign(assign_val) => {
                let (ref target, ref rhs) = *assign_val;
                self.assign_places(target, rhs, location)
            }
            _ => HashSet::new(),
        }
    }

    fn assign_places(
        &self,
        _target: &mir::Place,
        rhs: &mir::Rvalue,
        location: mir::Location,
    ) -> HashSet<Place> {
        let places = HashSet::new(); // im::hashset![Place::from_mir(target)];

        places.union(match rhs {
            mir::Rvalue::Use(op) => self.operand_places(op),
            mir::Rvalue::Repeat(op, _) => self.operand_places(op),
            mir::Rvalue::Ref(_, mir::BorrowKind::Shared { .. }, place) => {
                im::hashset![Place::from_mir(place)]
            }
            mir::Rvalue::Ref(_, mir::BorrowKind::Shallow, place) => {
                im::hashset![Place::from_mir(place)]
            }
            mir::Rvalue::Ref(_, mir::BorrowKind::Unique, place) => {
                im::hashset![Place::from_mir(place)]
            }
            mir::Rvalue::Ref(_, mir::BorrowKind::Mut { .. }, place) => {
                im::hashset![Place::from_mir(place)]
            }
            mir::Rvalue::Len(place) => im::hashset![Place::from_mir(place)],
            mir::Rvalue::Cast(_, op, _) => self.operand_places(op),
            mir::Rvalue::BinaryOp(_, op_a, op_b) => {
                self.operand_places(op_a).union(self.operand_places(op_b))
            }
            mir::Rvalue::CheckedBinaryOp(_, op_a, op_b) => {
                self.operand_places(op_a).union(self.operand_places(op_b))
            }
            mir::Rvalue::UnaryOp(_, op) => self.operand_places(op),
            mir::Rvalue::Aggregate(_, _) => unimplemented!("aggregate not supported"),
            _ => HashSet::new(),
        })
    }

    fn operand_places(&self, operand: &mir::Operand) -> HashSet<Place> {
        match operand {
            mir::Operand::Move(moved_place) => im::hashset![Place::from_mir(moved_place)],
            mir::Operand::Copy(copied_place) => im::hashset![Place::from_mir(copied_place)],
            _ => HashSet::new(),
        }
    }

    fn terminator_places(&self, term: mir::TerminatorKind) -> HashSet<Place> {
        match term {
            mir::TerminatorKind::Call { ref args, .. } => args
                .into_iter()
                .flat_map(|op| self.operand_places(op).into_iter())
                .collect(),
            mir::TerminatorKind::Drop { ref place, .. } => im::hashset![Place::from_mir(place)],
            mir::TerminatorKind::DropAndReplace {
                ref place,
                ref value,
                ..
            } => im::hashset![Place::from_mir(place)].union(self.operand_places(value)),
            mir::TerminatorKind::SwitchInt { ref discr, .. } => self.operand_places(discr),
            mir::TerminatorKind::Yield { .. } => unimplemented!("async code not yet supported"),
            _ => HashSet::new(),
        }
    }

    pub fn transform_pcs_to_include_place(
        &self,
        pcs_in: &Epcs,
        target: &Place,
    ) -> Result<Epcs, String> {
        let places = pcs_in.places.clone();

        if places.contains(&target) {
            trace!("No need to unpack");
            return Ok(pcs_in.clone());
        }

        let place_to_unpack = places
            .iter()
            .filter(|p| Place::is_parent(p, target))
            .fold_first(|max, cur| {
                if cur.projections().len() > max.projections().len() {
                    cur
                } else {
                    max
                }
            });
        let places_to_pack: HashSet<&Place> = places
            .iter()
            .filter(|p| Place::is_parent(target, p))
            .collect();

        if let Some(from) = place_to_unpack {
            // Unpack
            let unpacked_places = self.unpack(from, target);
            Ok(Epcs {
                places: places.without(from).union(unpacked_places),
                refs: pcs_in.refs.clone(),
            })
        } else if !places_to_pack.is_empty() && self.pack(places_to_pack.clone(), target) {
            Ok(Epcs {
                places: places
                    .clone()
                    .symmetric_difference(places_to_pack.into_iter().cloned().collect())
                    .update(target.clone()),
                refs: pcs_in.refs.clone(),
            })
        } else {
            trace!("no places to pack or unpack: {} {}", pcs_in, target);

            // Try to expire a borrow or two
            // EXPIRE
            let oracle = BorrowOracle::from_epcs(&pcs_in);
            let blocking = oracle.get_blocking_borrows(target);
            if blocking.is_empty() {
                trace!("No borrows to expire while packing");
                return Err(
                    format!("Could not pack/unpack to include {} in {}", target, pcs_in)
                        .to_string(),
                );
            }

            trace!("expiring borrows to pack/unpack");
            let try_again_pcs = blocking
                .iter()
                .filter(|(_, borrow_type, _)| matches!(borrow_type, BorrowType::Mutable))
                .fold(pcs_in.clone(), |acc, (s, bt, t)| {
                    trace!("expiring {} -{}-> {}", s, bt, t);
                    Epcs::add_place(Epcs::expire_borrow(acc, s), t.clone())
                });
            self.transform_pcs_to_include_place(&try_again_pcs, target)
        }
    }

    // Unpack will always succeed (as long as the assertions hold that is)
    fn unpack(&self, from: &Place, to: &Place) -> HashSet<Place> {
        assert!(matches!(from, Place::Concrete(_, _)));
        assert!(matches!(to, Place::Concrete(_, _)));
        assert!(
            Place::is_parent(from, to),
            "when unpacking {} to {}, the former must be a parent of the latter",
            from,
            to
        );

        // We unpack the place above us.
        // If we unpacked outselves then we would unpack "to".
        if from == to {
            return HashSet::new();
        }

        let one_proj_up = to
            .projections()
            .into_iter()
            .take(to.projections().len() - 1)
            .map(|x| x.clone())
            .collect();
        let one_up_place = Place::Concrete(to.base().clone(), one_proj_up);

        let mut places = self.unpack(from, &one_up_place);
        places = places.without(&one_up_place);

        let parent_ty = self.follow_place_to_ty(&one_up_place);
        match parent_ty.kind {
            ty::Adt(def, substs) => {
                if def.is_enum() {
                    // TODO(ws): Enums do not support split borrows, we should attempt to reflect this somehow
                    if let PlaceElement::DowncastAndField(variant, _) =
                        to.projections().last().unwrap()
                    {
                        let fields = def
                            .variants
                            .get(abi::VariantIdx::from_usize(*variant))
                            .unwrap()
                            .fields
                            .iter();

                        places = fields.enumerate().fold(places, |acc, (index, _)| {
                            acc.update(Place::add_projection(
                                one_up_place.clone(),
                                PlaceElement::DowncastAndField(*variant, index),
                            ))
                        });
                        return places;
                    } else {
                        panic!("");
                    }
                }

                if def.is_box() {
                    return places
                        .update(Place::add_projection(one_up_place, PlaceElement::Deref()));
                }

                places = def
                    .all_fields()
                    .enumerate()
                    .fold(places, |acc, (index, _)| {
                        acc.update(Place::add_projection(
                            one_up_place.clone(),
                            PlaceElement::Field(index),
                        ))
                    });
                return places;
            }
            ty::Ref(_, inner_ty, mutable) => {
                assert!(
                    matches!(to.projections().last().unwrap(), PlaceElement::Deref()),
                    "if type is a ref we must be derefing it"
                );
                places = places.update(to.clone());
                return places;
            }
            ty::Tuple(_) => {
                parent_ty
                    .tuple_fields()
                    .enumerate()
                    .fold(places, |acc, (field_index, _)| {
                        acc.update(Place::add_projection(
                            one_up_place.clone(),
                            PlaceElement::Field(field_index),
                        ))
                    })
            }
            _ => unreachable!("unpack not implemented for non ADTs {:?}", parent_ty.kind),
        }
    }

    // Pack may not succeed if the from set does not have all of the required places
    fn pack(&self, from: HashSet<&Place>, to: &Place) -> bool {
        assert!(matches!(to, Place::Concrete(_, _)));
        assert!(from.iter().all(|p| matches!(p, Place::Concrete(_, _))));
        assert!(from.iter().all(|p| Place::is_parent(to, p)));

        if from.contains(to) {
            assert!(from.len() == 1);
            return true;
        }

        if from.is_empty() {
            return false;
        }

        let ty = self.follow_place_to_ty(to);

        match ty.kind {
            ty::Adt(def, substs) => {
                if def.is_enum() {
                    // Try all the variants
                    return def.variants.iter().enumerate().any(|(var_index, var_def)| {
                        var_def.fields.iter().enumerate().all(|(field_index, _)| {
                            let one_down = Place::add_projection(
                                to.clone(),
                                PlaceElement::DowncastAndField(var_index, field_index),
                            );
                            let new_from = from
                                .iter()
                                .filter(|p| {
                                    Place::longest_common_projection(&one_down, p).len()
                                        == one_down.projections().len()
                                })
                                .cloned()
                                .collect();
                            self.pack(new_from, &one_down)
                        })
                    });
                }

                if def.is_box() {
                    let one_down = Place::add_projection(to.clone(), PlaceElement::Deref());
                    return self.pack(from, &one_down);
                }

                let okay = def.all_fields().enumerate().all(|(field_index, _)| {
                    let one_down =
                        Place::add_projection(to.clone(), PlaceElement::Field(field_index));
                    let new_from = from
                        .iter()
                        .filter(|p| {
                            Place::longest_common_projection(&one_down, p).len()
                                == one_down.projections().len()
                        })
                        .cloned()
                        .collect();

                    self.pack(new_from, &one_down)
                });

                return okay;
            }
            ty::Ref(_, _, _) => {
                let one_down = Place::add_projection(to.clone(), PlaceElement::Deref());
                return self.pack(from, &one_down);
            }
            ty::Tuple(_) => {
                let okay = ty.tuple_fields().enumerate().all(|(field_index, _)| {
                    let one_down =
                        Place::add_projection(to.clone(), PlaceElement::Field(field_index));
                    let new_from = from
                        .iter()
                        .filter(|p| {
                            Place::longest_common_projection(&one_down, p).len()
                                == one_down.projections().len()
                        })
                        .cloned()
                        .collect();

                    self.pack(new_from, &one_down)
                });

                return okay;
            }

            _ => unimplemented!("pack: unsupported data type"),
        }
    }

    pub fn follow_place_to_ty(&self, place: &Place) -> &ty::TyS<'tcx> {
        //trace!("follow_place_to_ty {}", place);
        assert!(
            matches!(place.base(), PlaceBase::Local(_)),
            "base must be local"
        );
        let mir_local = if let PlaceBase::Local(local) = place.base() {
            mir::Local::from_u32(local.clone())
        } else {
            panic!("");
        };

        let mut cur_ty = self.mir.local_decls[mir_local].ty.clone();

        for proj in place.projections() {
            cur_ty = match proj {
                PlaceElement::Field(field) => match cur_ty.kind {
                    ty::Adt(def, substs) => {
                        assert!(
                            !def.is_enum(),
                            "enums must first be downcast to the correct variant"
                        );

                        def.all_fields()
                            .enumerate()
                            .find(|(i, _)| i.clone() == field)
                            .unwrap()
                            .1
                            .ty(self.tcx, substs)
                            .clone()
                    }
                    ty::Tuple(substs) => substs.type_at(field.clone()).clone(),
                    _ => panic!("we have reached a deadend with packing"),
                },
                PlaceElement::Index(index) => unimplemented!("slices in pack/unpack"),
                PlaceElement::Downcast(variant) => panic!("downcast"),
                PlaceElement::DowncastAndField(variant, field) => match cur_ty.kind {
                    ty::Adt(def, substs) => {
                        assert!(def.is_enum(), "must be an enum to downcast");
                        let fields = def
                            .variants
                            .get(abi::VariantIdx::from_usize(variant))
                            .unwrap()
                            .fields
                            .iter();
                        fields
                            .enumerate()
                            .find(|(i, _)| i.clone() == field)
                            .unwrap()
                            .1
                            .ty(self.tcx, substs)
                            .clone()
                    }
                    _ => unreachable!(""),
                },
                PlaceElement::Deref() => match cur_ty.kind {
                    ty::Ref(_, inner_ty, _) => inner_ty.clone(),
                    ty::Adt(def, substs) => {
                        assert!(def.is_box(), "must be a box");
                        assert!(substs.types().count() == 1);

                        substs.types().next().unwrap().clone()
                    }
                    _ => panic!("deref on a type that isn't a ref: {:?}", cur_ty),
                },
            }
        }

        cur_ty
    }
}
