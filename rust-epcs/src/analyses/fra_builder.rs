// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use log::trace;
use rustc_middle::mir;
use rustc_middle::ty;
use std::fmt;

//use std::collections::{HashMap, HashSet};
use super::epcs;
use im::{HashMap, HashSet};

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct FRAResult {
    map: HashMap<LHS, HashSet<RHS>>,
}

type FRA = (LHS, HashSet<RHS>);

impl FRAResult {
    fn new() -> Self {
        FRAResult {
            map: HashMap::new(),
        }
    }

    fn merge(left: FRAResult, right: FRAResult) -> Self {
        FRAResult {
            map: left
                .map
                .union_with(right.map, |l_set, r_set| l_set.union(r_set)),
        }
    }
}

fn apply_fra_to_pcs<'a, 'tcx: 'a>(
    fra: FRA,
    binder: ty::Binder<ty::FnSig<'tcx>>,
    arguments: Vec<epcs::Place>,
    output: Option<epcs::Place>,
    epcs: epcs::Epcs,
    tcx: ty::TyCtxt<'tcx>,
    mir: &'a mir::Body<'tcx>,
) -> epcs::Epcs {
    let (lhs, rhs) = fra;

    let rhs_places = rhs
        .iter()
        .map(|r| rhs_to_places(r.clone(), binder, arguments.clone(), epcs.clone(), tcx))
        .flatten()
        .fold_first(|acc, ref_to| epcs::RefersTo::chain(acc, ref_to))
        .unwrap();
    let (lhs_base_place, lhs_ty, lifetime) = match lhs.clone() {
        LHS::AfterRefs(Argument::In(arg_index), lifetime) => (
            arguments[arg_index as usize].clone(),
            binder.skip_binder().inputs()[arg_index as usize]
                .kind
                .clone(),
            lifetime,
        ),
        LHS::AfterRefs(Argument::Out, lifetime) => (
            output.unwrap(),
            binder.skip_binder().output().kind.clone(),
            lifetime,
        ),
    };

    let lhs_places = places_outlive_lifetime(lhs_ty, lifetime, lhs_base_place.clone(), tcx); //.iter().map(|p| p.projections().split_off(lhs_base_place.clone().projections().len()).into_iter().map(|x| x.clone()).collect()).collect();

    trace!("Appting FRA. LHS: {}, RHS: {:?}", lhs.clone(), rhs);
    //trace!("LHS places: {:?}, RHS places: {:?}", lhs_places, rhs_places);

    let (mut lhs_prefix, lhs_postfixes) = common_pe_prefix(lhs_places);

    lhs_prefix = match epcs::RefersTo::resolve_dereferences(lhs_prefix, &epcs.clone()) {
        epcs::RefersTo::Definite(place) => place,
        _ => panic!("func ref is indefinite"),
    };

    // Need to pack/unpack PCS
    let base_place = epcs::Place::Concrete(
        lhs_prefix.base().clone(),
        lhs_prefix.projections().into_iter().collect(),
    );

    // TODO(ws): We shouldn't always go to refs, only if it is needed (e.g it is not needed for fn<'a>(&'a i32, &'a i32) -> &'a i32 as out -> {arg_1, arg_2}).
    // It is impossible to get out of refs form
    let base_mir_local = if let epcs::PlaceBase::Local(local) = base_place.base() {
        mir::Local::from_u32(local.clone())
    } else {
        panic!("");
    };
    let base_ty = mir.local_decls[base_mir_local].ty.kind.clone();

    if lhs_postfixes.iter().all(|p| p.len() == 0) && place_includes_adt(base_ty) {
        return epcs::Epcs::add_borrow(epcs, base_place, epcs::Borrow::Immutable(rhs_places));
    }

    epcs::Epcs::add_refs_definite(
        epcs,
        epcs::Place::RefsDefinite(Box::new(base_place), lhs_postfixes),
        epcs::Borrow::Immutable(rhs_places),
    )
}

// FIXME: Terrible code, rewrite
fn common_pe_prefix(places: Vec<epcs::Place>) -> (epcs::Place, HashSet<Vec<epcs::PlaceElement>>) {
    let first_base = places[0].base();
    if places.iter().any(|place| place.base() != first_base) {
        panic!("kjhfk");
    }

    let place = places
        .clone()
        .into_iter()
        .fold_first(|acc, place| epcs::Place::longest_common_place(&acc, &place))
        .unwrap();
    let longest_prefix = place.projections().len();

    let projs = places
        .iter()
        .map(|p| {
            p.projections()
                .into_iter()
                .skip(longest_prefix)
                .collect::<Vec<_>>()
        })
        .collect::<HashSet<_>>();
    (place, projs)
}

fn rhs_to_places<'tcx>(
    rhs: RHS,
    binder: ty::Binder<ty::FnSig<'tcx>>,
    arguments: Vec<epcs::Place>,
    epcs: epcs::Epcs,
    tcx: ty::TyCtxt<'tcx>,
) -> Vec<epcs::RefersTo> {
    let fn_sig = binder.skip_binder();

    let (ty, place, lifetime) = match rhs {
        RHS::BeforeRefs(Argument::In(arg_id), lifetime) => (
            fn_sig.inputs()[arg_id as usize].kind.clone(),
            arguments[arg_id as usize].clone(),
            lifetime,
        ),
        RHS::BeforeRefs(Argument::Out, _) => {
            unreachable!("FRA RHS references an output, should only reference inputs!")
        }
        _ => unimplemented!("blackbox"),
    };

    places_outlive_lifetime(ty, lifetime, place, tcx)
        .iter()
        .map(|place| epcs::Place::add_projection(place.clone(), epcs::PlaceElement::Deref()))
        .map(|p| epcs::RefersTo::resolve_dereferences(p, &epcs))
        .collect()
}

// TODO(ws): Support enum variants
// Given a Type kind and a lifetime make a list of all places in the Type that outlive or have a lifetime equal to the given lifetime.
// Uses the given place as a base
fn places_outlive_lifetime<'tcx>(
    ty_kind: ty::TyKind<'tcx>,
    lifetime: Lifetime,
    base_place: epcs::Place,
    tcx: ty::TyCtxt<'tcx>,
) -> Vec<epcs::Place> {
    match ty_kind {
        ty::TyKind::Ref(region, _, _) if Lifetime::from_region(region.clone()) == lifetime => {
            vec![base_place]
        }
        ty::TyKind::Ref(_, target_ty, _) => places_outlive_lifetime(
            target_ty.kind.clone(),
            lifetime,
            epcs::Place::add_projection(base_place, epcs::PlaceElement::Deref()),
            tcx,
        ),
        ty::TyKind::Adt(adt_def, substs)
            if substs
                .regions()
                .find(|r| Lifetime::from_region(r.clone().clone()) == lifetime.clone())
                .is_some() =>
        {
            assert!(!adt_def.is_enum(), "enums not yet supported");
            adt_def
                .all_fields()
                .enumerate()
                .map(|(index, f)| {
                    places_outlive_lifetime(
                        f.ty(tcx, substs).kind.clone(),
                        lifetime.clone(),
                        epcs::Place::add_projection(
                            base_place.clone(),
                            epcs::PlaceElement::Field(index),
                        ),
                        tcx,
                    )
                })
                .flatten()
                .collect()
        }
        _ => vec![],
    }
}

fn place_to_borrow_type<'tcx>(lifetime: Lifetime, ty_kind: ty::TyKind<'tcx>) -> epcs::BorrowType {
    match ty_kind {
        ty::TyKind::Ref(_, _, mir::terminator::Mutability::Mut) => epcs::BorrowType::Mutable,
        ty::TyKind::Ref(_, _, mir::terminator::Mutability::Not) => epcs::BorrowType::Shared,
        ty::TyKind::Adt(adt_def, _) => epcs::BorrowType::Shared,
        _ => unreachable!(""),
    }
}

fn place_includes_adt<'tcx>(ty_kind: ty::TyKind<'tcx>) -> bool {
    match ty_kind {
        ty::TyKind::Ref(_, inner_ty, _) => place_includes_adt(inner_ty.kind.clone()),
        ty::TyKind::Adt(def, _) => !def.is_box(),
        _ => false,
    }
}

impl fmt::Display for FRAResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let out = self
            .map
            .iter()
            .map(|(lhs, rhs)| {
                format!(
                    "{} = {}",
                    lhs,
                    rhs.iter()
                        .map(|r| format!("{}", r))
                        .collect::<Vec<String>>()
                        .join(" U ")
                )
            })
            .collect::<Vec<String>>()
            .join("\n");

        write!(f, "{}", out)
    }
}

// TODO(ws): Named lifetimes should maybe have DefIDs in somehow...
#[derive(Debug, Clone, Hash, Eq, PartialEq)]
enum Lifetime {
    Named(String),
    Anon(u32),
}

impl Lifetime {
    fn from_bound_region(region: ty::BoundRegion) -> Self {
        match region {
            ty::BoundRegion::BrAnon(id) => Lifetime::Anon(id),
            ty::BoundRegion::BrNamed(_, symb) => Lifetime::Named(symb.to_ident_string()),
            _ => unreachable!("BrEnv not supported"),
        }
    }

    fn from_region(region: ty::RegionKind) -> Self {
        match region {
            ty::RegionKind::ReLateBound(_, bound) => Lifetime::from_bound_region(bound),
            ty::RegionKind::ReEarlyBound(ty::EarlyBoundRegion { name, .. }) => {
                Lifetime::Named(name.to_ident_string())
            }
            _ => panic!("from_region called on a region without a lifetime"),
        }
    }
}

impl fmt::Display for Lifetime {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Lifetime::Named(symb) => write!(f, "{}", symb),
            Lifetime::Anon(id) => write!(f, "'#{}", id),
        }
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
enum Argument {
    In(u32),
    Out,
}

impl fmt::Display for Argument {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Argument::In(id) => write!(f, "arg_{}", id),
            Argument::Out => write!(f, "output"),
        }
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
enum LHS {
    AfterRefs(Argument, Lifetime),
}

impl fmt::Display for LHS {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LHS::AfterRefs(arg, lifetime) => write!(f, "refs_after({}, {})", arg, lifetime),
        }
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
enum RHS {
    BeforeRefs(Argument, Lifetime),
    BlackBox(),
}

impl fmt::Display for RHS {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RHS::BeforeRefs(arg, lifetime) => write!(f, "refs_before({}, {})", arg, lifetime),
            RHS::BlackBox() => write!(f, "black_box_catch_all"),
        }
    }
}

trait FRARule<'tcx> {
    fn is_applicable(&self, sig: ty::Binder<ty::FnSig<'tcx>>) -> bool;
    fn constraints(&self, sig: ty::Binder<ty::FnSig<'tcx>>) -> FRAResult;
}

struct MutRefStructRule {}
impl<'tcx> FRARule<'tcx> for MutRefStructRule {
    fn is_applicable(&self, binder: ty::Binder<ty::FnSig<'tcx>>) -> bool {
        true
    }

    fn constraints(&self, binder: ty::Binder<ty::FnSig<'tcx>>) -> FRAResult {
        let fn_sig = binder.skip_binder();

        let mut map: HashMap<Lifetime, Vec<(usize, bool)>> = HashMap::new();

        for (index, input) in fn_sig.inputs().iter().enumerate() {
            match input.kind {
                ty::TyKind::Ref(
                    _,
                    ty::TyS {
                        kind: ty::TyKind::Adt(def, substs),
                        ..
                    },
                    mutability,
                ) => {
                    let is_mutable = mutability == mir::terminator::Mutability::Mut;

                    substs.regions().for_each(|r| {
                        let lifetime = Lifetime::from_region(r.clone());
                        map.entry(lifetime.clone())
                            .and_modify(|v| v.push((index, is_mutable)))
                            .or_insert(vec![(index, is_mutable)]);
                    });
                }
                _ => trace!("kind: {:?}", input.kind),
            }
        }

        let mut res = FRAResult::new();
        for (lifetime, args) in map {
            for (arg_id, is_mutable) in args.clone() {
                if is_mutable {
                    let rhs = args
                        .iter()
                        .map(|(ref a_id, _)| {
                            RHS::BeforeRefs(Argument::In(a_id.clone() as u32), lifetime.clone())
                        })
                        .collect();
                    res.map = res.map.update(
                        LHS::AfterRefs(Argument::In(arg_id as u32), lifetime.clone()),
                        rhs,
                    );
                }
            }
        }

        //trace!("mut ref fra: {}", res);
        res
    }
}

struct OutRefRule {}
impl<'tcx> FRARule<'tcx> for OutRefRule {
    fn is_applicable(&self, binder: ty::Binder<ty::FnSig<'tcx>>) -> bool {
        true
    }

    //fn constraints(&self, fn_sig: ty::FnSig<'tcx>) -> FRAResult {
    fn constraints(&self, binder: ty::Binder<ty::FnSig<'tcx>>) -> FRAResult {
        let fn_sig = binder.skip_binder();
        let output = fn_sig.output();

        let output_region = match output.kind {
            ty::TyKind::Ref(region, _, _) => region,
            _ => return FRAResult::new(),
        };

        let mut rhs = HashSet::new();
        for (index, input) in fn_sig.inputs().iter().enumerate() {
            match input.kind {
                ty::TyKind::Ref(region, _, _) if region == output_region => {
                    rhs.insert(RHS::BeforeRefs(
                        Argument::In(index as u32),
                        Lifetime::from_region(region.clone()),
                    ));
                }
                _ => (),
            }
        }

        let mut res = FRAResult::new();

        if rhs.len() > 0 {
            res.map.insert(
                LHS::AfterRefs(Argument::Out, Lifetime::from_region(output_region.clone())),
                rhs,
            );
        }

        //trace!("out ref fra: {}", res);

        res
    }
}

pub struct FRABuilder<'a, 'tcx: 'a> {
    fn_sig: ty::Binder<ty::FnSig<'tcx>>,
    tcx: ty::TyCtxt<'tcx>,
    mir: &'a mir::Body<'tcx>,

    // TODO(ws): replace with slice
    rules: Vec<Box<dyn FRARule<'tcx>>>,
    pub result: FRAResult,
}

impl<'a, 'tcx> FRABuilder<'a, 'tcx> {
    pub fn new(
        fn_sig: ty::Binder<ty::FnSig<'tcx>>,
        tcx: ty::TyCtxt<'tcx>,
        mir: &'a mir::Body<'tcx>,
    ) -> Self {
        FRABuilder {
            fn_sig,
            tcx,
            mir,

            rules: vec![Box::new(OutRefRule {}), Box::new(MutRefStructRule {})],
            result: FRAResult::new(),
        }
    }

    pub fn run(&mut self) {
        for rule in self.rules.iter() {
            let rule_result = (*rule).constraints(self.fn_sig);
            self.result = FRAResult::merge(self.result.clone(), rule_result);
        }
    }

    pub fn apply_to_pcs(
        &self,
        arguments: Vec<epcs::Place>,
        output: Option<epcs::Place>,
        epcs: epcs::Epcs,
    ) -> epcs::Epcs {
        let mut pcs = epcs;
        for fra in self.result.map.clone() {
            pcs = apply_fra_to_pcs(
                fra,
                self.fn_sig,
                arguments.clone(),
                output.clone(),
                pcs.clone(),
                self.tcx,
                self.mir,
            );
        }

        pcs
    }
}
