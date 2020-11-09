// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::epcs::{BorrowOracle, Epcs, Permission, Place, PlaceBase, PlaceElement, RefersTo};
use super::pack_unpack::PackUnpacker;
use rustc_middle::mir;
use rustc_middle::ty;

pub fn pretty_print_epcs_rust<'tcx>(
    mir: &mir::Body<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
    epcs: &Epcs,
) -> String {
    let oracle = BorrowOracle::from_epcs(epcs);
    let places = epcs
        .places
        .iter()
        .filter(|p| place_is_rust(mir, p))
        .map(|p| {
            format!(
                "{}:{}",
                pretty_print_place(mir, tcx, p),
                if matches!(
                    oracle.get_resolved_permission(p, epcs),
                    Permission::ReadWrite
                ) {
                    "rw".to_string()
                } else {
                    "r".to_string()
                }
            )
        })
        .collect::<Vec<String>>()
        .join(", ");

    let refs = epcs
        .refs
        .iter()
        .filter(|(source, _)| place_is_rust(mir, source))
        .map(|(p, (borrow_type, ref_to))| {
            format!(
                "{} -{}-> {}",
                pretty_print_place(mir, tcx, p),
                borrow_type,
                pretty_print_refto(mir, tcx, ref_to)
            )
        })
        .collect::<Vec<String>>()
        .join(", ");
    format!("{{ {} }} ( {} ) ", places, refs)
}

fn place_is_rust(mir: &mir::Body, place: &Place) -> bool {
    match place.base() {
        PlaceBase::Local(local) => mir
            .local_decls
            .get(mir::Local::from_u32(local.clone()))
            .map_or(false, |decl| decl.is_user_variable()),
        _ => false,
    }
}

fn pretty_print_place<'tcx>(mir: &mir::Body<'tcx>, tcx: ty::TyCtxt<'tcx>, place: &Place) -> String {
    let base = if matches!(place, Place::Concrete(_, _)) {
        if let Some(symb) = mir
            .var_debug_info
            .iter()
            .find(|info| Place::from_mir(&info.place).base() == place.base())
        {
            format!("{}.", symb.name)
        } else {
            format!("{}.", place.base())
        }
    } else {
        return format!("{}", place);
    };

    let mut cur = Vec::new();

    let proj_str = place
        .projections()
        .iter()
        .map(|proj| {
            let packer = PackUnpacker::new(tcx, mir);
            let outp = match proj {
                PlaceElement::Field(idx) => {
                    // XXX: Hack, should separate func out
                    //let packer = PackUnpacker::new(tcx, mir);
                    match packer
                        .follow_place_to_ty(&Place::Concrete(place.base().clone(), cur.clone()))
                        .kind
                    {
                        ty::Adt(def, _) => {
                            assert!(
                                !def.is_enum(),
                                "enums must first be downcast to the correct variant"
                            );

                            format!(
                                "{}",
                                def.all_fields()
                                    .enumerate()
                                    .find(|(i, _)| i == idx)
                                    .unwrap()
                                    .1
                                    .ident
                                    .name
                                    .clone()
                            )
                        }
                        _ => unreachable!("place and type do not match"),
                    }
                }
                _ => format!("{}", proj),
            };
            cur.push(proj.clone());
            outp
        })
        .collect::<Vec<_>>()
        .join(".");

    format!("{}{}", base, proj_str)
        .trim_end_matches('.')
        .to_string()
}

fn pretty_print_refto<'tcx>(
    mir: &mir::Body<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
    refto: &RefersTo,
) -> String {
    match refto {
        RefersTo::Definite(p) => format!("{}", pretty_print_place(mir, tcx, p)),
        RefersTo::Indefinite(places) => format!(
            "{{{}}}",
            places
                .iter()
                .map(|p| format!("{}", pretty_print_place(mir, tcx, p)))
                .collect::<Vec<String>>()
                .join(", ")
        ),
    }
}
