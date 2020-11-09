// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! The data structures representing the EPCS at each program point
extern crate im;

use im::hashmap::HashMap;
use im::hashset::HashSet;
use log::info;
use rustc_middle::mir;
use std::fmt;

/// The EPCS at a given point
///
/// The Extended Place Capabilities Summary is a combination of the PCS (Place Capabilities
/// Summary) and the RCS (Reference Capabilities Summary). The PCS tracks the capabilities each
/// place has to access the memory location it corresponds to. The RCS tracks which
/// borrows/references are alive, and what they refer to.
///
/// # Cloning
/// The EPCS is primarily implemented with immutable data structures from the im crate. This was a
/// design choice made to allow for quick cloning of EPCS to compute a transform for the next
/// statement.
#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct Epcs {
    /// The PCS
    pub places: HashSet<Place>,

    /// The RCS
    pub refs: HashMap<Place, (BorrowType, RefersTo)>,
}

// PCS
impl Epcs {
    /// Creates a new EPCS at Start(bb0\[0\])
    pub fn new() -> Epcs {
        Epcs {
            places: HashSet::new(),
            refs: HashMap::new(),
        }
    }

    /// Add a place to the PCS
    pub fn add_place(epcs: Epcs, place: Place) -> Epcs {
        //assert!(!epcs.places.contains(&place), "place to add to PCS is not already in PCS: {}", place);
        Epcs {
            places: epcs.places.update(place),
            refs: epcs.refs,
        }
    }

    pub fn add_place_mir(epcs: Epcs, place: &mir::Place) -> Epcs {
        Epcs::add_place(epcs, Place::from_mir(place))
    }

    pub fn remove_place(epcs: Epcs, place: Place) -> Epcs {
        assert!(
            epcs.places.contains(&place),
            "epcs remove place: {} not in pcs",
            place
        );
        Epcs {
            places: epcs.places.without(&place),
            refs: epcs.refs,
        }
    }

    pub fn remove_place_mir(epcs: Epcs, place: &mir::Place) -> Epcs {
        Epcs::remove_place(epcs, Place::from_mir(place))
    }

    pub fn has_place(epcs: Epcs, place: &Place) -> bool {
        match place {
            Place::Concrete(_, _) => epcs.places.contains(place),
            Place::RefsDefinite(root_place, projs) => projs
                .into_iter()
                .map(|proj| {
                    proj.into_iter().fold(*(root_place.clone()), |p, pro| {
                        Place::add_projection(p, pro.clone())
                    })
                })
                .all(|p| epcs.places.contains(&p)),
            Place::BlackBox(_, _) | Place::Reachable(_) | Place::WildcardArg => {
                panic!("{} should not be in pcs places", place)
            }
        }
    }
}

// Borrows part
impl Epcs {
    // Get what place points to in the EPCS
    pub fn get_borrow<'a>(epcs: &'a Epcs, place: &Place) -> Option<(BorrowType, RefersTo)> {
        //info!("get_borrow: {:?} {:?}", epcs, place);

        if let Some(ref_to) = Epcs::find_place_in_ref_definite(epcs, place) {
            return Some(ref_to.clone());
        }

        match place {
            Place::Concrete(_, _) => epcs.refs.get(place).map(|r| r.clone()),
            _ => panic!("lhs of a borrow should only be concrete not {}", place),
        }
    }

    // TODO(ws): This has been replaced nearly everywhere by add_borrow_new, examine which of the two to keep or rename
    pub fn add_borrow(epcs: Epcs, place: Place, what: Borrow) -> Epcs {
        assert!(
            Epcs::has_place(epcs.clone(), &place) || matches!(place, Place::RefsDefinite(_, _)),
            "epcs add borrow: {} not in pcs",
            &place
        );
        assert!(
            what.refers_to()
                .places()
                .iter()
                .filter(|p| matches!(p, Place::Concrete(_, _)))
                .all(|p| epcs.places.contains(p)),
            "epcs add borrow: target not in pcs"
        );

        Epcs {
            places: match what {
                Borrow::Mutable(ref ref_to) => {
                    // TODO(ws): refactor
                    ref_to
                        .places()
                        .iter()
                        .fold(epcs.places.clone(), |pcs, place| pcs.without(place))
                }
                Borrow::Immutable(_) => epcs.places,
            },

            // TODO(ws): Put mutable or immutable in the PCS
            refs: epcs.refs.update(
                place,
                match what {
                    Borrow::Mutable(ref r) => (BorrowType::Mutable, r.clone()),
                    Borrow::Immutable(ref r) => (BorrowType::Shared, r.clone()),
                },
            ),
        }
    }

    pub fn add_borrow_new(
        epcs: Epcs,
        source: Place,
        borrow_type: BorrowType,
        target: Place,
    ) -> Epcs {
        info!(
            "add_borrow {} -{}-> {} to pcs: {}",
            source, borrow_type, target, epcs
        );
        assert!(
            epcs.places.contains(&source),
            "epcs add borrow: {} not in pcs",
            &source
        );
        assert!(
            matches!(target, Place::WildcardArg | Place::BlackBox(_, _))
                || epcs.places.contains(&target),
            "epcs add borrow: target not in pcs"
        );

        let ref_to = RefersTo::resolve_dereferences(target.clone(), &epcs);
        let blocked_places: HashSet<Place> = ref_to
            .places()
            .iter()
            .map(|p| match p {
                Place::Reachable(base) => *base.clone(),
                Place::RefsDefinite(_, _) => panic!("refs not allowed on rhs!"),
                _ => p.clone().clone(),
            })
            .filter(|p| !matches!(p, Place::BlackBox(_, _)))
            .collect();

        /*assert!(
            blocked_places.iter().all(|p| epcs.places.contains(p)),
            "{:?} {:?}", blocked_places,
            blocked_places
                .iter()
                .filter(|p| !epcs.places.contains(p))
                .collect::<Vec<_>>()
        );*/

        Epcs {
            places: match borrow_type {
                BorrowType::Mutable => {
                    // TODO(ws): refactor

                    blocked_places
                        .iter()
                        .fold(epcs.places.without(&target), |pcs, place| {
                            pcs.without(&place)
                        })
                        .without(&target)
                }
                BorrowType::SleepingMutable | BorrowType::Shared => epcs.places,
            },
            refs: epcs.refs.update(source, (borrow_type, ref_to.clone())),
        }
    }

    pub fn add_shared_borrow_mir(epcs: Epcs, source: &mir::Place, target: &mir::Place) -> Epcs {
        Epcs::add_borrow_new(
            epcs,
            Place::from_mir(source),
            BorrowType::Shared,
            Place::from_mir(target),
        )
    }

    // 1. Remove what we're referring to from the PCS
    // 2. Add the reference, ideally we should mark it as mutable? (I think we need this info somewhere)
    pub fn add_mutable_borrow_mir(
        epcs: Epcs,
        place: &mir::Place,
        referenced_place: &mir::Place,
    ) -> Epcs {
        Epcs::add_borrow_new(
            epcs,
            Place::from_mir(place),
            BorrowType::Mutable,
            Place::from_mir(referenced_place),
        )
    }

    pub fn remove_borrow(epcs: Epcs, place: &Place) -> Epcs {
        assert!(
            epcs.refs.contains_key(place),
            "epcs remove borrow: borrow {} must be in pcs",
            place
        );
        Epcs {
            places: epcs.places,
            refs: epcs.refs.without(place),
        }
    }

    pub fn expire_borrow(epcs: Epcs, source: &Place) -> Epcs {
        assert!(epcs.refs.contains_key(source));

        Epcs {
            places: epcs
                .places
                .iter()
                .filter(|p| !Place::is_parent(source, p))
                .cloned()
                .collect::<HashSet<Place>>()
                .without(source),
            refs: epcs.refs.without(source),
        }
    }

    pub fn remove_borrow_mir(epcs: Epcs, place: &mir::Place) -> Epcs {
        Epcs::remove_borrow(epcs, &Place::from_mir(place))
    }

    // TODO(ws): I don't like having this seperate function & it's also written terribly
    pub fn add_refs_definite(epcs: Epcs, place: Place, what: Borrow) -> Epcs {
        assert!(
            matches!(place, Place::RefsDefinite(_, _)),
            "place is refs definite"
        );

        let mut pcs_out = epcs;
        if let Place::RefsDefinite(base_place, projs) = place.clone() {
            if projs.iter().all(|proj| proj.is_empty()) {
                return Epcs::add_borrow(pcs_out, *base_place, what);
            }

            for proj in projs {
                let mut final_proj = Vec::new();
                final_proj.append(&mut base_place.projections().clone());
                final_proj.append(&mut proj.clone());

                // Don't call remove_borrow, because we don't mind if the borrow doesn't exist, the borrow doesn't exist for the result of a fn call just the args.
                // TODO(ws): Should we expire borrws here?
                pcs_out = Epcs {
                    places: pcs_out.places.clone(),
                    refs: pcs_out
                        .refs
                        .without(&Place::Concrete(base_place.base().clone(), final_proj)),
                };
            }
        }

        Epcs::add_borrow(pcs_out, place, what)
    }

    // TODO(ws): Change this function name
    fn find_place_in_ref_definite<'a>(
        epcs: &'a Epcs,
        place: &'a Place,
    ) -> Option<&'a (BorrowType, RefersTo)> {
        epcs.refs
            .iter()
            .find(|(k, _)| match k {
                Place::RefsDefinite(base_place, fields) if place.base() == base_place.base() => {
                    for field in fields {
                        if place.projections()
                            == base_place
                                .projections()
                                .iter()
                                .chain(field.into_iter())
                                .map(|pe| pe.clone())
                                .collect::<Vec<PlaceElement>>()
                        {
                            return true;
                        }
                    }
                    return false;
                }
                _ => false,
            })
            .map(|(_, r)| r)
    }

    // TODO: doesn't support refs
    fn is_borrow(epcs: &Epcs, place: &Place) -> bool {
        epcs.refs.iter().find(|(p, _)| p == place).is_some()
    }
}

// Moving PCS
impl Epcs {
    fn move_to(epcs: Epcs, to: Place, from: Place) -> Epcs {
        assert!(
            epcs.places.contains(&from),
            "epcs move: from place must be in pcs"
        );

        Epcs {
            places: epcs
                .places
                .without(&from)
                .into_iter()
                .filter(|p| !Place::is_parent(&to, p))
                .collect::<HashSet<_>>()
                .update(to.clone()),
            refs: match epcs.refs.get(&from) {
                Some(v) => epcs.refs.update(to.clone(), v.clone()),
                _ => epcs.refs,
            },
        }
    }

    pub fn move_to_mir(epcs: Epcs, to: &mir::Place, from: &mir::Place) -> Epcs {
        Epcs::move_to(epcs, Place::from_mir(to), Place::from_mir(from))
    }

    pub fn move_out_mir(mut epcs: Epcs, place: &mir::Place) -> Epcs {
        if Epcs::is_borrow(&epcs, &Place::from_mir(place)) {
            // TODO(ws): Refactor and is this correct in cases such as x -> reachable(root) to put root
            // back in the allowed places?
            let place = Place::from_mir(place);
            if let Some((BorrowType::Mutable, ref_to)) = epcs.refs.get(&place) {
                for ref_place in ref_to
                    .places()
                    .iter()
                    .filter_map(|ref_place| match ref_place {
                        Place::Concrete(_, _) => Some(ref_place),
                        Place::Reachable(inner) => Some(inner.as_ref()),
                        _ => None,
                    })
                {
                    epcs = Epcs::add_place(epcs, ref_place.clone());
                }
            }

            epcs = Epcs::remove_borrow(epcs, &place);
        }
        Epcs::remove_place_mir(epcs, place)
    }

    pub fn copy_mir(epcs: Epcs, to: &mir::Place, from: &mir::Place) -> Epcs {
        assert!(
            epcs.places.contains(&Place::from_mir(from)),
            "epcs copy: from place must be in pcs"
        );

        Epcs {
            places: epcs.places.update(Place::from_mir(to)),
            refs: match Epcs::get_borrow(&epcs, &Place::from_mir(from)) {
                Some(ref_to) => epcs.refs.update(Place::from_mir(to), ref_to.clone()),
                _ => epcs.refs,
            },
        }
    }
}

// Merging EPCS
impl Epcs {
    pub fn fp_merge(left: Epcs, right: Epcs) -> Epcs {
        // TODO(ws): Organise these rules into a nice table that can be searched through

        info!("Merging\n    {}\nand\n    {}", left.clone(), right.clone());

        let mut merged_places = HashSet::new();
        for lp in left.places.iter() {
            if right.places.contains(lp) {
                merged_places.insert(lp.clone());
                continue;
            }
            for rp in right.places.iter() {
                if Place::is_parent(lp, rp) {
                    merged_places.insert(rp.clone());
                    continue;
                }
                if Place::is_parent(rp, lp) {
                    merged_places.insert(lp.clone());
                    break;
                }
            }
        }

        let res = Epcs {
            places: merged_places,
            refs: left
                .refs
                .intersection_with(right.refs, |(l_borrow, l), (r_borrow, r)| {
                    assert_eq!(
                        l_borrow, r_borrow,
                        "when merging borrows the type of borrow must be the same, {}, {}",
                        l, r
                    );
                    (
                        l_borrow,
                        // TODO(ws): Replace with just merging l.places(), r.places()
                        match (l, r) {
                            (RefersTo::Definite(left_place), RefersTo::Definite(right_place))
                                if Place::shares_base(&left_place, &right_place) =>
                            {
                                RefersTo::Definite(Place::fp_merge(&left_place, &right_place))
                            }
                            (RefersTo::Definite(left_place), RefersTo::Definite(right_place)) => {
                                RefersTo::Indefinite(im::hashset![left_place, right_place])
                            }
                            (
                                RefersTo::Definite(left_place),
                                RefersTo::Indefinite(right_places),
                            )
                            | (
                                RefersTo::Indefinite(right_places),
                                RefersTo::Definite(left_place),
                            ) => {
                                assert!(
                                    right_places
                                        .iter()
                                        .filter(|p| Place::shares_base(&left_place, p))
                                        .count()
                                        <= 1,
                                    "?: only merge once {:?}",
                                    right_places
                                        .iter()
                                        .filter(|p| Place::shares_base(&left_place, p))
                                        .collect::<Vec<&Place>>()
                                );

                                RefersTo::Indefinite(
                                    if right_places
                                        .iter()
                                        .any(|p| Place::shares_base(&left_place, p))
                                    {
                                        // We have to approximate
                                        right_places
                                            .iter()
                                            .map(|p| {
                                                if Place::shares_base(&left_place, p) {
                                                    Place::fp_merge(&left_place, p)
                                                } else {
                                                    p.clone()
                                                }
                                            })
                                            .collect()
                                    } else {
                                        // Add left to right_places
                                        right_places.update(left_place)
                                    },
                                )
                            }
                            (
                                RefersTo::Indefinite(left_places),
                                RefersTo::Indefinite(right_places),
                            ) => {
                                let mut output = HashSet::new();
                                let mut r = right_places;

                                for lp in left_places {
                                    assert!(
                                        r.clone()
                                            .iter()
                                            .filter(|p| Place::shares_base(&lp, p))
                                            .count()
                                            <= 1,
                                        "?: only merge once {:?}"
                                    );
                                    if let Some(rp) =
                                        r.iter().find(|p| Place::shares_base(&lp, p.clone()))
                                    {
                                        output = output.update(Place::fp_merge(&lp, rp));
                                        r = r.without(rp);
                                    }
                                    output = output.update(lp);
                                }

                                for rp in r {
                                    output = output.update(rp);
                                }

                                RefersTo::Indefinite(output)
                                //left_places.union(right_places)
                                //unimplemented!("indefinite + indefinite merging")
                            }
                        },
                    )
                }),
        };

        info!("into\n    {}", res);
        res
    }
}

// Sanity
impl Epcs {
    fn sane(epcs: &Epcs) {
        assert!(epcs
            .places
            .iter()
            .all(|p| matches!(p, Place::Concrete(PlaceBase::Local(_), _))));
    }
}

impl fmt::Display for Epcs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let oracle = BorrowOracle::from_epcs(self);
        let places = self
            .places
            .iter()
            .map(|p| {
                format!(
                    "{}:{}",
                    p,
                    if matches!(
                        oracle.get_resolved_permission(p, self),
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

        let refs = self
            .refs
            .iter()
            .map(|(p, (borrow_type, ref_to))| format!("{} -{}-> {}", p, borrow_type, ref_to))
            .collect::<Vec<String>>()
            .join(", ");
        write!(f, "{{ {} }} ( {} ) ", places, refs)
    }
}

pub struct BorrowOracle {
    //borrows: HashMap<Permission, Place>,
    borrows: HashMap<PlaceBase, HashSet<(Place, BorrowType, Place)>>,
    pcs: Epcs,
}

impl BorrowOracle {
    pub fn from_epcs(epcs: &Epcs) -> Self {
        let mut permsr = BorrowOracle {
            borrows: HashMap::new(),
            pcs: epcs.clone(),
        };

        for (source, (borrow_type, ref_to)) in epcs.refs.iter() {
            match ref_to {
                RefersTo::Definite(target) => {
                    permsr.add_borrow(source, borrow_type.clone(), &target)
                }
                RefersTo::Indefinite(targets) => targets
                    .iter()
                    .for_each(|target| permsr.add_borrow(source, borrow_type.clone(), target)),
            }
        }

        // FIXME: Doesn't support split borrows
        //permsr.assert_no_mutable_shared_conflicts();

        permsr
    }

    fn get_permission(
        &self,
        place: &Place,
        epcs: &Epcs,
    ) -> (Permission, Option<HashSet<(Place, BorrowType, Place)>>) {
        if let Some((BorrowType::Shared, target)) = epcs.refs.get(place) {
            // TODO: Actually return the borrow here
            return (Permission::Read, None);
        }

        let base_borrows = self.borrows.get(place.base());
        let base_borrows = if let Some(b) = base_borrows {
            b
        } else {
            return (Permission::ReadWrite, None);
        };

        let borrows: HashSet<(Place, BorrowType, Place)> = base_borrows
            .into_iter()
            .filter(|(source, _, target)| {
                Place::is_parent(place, target)
                    || Place::is_parent(target, place) && epcs.places.contains(source)
            })
            .cloned()
            .collect();

        let have_shared = borrows
            .iter()
            .any(|(_, borrow_type, _)| matches!(borrow_type, BorrowType::Shared));
        if have_shared {
            (Permission::Read, Some(borrows))
        } else {
            (Permission::ReadWrite, Some(borrows))
        }
    }

    pub fn get_resolved_permission(&self, place: &Place, epcs: &Epcs) -> Permission {
        let rw = RefersTo::resolve_dereferences(place.clone(), epcs)
            .places()
            .iter()
            .map(|p| self.get_permission(p, epcs))
            .map(|(perm, _)| perm)
            .all(|perm| matches!(perm, Permission::ReadWrite));

        if rw {
            Permission::ReadWrite
        } else {
            Permission::Read
        }
    }

    // TODO(ws):
    pub fn get_blocking_borrows(&self, target: &Place) -> HashSet<(Place, BorrowType, Place)> {
        self.borrows
            .get(target.base())
            .cloned()
            .unwrap_or(HashSet::new())
            .into_iter()
            .filter(|(_, _, t)| Place::is_parent(target, t) || Place::is_parent(t, target))
            .filter(|(source, _, _)| {
                self.pcs
                    .places
                    .iter()
                    .find(|place| {
                        Place::is_parent(source, place) || Place::is_parent(place, source)
                    })
                    .is_some()
            })
            .collect()
    }

    // TODO(ws): Wrongly panics when split borrowing
    fn assert_no_mutable_shared_conflicts(&self) {
        for (_, borrow_set) in self.borrows.iter() {
            for (source, borrow_type, target) in borrow_set.iter() {
                for (source_1, borrow_type_1, target_1) in borrow_set.iter() {
                    if target != target_1
                        && (Place::is_parent(target, target_1)
                            || Place::is_parent(target_1, target))
                    {
                        // TODO(ws): Make this support split borrows, if the source isn't in pcs but a child is (note if they're both reachable then one should count as a child of the other) then it's a split borrow
                        assert!(
                            matches!(borrow_type, BorrowType::Shared)
                                && matches!(borrow_type_1, BorrowType::Shared),
                            "{} -{}-> {} and {} -{}-> {} conflict!",
                            source,
                            borrow_type,
                            target,
                            source_1,
                            borrow_type_1,
                            target_1
                        );
                    }
                }
            }
        }
    }

    fn add_borrow(&mut self, source: &Place, borrow_type: BorrowType, target: &Place) {
        match source {
            Place::Concrete(_, _) => (),
            Place::RefsDefinite(base, projss) => {
                projss.iter().for_each(|projs| {
                    let place = projs.iter().fold(*(base.clone()), |acc, proj| {
                        Place::add_projection(acc.clone(), proj.clone())
                    });
                    self.add_borrow(&place, borrow_type.clone(), target);
                });
                return;
            }
            _ => panic!("lhs of x -> y must be either concrete or refs(x, 'a)"),
        }

        assert!(
            !matches!(target, Place::RefsDefinite(_, _)),
            "rhs of {} -{}-> {} cannot be refs(.., 'a)",
            source,
            borrow_type,
            target
        );

        let borrow_tuple = (source.clone(), borrow_type.clone(), target.clone());
        self.borrows
            .entry(target.base().clone())
            .and_modify(|set| {
                set.insert(borrow_tuple.clone());
            })
            .or_insert(im::hashset![borrow_tuple]);
    }
}

/// A place expression
///
/// Composed of one or more PlaceElements (variables, fields, dereferences etc.), a place
/// expression is a way to refer to a specific memory location. For example:
///
/// ```*(foo.bar)```
///
/// ... is a place expression.
//type PlaceBase = u32;
struct PlaceProjection(Vec<PlaceElement>);
/*impl fmt::Display for PlaceProjection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self
            .iter()
            .map(|pe| format!("{}", pe))
            .collect::<Vec<String>>()
            .join("."))
    }
}*/

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum Permission {
    Read,
    ReadWrite,
}

impl fmt::Display for Permission {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Permission::Read => write!(f, "r"),
            Permission::ReadWrite => write!(f, "rw"),
        }
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum PlaceBase {
    Local(u32),
    Arg(u32),
    PromotedConst(u32),
    InlineConst(u32),
    Wildcard,
}

impl fmt::Display for PlaceBase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PlaceBase::Local(local) => write!(f, "_{}", local),
            PlaceBase::Arg(base) => write!(f, "Arg(#{})", base),
            PlaceBase::PromotedConst(base) => write!(f, "PromConst(#{})", base),
            PlaceBase::InlineConst(base) => write!(f, "InlineConst(#{})", base),
            PlaceBase::Wildcard => write!(f, "WildcardArg"),
        }
    }
}

// TODO(ws): We don't really need BlackBox anymore do we? BlackBox == Concrete with base of Arg or PromotedConstant
// .         They're currently different because in the past the struct PlaceBase didn't exist
#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum Place {
    Concrete(PlaceBase, Vec<PlaceElement>),
    Reachable(Box<Place>),
    BlackBox(PlaceBase, Vec<PlaceElement>),
    WildcardArg,

    // TODO(ws): We would like to reintroduce this approximation
    //Refs(PlaceBase, Vec<PlaceElement>, Lifetime),
    RefsDefinite(Box<Place>, HashSet<Vec<PlaceElement>>),
}

impl Place {
    pub fn base(&self) -> &PlaceBase {
        match self {
            Place::Concrete(base, _) => base,
            Place::Reachable(base_place) | Place::RefsDefinite(base_place, _) => base_place.base(),
            Place::BlackBox(base, _) => base, //panic!("we should not get the base of a blackbox, it has no local base"),
            Place::WildcardArg => Box::leak(Box::new(PlaceBase::Wildcard)), // FIXME: This is a hacky way of returning a pointer to a wildcard base
        }
    }

    pub fn shares_base(left: &Place, right: &Place) -> bool {
        left.base() == right.base()
    }

    pub fn fp_merge(left: &Place, right: &Place) -> Place {
        assert!(
            Place::shares_base(left, right),
            "to merge must have the same base"
        );

        // They share the same base, if they have the same projections (i.e they are the same) we leave it in
        // If their projections differ we take an approximation of reachable from the base
        if left.projections() == right.projections() {
            // Can share the same base but one could be reachable./
            return match (left, right) {
                (Place::Reachable(_), _) => left.clone(),
                (_, Place::Reachable(_)) => right.clone(),
                _ => left.clone(),
            };
        }

        // We approximate to reachable from the base
        Place::Reachable(Box::new(match left {
            Place::Concrete(base, _) => {
                Place::Concrete(base.clone(), Place::longest_common_projection(left, right))
            }
            Place::Reachable(base) => *(base.clone()),
            Place::BlackBox(base, _) => {
                Place::BlackBox(base.clone(), Place::longest_common_projection(left, right))
            }
            Place::RefsDefinite(base, _) => panic!("refs(x,'a) should only be on lhs of x -> y"),
            Place::WildcardArg => Place::WildcardArg,
        }))
    }

    /*pub fn to_mir_local(&self) -> mir::Local {
        match self {
            Place::Concrete(base, _) => mir::Local::from_u32(*base),
            Place::Reachable(base_place) | Place::RefsDefinite(base_place, _) => {
                base_place.to_mir_local()
            }
            Place::BlackBox(_, _) => panic!("blackbox is not a local by defintion"),
        }
    }*/

    pub fn projections(&self) -> Vec<PlaceElement> {
        match self {
            Place::Concrete(_, elems) | Place::BlackBox(_, elems) => {
                elems.into_iter().map(|pe| pe.clone()).collect()
            }
            Place::Reachable(base_place) | Place::RefsDefinite(base_place, _) => {
                base_place.projections()
            }
            _ => Vec::new(),
        }
    }

    pub fn add_projection(place: Place, projection: PlaceElement) -> Place {
        match place {
            Place::Concrete(base, mut projections) => {
                projections.push(projection);
                Place::Concrete(base, projections)
            }
            Place::Reachable(base_place) => {
                Place::Reachable(Box::new(Place::add_projection(*base_place, projection)))
            }
            Place::BlackBox(arg_id, mut projections) => {
                projections.push(projection);
                Place::BlackBox(arg_id, projections)
            }
            Place::RefsDefinite(base_place, fields) => Place::RefsDefinite(
                Box::new(Place::add_projection(*base_place, projection)),
                fields,
            ),
            _ => place,
        }
    }

    pub fn longest_common_place(left: &Self, right: &Self) -> Self {
        assert!(std::mem::discriminant(left) == std::mem::discriminant(right));
        assert!(left.base() == right.base());

        match left.clone() {
            Place::Concrete(base, _) => {
                Place::Concrete(base, Place::longest_common_projection(left, right))
            }
            Place::Reachable(base) => *base,
            Place::BlackBox(base, _) => {
                Place::BlackBox(base, Place::longest_common_projection(left, right))
            }
            Place::RefsDefinite(base, _) => panic!("refs should only be on lhs of x -> y"),
            Place::WildcardArg => left.clone(),
        }
    }

    pub fn longest_common_projection(left: &Self, right: &Self) -> Vec<PlaceElement> {
        assert!(Place::shares_base(left, right), "the bases must match");

        left.projections()
            .into_iter()
            .zip(right.projections().into_iter())
            .take_while(|(left_place_element, right_place_element)| {
                left_place_element == right_place_element
            })
            .map(|(l, _)| l.clone())
            .collect()
    }

    pub fn is_parent(parent: &Place, child: &Place) -> bool {
        Place::shares_base(parent, child)
            && Place::longest_common_projection(parent, child).len() == parent.projections().len()
    }

    /*pub fn is_concrete(&self) -> bool {
        match self {
            Place::Concrete(_, _) => true,
            Place::Reachable(_) => false,
        }
    }*/

    // Convert from mir::Place to epcs::Place
    // Chains all the projection elements together
    pub fn from_mir(place: &mir::Place) -> Self {
        let mut projection_elements = Vec::new();
        let mut downcast_to = None;
        for pe in place.projection {
            if let mir::ProjectionElem::Downcast(Some(_), discrim) = pe.clone() {
                downcast_to = Some(discrim);
                continue;
            }

            if let mir::ProjectionElem::Field(field, _type) = pe.clone() {
                if let Some(discrim) = downcast_to {
                    projection_elements.push(PlaceElement::DowncastAndField(
                        discrim.as_usize(),
                        field.as_usize(),
                    ));
                    downcast_to = None;
                    continue;
                }
            }

            projection_elements.push(PlaceElement::from_mir(pe));
        }

        Place::Concrete(PlaceBase::Local(place.local.as_u32()), projection_elements)
    }
}

impl fmt::Display for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Place::Concrete(base, proj) => write!(
                f,
                "{}{}",
                base,
                proj.iter()
                    .map(|pe| format!("{}", pe))
                    .collect::<Vec<String>>()
                    .join(".")
            ),
            Place::Reachable(base_place) => write!(f, "reachable({})", *base_place),
            Place::BlackBox(base, proj) => write!(
                f,
                "blackbox({}){}",
                base,
                proj.iter()
                    .map(|pe| format!("{}", pe))
                    .collect::<Vec<String>>()
                    .join(".")
            ),
            Place::RefsDefinite(base_place, fields) => write!(
                f,
                "refs({}, {{ {} }})",
                base_place,
                fields
                    .iter()
                    .map(|pes| pes
                        .iter()
                        .map(|pe| format!("{}", pe))
                        .collect::<Vec<String>>()
                        .join("."))
                    .collect::<Vec<String>>()
                    .join(", "),
            ),
            Place::WildcardArg => write!(f, "WildcardSharedArg"),
        }
    }
}

/// Components of a Place (e.g. fields, indices, variables etc.)
#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
pub enum PlaceElement {
    Field(usize),
    Index(u64),
    Downcast(usize),
    DowncastAndField(usize, usize),
    Deref(),
    //PromotedMonomorphStatic(u32),
}

impl fmt::Display for PlaceElement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PlaceElement::Field(num) => write!(f, "f{}", num),
            PlaceElement::Index(num) => write!(f, "[{}]", num),
            PlaceElement::Deref() => write!(f, "*"),
            PlaceElement::DowncastAndField(discrim, field) => {
                write!(f, " as {}.f{}", discrim, field)
            }
            PlaceElement::Downcast(to) => write!(f, " as {}", to),
            //PlaceElement::PromotedMonomorphStatic(num) => write!(f, "static_{}", num),
        }
    }
}

impl PlaceElement {
    pub fn from_mir(place_elem: mir::PlaceElem) -> Self {
        match place_elem {
            mir::ProjectionElem::Deref => PlaceElement::Deref(),
            mir::ProjectionElem::Field(field, _type) => PlaceElement::Field(field.as_usize()),
            mir::ProjectionElem::Downcast(Some(_), discrim) => {
                PlaceElement::Downcast(discrim.as_usize())
            }
            _ => {
                panic!("Mir ProjectionElem {:?} not handled", place_elem);
                // PlaceElement::Deref()
            }
        }
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum BorrowType {
    Mutable,
    SleepingMutable,
    Shared,
}

impl BorrowType {
    pub fn from_mir(bk: mir::BorrowKind) -> Self {
        match bk {
            mir::BorrowKind::Shared => BorrowType::Shared,
            mir::BorrowKind::Mut { .. } => BorrowType::Mutable,
            _ => unimplemented!("BorrowKind not supported"),
        }
    }
}

impl fmt::Display for BorrowType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BorrowType::Mutable => write!(f, "m"),
            BorrowType::SleepingMutable => write!(f, "zzz_m"),
            BorrowType::Shared => write!(f, "s"),
        }
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum Borrow {
    Mutable(RefersTo),
    Immutable(RefersTo),
}

impl Borrow {
    fn refers_to(&self) -> &RefersTo {
        match self {
            Borrow::Mutable(refers_to) => refers_to,
            Borrow::Immutable(refers_to) => refers_to,
        }
    }
}

/// The target of a reference
///
/// Can be associated with either a specific borrow, or a number of regions
#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum RefersTo {
    Definite(Place),
    Indefinite(HashSet<Place>), // Set of borrows
                                //ReachableFrom(Place), // FP approximation
}

impl RefersTo {
    pub fn places(&self) -> HashSet<Place> {
        match self {
            RefersTo::Definite(place) => im::hashset![place.clone()],
            RefersTo::Indefinite(places) => places.clone(),
            //RefersTo::ReachableFrom(place) => std::iter::once(place),
        }
    }

    pub fn chain(left: RefersTo, right: RefersTo) -> RefersTo {
        match (left, right) {
            (RefersTo::Definite(left_place), RefersTo::Definite(right_place))
                if left_place == right_place =>
            {
                RefersTo::Definite(left_place)
            }
            (RefersTo::Definite(left_place), RefersTo::Definite(right_place)) => {
                RefersTo::Indefinite(im::hashset![left_place, right_place])
            }
            (RefersTo::Definite(left_place), RefersTo::Indefinite(right_set))
            | (RefersTo::Indefinite(right_set), RefersTo::Definite(left_place)) => {
                RefersTo::Indefinite(right_set.update(left_place))
            }
            (RefersTo::Indefinite(left_set), RefersTo::Indefinite(right_set)) => {
                RefersTo::Indefinite(left_set.union(right_set))
            }
        }
    }

    // Replaces any *x in a place with what the epcs says x points to.
    // TOOD(ws): complete
    pub fn resolve_dereferences(place: Place, epcs: &Epcs) -> RefersTo {
        //let (base, projection) = (place.base(), place.projections());
        let (base, projection) = match place.clone() {
            Place::Concrete(base, projection) => (base, projection),
            _ => return RefersTo::Definite(place.clone()),
        };

        let mut resolved_places = vec![Place::Concrete(base, Vec::<PlaceElement>::new())];

        for proj in projection {
            let mut new_resolved_places = Vec::new();

            for p in resolved_places {
                if let Place::BlackBox(_, _) = p {
                    // If we're talking about black boxes we want to keep derefs in the EPCS
                    // as we do not know what they point to but we want to keep the knowledge that
                    // we point to them.
                    new_resolved_places.push(Place::add_projection(p, proj));
                    continue;
                }

                if let Place::Reachable(_) = p {
                    new_resolved_places.push(p);
                    continue;
                }

                //info!("resolv_deref: {:?} {:?}", epcs, p);
                match proj {
                    PlaceElement::Deref() => match Epcs::get_borrow(&epcs, &p) {
                        Some((_, RefersTo::Definite(place))) => {
                            new_resolved_places.push(place.clone())
                        }
                        Some((_, RefersTo::Indefinite(places))) => {
                            for p1 in places {
                                new_resolved_places.push(p1.clone());
                            }
                        }
                        _ => panic!(
                            "cannot find borrow {} in pcs {}\nwhile trying to resolve {}",
                            p, epcs, place
                        ),
                    },
                    _ => new_resolved_places.push(Place::add_projection(p, proj)),
                }
            }
            resolved_places = new_resolved_places;
            /*resolved_places = match proj {
                // If we hit a deref we find the places in the EPCS and replace the place with the place it points to.
                // e.g _1 = *_2 // (_2 -> _3)
                // .   _1 = _3
                // e.g _1 = (*_2).0 // (_2 -> {_3, _4})
                // .   _1 = {_3.0, _4.0}
                PlaceElement::Deref() => resolved_places.flat_map(|place: &Place| -> dyn std::iter::Iterator<Item = Place> { match Epcs::get_borrow(&epcs, &place).unwrap() {
                    RefersTo::Definite(place) => std::iter::once(*place),
                    RefersTo::Indefinite(places) => places.iter(),
                    //RefersTo::ReachableFrom(place) => std::iter::once(place),
                }}),
                _ => resolved_places.map(|place| Place::add_projection(place, proj)),
            };*/
        }

        //let resolved_places = resolved_places.collect();
        assert!(
            resolved_places.len() > 0,
            "resolved places has a length > 0"
        );

        if resolved_places.len() == 1 {
            RefersTo::Definite(resolved_places[0].clone())
        } else {
            RefersTo::Indefinite(resolved_places.into_iter().collect::<HashSet<Place>>())
        }
    }
}

impl fmt::Display for RefersTo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RefersTo::Definite(p) => write!(f, "{}", p),
            RefersTo::Indefinite(places) => write!(
                f,
                "{{{}}}",
                places
                    .iter()
                    .map(|p| format!("{}", p))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
        }
    }
}
