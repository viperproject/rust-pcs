#![feature(rustc_private)]
#[allow(dead_code)]
#[allow(unused)]
extern crate env_logger;
extern crate lazy_static;
extern crate log;
extern crate rust_epcs;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;

use log::info;
use rust_epcs::analyses::common::MirAnalysisResult;
use rust_epcs::analyses::epcs::{BorrowType, Epcs, Place, PlaceBase, PlaceElement, RefersTo};
use rust_epcs::analyses::epcs_builder;
use rust_epcs::{find_sysroot, rustc_default_args};
use rustc_hir::def_id;
use rustc_interface::interface;
use rustc_middle::mir;
use std::env;
use std::path::Path;
use std::path::PathBuf;

use im;

fn init_logger() {
    let _ = env_logger::builder().is_test(true).try_init();
}

fn get_test_resource(resource: &str) -> Box<Path> {
    let mut d: PathBuf = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    d.push("tests/resources");
    d.push(resource);
    return d.into_boxed_path();
}

fn mir_location(bb: usize, index: usize) -> mir::Location {
    mir::Location {
        block: mir::BasicBlock::from_usize(bb),
        statement_index: index,
    }
}

#[derive(Clone)]
pub struct EpcsUnitTestCallback {
    pub result: Option<MirAnalysisResult<Epcs>>,
}
impl EpcsUnitTestCallback {
    pub fn new() -> EpcsUnitTestCallback {
        EpcsUnitTestCallback { result: None }
    }
}

impl rustc_driver::Callbacks for EpcsUnitTestCallback {
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &interface::Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> rustc_driver::Compilation {
        compiler.session().abort_if_errors();

        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            if self.result.is_some() {
                panic!("thread error!");
            }

            let def_id = tcx.body_owners().nth(0).unwrap().to_def_id();
            let mir: &mir::Body = tcx.optimized_mir(def_id);
            let pcs = epcs_builder::compute_epcs(tcx, mir);

            self.result = Some(pcs);
        });

        compiler.session().abort_if_errors();

        rustc_driver::Compilation::Stop
    }
}

fn calculate_epcs(input_file_path: Box<Path>) -> MirAnalysisResult<Epcs> {
    let sysroot = find_sysroot();
    info!("Using SYSROOT {}", sysroot);

    let mut rustc_args: Vec<String> = Vec::new();
    rustc_args.push("rustc".to_owned());
    rustc_args.push(input_file_path.to_str().unwrap().to_owned());
    rustc_args.push(format!("{}{}", "--sysroot=", sysroot));
    rustc_args.extend(rustc_default_args().iter().map(ToString::to_string));

    //rustc_driver::init_rustc_env_logger();
    let mut callback = EpcsUnitTestCallback::new();
    let r = &mut callback;
    rustc_driver::install_ice_hook();
    let result = rustc_driver::catch_fatal_errors(move || {
        rustc_driver::run_compiler(&rustc_args, r, None, None)
    })
    .and_then(|result| result);

    assert!(!result.is_err());

    callback.clone().result.unwrap()
}

/*#[test]
fn integ_test_mut_borrow_definite() {
    init_logger();
    let input_file = get_test_resource("reborrow.rs");
    let result = calculate_epcs(input_file);
*/
/*// bb0[13]: _5 = &_3
let point = Point {
    position: Position::Start,
    bb_number: 0,
    index_in_bb: 14,
};

let expected_referrer = Place::ConcretePlace(vec![PlaceElement::Local(5)]);
let expected_loan = Loan {
    uid: "\"bw0\"".to_owned(),
};

let expected_refto_place = Place::ConcretePlace(vec![PlaceElement::Local(3)]);
let expected_refto = RefersTo::Definite(expected_loan, expected_refto_place.clone());

let actual_refto = Epcs::deref(
    result.pointwise_epcs.get(&point).unwrap(),
    &expected_referrer,
)
.unwrap();

assert_eq!(
    expected_refto, *actual_refto,
    "Reference _5 --> _3 not found"
);
assert!(
    !result
        .pointwise_epcs
        .get(&point)
        .unwrap()
        .places
        .contains(&expected_refto_place),
    "Referred to place should be removed from PCS for mut borrow"
);*/
/*}

#[test]
fn integ_test_borrow_indefinite() {
    init_logger();
    let input_file = get_test_resource("simplest_loop.rs");
    let result = calculate_epcs(input_file);

    // bb3[1]: _9 = &(*((*_3).1: &Node<'_>));
    let point = Point {
        position: Position::Start,
        bb_number: 3,
        index_in_bb: 2,
    };

    let expected_referrer = Place::ConcretePlace(vec![PlaceElement::Local(9)]);

    let expected_var_blocked = Local { id: 3 };
    let expected_var_blocked_1 = Local { id: 1 };

    match Epcs::deref(
        result.pointwise_epcs.get(&point).unwrap(),
        &expected_referrer,
    )
    .unwrap()
    {
        RefersTo::Indefinite(regions) => {
            assert!(
                Region::all_vars_blocked(regions).contains(&expected_var_blocked),
                "Expected indefinite borrow to block used variable"
            );
            assert!(
                Region::all_vars_blocked(regions).contains(&expected_var_blocked_1),
                "Expected borrow to block transitive variable"
            );
        }
        _ => panic!("Expected region from _9 --> "),
    };
}

#[test]
fn integ_test_expire_borrow() {
    init_logger();
    let input_file = get_test_resource("reborrow.rs");
    let result = calculate_epcs(input_file);

    // bb0[24]:  (borrows expire here)
    let point = Point {
        position: Position::Start,
        bb_number: 0,
        index_in_bb: 24,
    };

    let expected_referrer = Place::ConcretePlace(vec![PlaceElement::Local(6)]);
    let expected_refto_place =
        Place::ConcretePlace(vec![PlaceElement::Local(3), PlaceElement::Field(0)]);

    let actual_refto = Epcs::deref(
        result.pointwise_epcs.get(&point).unwrap(),
        &expected_referrer,
    );

    assert_eq!(
        None, actual_refto,
        "Reference _6 --> _3.f0 should be removed"
    );
    assert!(
        result
            .pointwise_epcs
            .get(&point)
            .unwrap()
            .places
            .contains(&expected_refto_place),
        "3.f0 should be restored"
    );
}

*/
#[test]
fn integ_test_expire_borrow() {
    init_logger();
    let input_file = get_test_resource("reborrow.rs");
    let result = calculate_epcs(input_file);
}

#[test]
fn integ_test_simplest_loop() {
    init_logger();
    let input_file = get_test_resource("simplest_loop.rs");
    let result = calculate_epcs(input_file);
}

#[test]
fn integ_test_append() {
    init_logger();
    let input_file = get_test_resource("append.rs");
    let result = calculate_epcs(input_file);
}

#[test]
fn integ_test_fra1() {
    init_logger();
    let input_file = get_test_resource("function_annotation1.rs");
    let result = calculate_epcs(input_file);
}

#[test]
fn integ_test_fra2() {
    init_logger();
    let input_file = get_test_resource("function_annotation2.rs");
    let result = calculate_epcs(input_file);
}

#[test]
fn integ_test_fra3() {
    init_logger();
    let input_file = get_test_resource("arg_struct.rs");
    let result = calculate_epcs(input_file);
}

#[test]
fn integ_test_pack_expire() {
    init_logger();
    let input_file = get_test_resource("pack.rs");
    let result = calculate_epcs(input_file);
}

#[test]
fn integ_test_permissions() {
    init_logger();
    let input_file = get_test_resource("permissions.rs");
    let result = calculate_epcs(input_file);
}

#[test]
fn integ_test_expire_mutable() {
    init_logger();
    let input_file = get_test_resource("expire_mutable.rs");
    let result = calculate_epcs(input_file);
}

#[test]
fn integ_test_two_phase_borrow() {
    init_logger();
    let input_file = get_test_resource("two_phase_borrow.rs");
    let result = calculate_epcs(input_file);
}

#[test]
fn integ_test_enum_split_borrows() {
    init_logger();
    let input_file = get_test_resource("enum_split_borrows.rs");
    let result = calculate_epcs(input_file);
}

#[test]
fn integ_test_expire_shared_with_mutable() {
    init_logger();
    let input_file = get_test_resource("expire_shared_with_mutable.rs");
    let result = calculate_epcs(input_file);

    assert!(!result.after_statement[&mir_location(0, 5)]
        .places
        .contains(&Place::Concrete(PlaceBase::Local(2), Vec::new())),);
}

#[test]
fn integ_test_expire_mutable_with_mutable() {
    init_logger();
    let input_file = get_test_resource("expire_mutable_with_mutable.rs");
    let result = calculate_epcs(input_file);
}

#[test]
fn integ_test_simple_if() {
    init_logger();
    let input_file = get_test_resource("simple_if.rs");
    let result = calculate_epcs(input_file);

    let local = Place::Concrete(PlaceBase::Local(4), Vec::new());
    assert!(result.after_statement[&mir_location(3, 0)]
        .refs
        .contains_key(&local),);

    assert!(matches!(result.after_statement[&mir_location(3, 0)]
        .refs.get(&local).unwrap(), (BorrowType::Shared, RefersTo::Indefinite(refs)) if refs.len() == 2 && refs.contains(&Place::Concrete(PlaceBase::Local(3), Vec::new())) && refs.contains(&Place::Concrete(PlaceBase::Local(2), Vec::new()))));
}

#[test]
fn integ_test_expire_borrows_liveness() {
    init_logger();
    let input_file = get_test_resource("expire_borrows_liveness.rs");
    let result = calculate_epcs(input_file);

    assert!(!result.after_statement[&mir_location(0, 14)]
        .refs
        .contains_key(&Place::Concrete(PlaceBase::Local(4), Vec::new())));
    assert!(!result.after_statement[&mir_location(0, 15)]
        .refs
        .contains_key(&Place::Concrete(PlaceBase::Local(3), Vec::new())));
}
