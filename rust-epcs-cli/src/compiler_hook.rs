// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Contains callback infrastructure to hook into the Rust compiler

extern crate rustc_hir;
extern crate rustc_mir;

use rust_epcs::analyses::common::{print_mir_graphviz, print_mir_result};
use rust_epcs::analyses::epcs_builder;
use rustc_hir::def_id;
use rustc_interface::interface;
use rustc_middle::mir;

use rustc_span;

pub struct DumpCallback {}
impl DumpCallback {
    pub fn new() -> DumpCallback {
        DumpCallback {}
    }
}

impl rustc_driver::Callbacks for DumpCallback {
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &interface::Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> rustc_driver::Compilation {
        compiler.session().abort_if_errors();

        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            // TODO get rid of this unwrap

            let def_id: def_id::DefId = tcx.body_owners().nth(0).unwrap().to_def_id();
            let mir: &mir::Body = tcx.optimized_mir(def_id);
            let pcs = epcs_builder::compute_epcs(tcx, mir);
            //let liveness = rust_epcs::analyses::liveness::compute_liveness(mir);
            //print_mir_result(mir, &liveness);

            print_mir_source(mir, &pcs);
            print_mir_graphviz(mir, &pcs);
        });

        compiler.session().abort_if_errors();

        rustc_driver::Compilation::Stop
    }
}

pub fn print_mir_source<T: std::fmt::Display>(
    mir: &mir::Body,
    result: &rust_epcs::analyses::common::MirAnalysisResult<T>,
) {
    let pcs_before: std::collections::HashMap<usize, rust_epcs::analyses::epcs::Epcs> =
        std::collections::HashMap::new();
    let pcs_after: std::collections::HashMap<usize, rust_epcs::analyses::epcs::Epcs> =
        std::collections::HashMap::new();

    for bb in mir.basic_blocks().indices() {
        let mir::BasicBlockData {
            ref statements,
            ref terminator,
            ..
        } = mir[bb];

        for statement_index in 0..statements.len() {
            let location = mir::Location {
                block: bb,
                statement_index,
            };

            let statement = mir[bb].statements[statement_index].clone();

            println!("\n    {}", result.before_statement[&location]);
            println!("    {:?} //{:?}[{}]", statement, bb, statement_index);
            println!("    {:?}", statement.source_info);
            println!("    {}\n", result.after_statement[&location]);
        }
        if let Some(t) = terminator {
            println!("    {:?} // terminator\n", t.kind);
        }
        println!("{}", result.after_block[&bb]);
        println!("}}\n")
    }
}
