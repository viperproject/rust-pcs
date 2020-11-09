// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Contains callback infrastructure to hook into the Rust compiler

extern crate rustc_hir;
extern crate rustc_mir;

use rust_epcs::analyses::common::closest_result_to;
use rust_epcs::analyses::epcs_builder;
use rust_epcs::analyses::pretty_printer;
use rustc_hir::def_id;
use rustc_interface::interface;
use rustc_middle::mir;

use log::info;

#[derive(Clone)]
pub struct EpcsCallback {
    tx: std::sync::mpsc::Sender<String>,
    line: u64,
    col: u64,
}
impl EpcsCallback {
    pub fn new(tx: std::sync::mpsc::Sender<String>, line: u64, col: u64) -> EpcsCallback {
        EpcsCallback { tx, line, col }
    }
}

impl rustc_driver::Callbacks for EpcsCallback {
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &interface::Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> rustc_driver::Compilation {
        compiler.session().abort_if_errors();

        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            // TODO get rid of this unwrap

            let source_map = compiler.session().source_map();
            let def_id: def_id::DefId = tcx.body_owners().nth(0).unwrap().to_def_id();
            let mir: &mir::Body = tcx.optimized_mir(def_id);
            let pcs = epcs_builder::compute_epcs(tcx, mir);
            let closest_pcs =
                closest_result_to(mir, &pcs, source_map, self.line as usize, self.col as usize);

            info!("Found closest: {}", closest_pcs);
            let outp = pretty_printer::pretty_print_epcs_rust(mir, tcx, closest_pcs);
            info!("Pretty printed: {}", outp);
            self.tx.send(outp).unwrap();
        });

        compiler.session().abort_if_errors();

        rustc_driver::Compilation::Stop
    }
}
