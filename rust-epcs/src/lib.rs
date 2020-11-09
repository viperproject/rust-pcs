// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! The core EPCS library and API
#![feature(option_result_contains)]
#![feature(rustc_private)]
#![feature(iterator_fold_self)]

#[allow(dead_code)]
#[allow(unused)]
extern crate log;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
extern crate rustc_target;

pub mod analyses;

pub fn find_sysroot() -> String {
    let home = option_env!("RUSTUP_HOME").or(option_env!("MULTIRUST_HOME"));
    let toolchain = option_env!("RUSTUP_TOOLCHAIN").or(option_env!("MULTIRUST_TOOLCHAIN"));

    match (option_env!("RUST_SYSROOT"), home, toolchain) {
        (Some(sysroot), _, _) => sysroot.to_owned(),
        (None, Some(home), Some(toolchain)) => format!("{}/toolchains/{}", home, toolchain),
        _ => panic!("need to specify RUST_SYSROOT env var or use rustup or multirust"),
    }
}

pub fn rustc_default_args() -> &'static [&'static str] {
    &[
        "--crate-type=lib",
        "-Zalways-encode-mir",
        //"-Zmir-emit-retag",
        "-Zmir-opt-level=0",
        "--cap-lints=allow",
    ]
}
