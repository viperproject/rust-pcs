// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(rustc_private)]
#[allow(dead_code)]
#[allow(unused)]
extern crate clap;
extern crate env_logger;
extern crate log;
extern crate log4rs;
extern crate rust_epcs;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

use clap::App;
use clap::Arg;
use clap::ArgMatches;
use log::info;
use std::path::Path;

use log::LevelFilter;
use log4rs::append::console::ConsoleAppender;
use log4rs::config::{Appender, Config, Logger, Root};

mod compiler_hook;
use compiler_hook::DumpCallback;

/// Entrypoint for the EPCS CLI
fn main() -> Result<(), rustc_errors::ErrorReported> {
    let matches: ArgMatches = App::new("EPCS CLI")
        .arg(
            Arg::with_name("FILE TO EPCS")
                .help("Sets the input file to use")
                .required(true)
                .index(1),
        )
        .arg(
            Arg::with_name("verbosity")
                .short("v")
                .multiple(true)
                .help("Sets the level of verbosity"),
        )
        .arg(
            Arg::with_name("RUST SYSROOT")
                .short("s")
                .long("sysroot")
                .takes_value(true)
                .help("Sets the rust compiler system root"),
        )
        .get_matches();

    setup_logging(matches.occurrences_of("verbosity"));

    let input_file = matches.value_of("FILE TO EPCS").unwrap();
    info!("Using input file: {}", input_file);

    let sysroot = rust_epcs::find_sysroot();
    info!("Using sysroot: {}", sysroot);

    let file_path = Path::new(input_file);
    let mut rustc_args: Vec<String> = Vec::new();
    rustc_args.push("rustc".to_owned());
    rustc_args.push(file_path.to_str().unwrap().to_owned());
    rustc_args.push("--crate-type=lib".to_owned());
    rustc_args.push(format!("{}{}", "--sysroot=", sysroot));
    rustc_args.extend(
        rust_epcs::rustc_default_args()
            .iter()
            .map(ToString::to_string),
    );

    let mut callback = DumpCallback::new();

    rustc_driver::install_ice_hook();
    let result = rustc_driver::catch_fatal_errors(move || {
        rustc_driver::run_compiler(&rustc_args, &mut callback, None, None)
    })
    .and_then(|result| result);

    result
}

fn setup_logging(vb_occurrences: u64) {
    let verbosity = match vb_occurrences {
        0 => LevelFilter::Warn,
        1 => LevelFilter::Info,
        2 => LevelFilter::Debug,
        3 | _ => LevelFilter::Trace,
    };

    let stdout = ConsoleAppender::builder().build();
    let config = Config::builder()
        .appender(Appender::builder().build("stdout", Box::new(stdout)))
        .logger(Logger::builder().build("rust_epcs_cli", verbosity))
        .logger(Logger::builder().build("rust_epcs", verbosity))
        .logger(Logger::builder().build("analyses", verbosity))
        .logger(Logger::builder().build("borrow_checker_output", verbosity))
        .build(Root::builder().appender("stdout").build(LevelFilter::Trace))
        .unwrap();

    let _handle = log4rs::init_config(config).unwrap();
}
