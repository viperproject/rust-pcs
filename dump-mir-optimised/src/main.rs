#![feature(rustc_private)]

use std::env;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir;
use rustc_driver::Compilation;
use rustc_interface::interface;
use rustc_interface::Queries;
use rustc_middle::mir;

struct Callback {}

impl rustc_driver::Callbacks for Callback {
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &interface::Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        compiler.session().abort_if_errors();

        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            let def_ids = tcx.body_owners().map(|bod| bod.to_def_id());

            def_ids.for_each(|def_id| {
                println!("Body: {:?}", def_id);
                print_mir(tcx.optimized_mir(def_id));
            });
        });

        compiler.session().abort_if_errors();

        Compilation::Stop
    }
}

pub fn print_mir(mir: &mir::Body) {
    for bb in mir.basic_blocks().indices() {
        println!("{:?} {{", bb);
        let mir::BasicBlockData {
            ref statements,
            ref terminator,
            ..
        } = mir[bb];
        for statement_index in 0..statements.len() {
            println!(
                "    {:?} //{:?}[{}]",
                statements[statement_index], bb, statement_index
            );
        }
        if let Some(t) = terminator {
            println!("    {:?} // terminator", t.kind);
        }
        println!("}}\n")
    }
}

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
        "-Zalways-encode-mir",
        "-Zmir-opt-level=0",
        "--cap-lints=allow",
    ]
}

fn main() -> Result<(), rustc_errors::ErrorReported> {
    let args: Vec<String> = env::args().collect();

    let sysroot = find_sysroot();

    let mut rustc_args: Vec<String> = Vec::new();
    rustc_args.push("rustc".to_owned()); // First arg is always the program name
    rustc_args.push(args[1].to_string());
    rustc_args.push("--crate-type=lib".to_owned());
    rustc_args.push(format!("{}{}", "--sysroot=", sysroot));
    rustc_args.extend(rustc_default_args().iter().map(ToString::to_string));

    //rustc_driver::init_rustc_env_logger();
    rustc_driver::install_ice_hook();
    rustc_driver::catch_fatal_errors(move || {
        rustc_driver::run_compiler(&rustc_args, &mut Callback {}, None, None)
    })
    .and_then(|result| result)
}
