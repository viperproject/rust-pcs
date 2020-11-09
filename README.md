# Rust PCS

This project provides the prototype of a library to compute Rust's Place Capabilities Summary (PCS) information. For details see the writups by Dylan Wolff ([project description](https://ethz.ch/content/dam/ethz/special-interest/infk/chair-program-method/pm/documents/Education/Theses/Dylan_Wolff_RICS_Report.pdf), [final report](https://ethz.ch/content/dam/ethz/special-interest/infk/chair-program-method/pm/documents/Education/Theses/Dylan_Wolff_RICS_Report.pdf)) and by William Seddon ([project description](https://ethz.ch/content/dam/ethz/special-interest/infk/chair-program-method/pm/documents/Education/Theses/William_Seddon_MA_Description.pdf), [final report](https://ethz.ch/content/dam/ethz/special-interest/infk/chair-program-method/pm/documents/Education/Theses/William_Seddon_MS_Report.pdf)).

## How do I run it?

1. `./x.py setup` to install the system dependencies.
2. `./x.py build --all` to compile the project.
3. `./x.py run --bin rust-epcs-cli rust-epcs/tests/resources/append.rs` to run the command line interface.

Note that `rust-epcs/tests/resources/append.rs` is just an example. Feel free to replace it in the command above with the path to another Rust program.

This will run the CLI with the appropriate `RUST_SYSROOT`, displaying at the end of the execution a textual (MIR-style) and a graphical (in the DOT file format) representation of the computed pointwise PCSs.

For the IDE plugin see the `vscode-epcs-hover` folder .

## License

Copyright 2020, ETH Zurich.

This project is released under the Mozilla Public License, v. 2.0 except for:

* the file `lsp-epcs-hover/src/main.rs`, which is an adaptation of <https://github.com/rust-analyzer/lsp-server/blob/master/examples/goto_def.rs>

* the file `vscode-epcs-hover/client/src/extension.ts`, which is an adaptation of <https://github.com/microsoft/vscode-languageserver-node-example/blob/master/client/src/extension.ts>
