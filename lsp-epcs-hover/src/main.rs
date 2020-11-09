// Adapted from https://github.com/rust-analyzer/lsp-server/blob/master/examples/goto_def.rs

#![feature(rustc_private)]
use std::error::Error;

use log::info;
use lsp_types::{
    request::HoverRequest, Hover, HoverContents, HoverProviderCapability, InitializeParams,
    MarkedString, ServerCapabilities,
};

use lsp_server::{Connection, Message, Request, RequestId, Response};

use std::sync::mpsc::channel;

extern crate rust_epcs;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
mod compiler_hook;

fn main() -> Result<(), Box<dyn Error + Sync + Send>> {
    // Set up logging. Because `stdio_transport` gets a lock on stdout and stdin, we must have
    // our logging only write out to stderr.
    flexi_logger::Logger::with_str("info").start().unwrap();
    info!("starting generic LSP server");

    // Create the transport. Includes the stdio (stdin and stdout) versions but this could
    // also be implemented to use sockets or HTTP.
    let (connection, io_threads) = Connection::stdio();

    // Run the server and wait for the two threads to end (typically by trigger LSP Exit event).
    let mut cap = ServerCapabilities::default();
    cap.hover_provider = Some(HoverProviderCapability::Simple(true));
    let server_capabilities = serde_json::to_value(&cap).unwrap();
    let initialization_params = connection.initialize(server_capabilities)?;
    main_loop(&connection, initialization_params)?;
    io_threads.join()?;

    // Shut down gracefully.
    info!("shutting down server");
    Ok(())
}

fn main_loop(
    connection: &Connection,
    params: serde_json::Value,
) -> Result<(), Box<dyn Error + Sync + Send>> {
    let _params: InitializeParams = serde_json::from_value(params).unwrap();
    info!("starting example main loop");
    for msg in &connection.receiver {
        info!("got msg: {:?}", msg);
        match msg {
            Message::Request(req) => {
                if connection.handle_shutdown(&req)? {
                    return Ok(());
                }
                info!("got request: {:?}", req);

                match cast::<HoverRequest>(req) {
                    Ok((id, params)) => {
                        info!("got hover request #{}: {:?}", id, params);
                        let pos = params.text_document_position_params.position;
                        let url = params.text_document_position_params.text_document.uri;

                        let sysroot = rust_epcs::find_sysroot();
                        info!("Using sysroot: {}", sysroot);

                        let mut rustc_args: Vec<String> = Vec::new();
                        rustc_args.push("rustc".to_owned());
                        rustc_args.push(url.as_str().to_owned().replace("file://", ""));
                        rustc_args.push("--crate-type=lib".to_owned());
                        rustc_args.push(format!("{}{}", "--sysroot=", sysroot));
                        rustc_args.extend(
                            rust_epcs::rustc_default_args()
                                .iter()
                                .map(ToString::to_string),
                        );
                        let (tx, rx): (
                            std::sync::mpsc::Sender<String>,
                            std::sync::mpsc::Receiver<String>,
                        ) = channel();

                        let mut callback =
                            compiler_hook::EpcsCallback::new(tx, pos.line, pos.character);
                        rustc_driver::install_ice_hook();
                        let result = rustc_driver::catch_fatal_errors(move || {
                            rustc_driver::run_compiler(&rustc_args, &mut callback, None, None)
                        })
                        .and_then(|result| result);
                        assert!(result.is_ok());
                        let hover_str = format!("```\n{}\n```", rx.recv().unwrap());
                        info!("Got result: {}", hover_str);

                        let result = Some(Hover {
                            contents: HoverContents::Scalar(MarkedString::String(hover_str)),
                            range: None,
                        });
                        let result = serde_json::to_value(&result).unwrap();
                        let resp = Response {
                            id,
                            result: Some(result),
                            error: None,
                        };
                        connection.sender.send(Message::Response(resp))?;
                        continue;
                    }
                    Err(req) => req,
                };
                // ...
            }
            Message::Response(resp) => {
                info!("got response: {:?}", resp);
            }
            Message::Notification(not) => {
                info!("got notification: {:?}", not);
            }
        }
    }
    Ok(())
}

fn cast<R>(req: Request) -> Result<(RequestId, R::Params), Request>
where
    R: lsp_types::request::Request,
    R::Params: serde::de::DeserializeOwned,
{
    req.extract(R::METHOD)
}
