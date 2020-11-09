// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License. See License.txt in the project root for license information.

import * as vscode from 'vscode';
import * as lsp from 'vscode-languageclient';
import * as process from 'process';

let client: lsp.LanguageClient;

export function activate(context: vscode.ExtensionContext) {
	// FIXME: the following is not platform generic, but it works on Ubuntu.
	let serverExe = `${__dirname}/../../../target/debug/lsp-epcs-hover`;
	const env = {
		...process.env,
		LD_LIBRARY_PATH:
			`${process.env.HOME}/.rustup/toolchains/` +
			`nightly-2020-07-27-x86_64-unknown-linux-gnu/lib/`
	};
	let serverOptions: lsp.ServerOptions = {
        run: {command: serverExe, args:[], options: {env}},
        debug: {command: serverExe, args:[], options: {env}}
    };

	// Options to control the language client
	let clientOptions: lsp.LanguageClientOptions = {
		// Register the server for Rust source code files
		documentSelector: [
		    { scheme: 'file', language: 'rust' }
		],
	};

	// Create the language client and start the client.
	client = new lsp.LanguageClient(
		'languageServerExample',
		'Language Server Example',
		serverOptions,
		clientOptions
	);

	// Start the client. This will also launch the server
	client.start();
}

export async function deactivate(): Promise<void> {
	if (!client) {
		return;
	}
	await client.stop();
}
