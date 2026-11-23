//! Login for ACP clients: the methods `initialize` advertises and the
//! `-32000` answer a session start (or `authenticate`) gets while no model
//! provider is logged in. The login itself runs in eukhe's own terminal UI.

use serde_json::{json, Value};

use super::jsonrpc;

/// The ACP "authentication required" error code.
pub(super) const AUTH_REQUIRED: i64 = -32000;
/// The method a client confirms with `authenticate` once the user logged in.
pub(super) const AGENT_METHOD_ID: &str = "eukhe-login";
/// The method a terminal-capable client runs as `eukhe` in a terminal.
pub(super) const TERMINAL_METHOD_ID: &str = "eukhe-terminal-login";
/// The command that logs in, then the command typed in it.
const LOGIN_COMMAND: &str = "eukhe";
const LOGIN_SLASH_COMMAND: &str = "/login";
const INSTRUCTIONS: &str =
    "Run `eukhe` in a terminal, type /login and pick a model provider, then start the session again.";

/// Whether the client runs terminal login methods
/// (`clientCapabilities.auth.terminal`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) enum TerminalLogin {
    #[default]
    Unsupported,
    Supported,
}

impl TerminalLogin {
    /// The client's capability from its `initialize` params.
    pub(super) fn of_initialize(params: &Value) -> TerminalLogin {
        if params["clientCapabilities"]["auth"]["terminal"] == json!(true) {
            TerminalLogin::Supported
        } else {
            TerminalLogin::Unsupported
        }
    }
}

/// The `authMethods`: the agent method always, the terminal method for a
/// client that runs one.
pub(super) fn auth_methods(terminal: TerminalLogin) -> Value {
    let agent = json!({
        "id": AGENT_METHOD_ID,
        "name": "Log in to a model provider",
        "description": INSTRUCTIONS,
    });
    match terminal {
        TerminalLogin::Unsupported => json!([agent]),
        TerminalLogin::Supported => json!([agent, {
            "type": "terminal",
            "id": TERMINAL_METHOD_ID,
            "name": "Log in in a terminal",
            "description": "Opens eukhe; type /login and pick a model provider, then quit.",
            "args": [],
        }]),
    }
}

/// The answer to a request that needs a logged-in model provider.
pub(super) fn auth_required(id: &Value, terminal: TerminalLogin) -> Value {
    jsonrpc::error_response(
        id,
        AUTH_REQUIRED,
        "Authentication required",
        Some(&json!({
            "login": {
                "command": LOGIN_COMMAND,
                "slashCommand": LOGIN_SLASH_COMMAND,
                "instructions": INSTRUCTIONS,
            },
            "authMethods": auth_methods(terminal),
        })),
    )
}

/// Whether `method_id` names an advertised method.
pub(super) fn is_method(method_id: &str) -> bool {
    method_id == AGENT_METHOD_ID || method_id == TERMINAL_METHOD_ID
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_terminal_method_follows_the_client_capability() {
        let ids = |params: Value| {
            auth_methods(TerminalLogin::of_initialize(&params))
                .as_array()
                .map(|methods| {
                    methods
                        .iter()
                        .map(|method| method["id"].as_str().unwrap_or_default().to_string())
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default()
        };
        assert_eq!(
            [
                ids(json!({ "clientCapabilities": {} })),
                ids(json!({ "clientCapabilities": { "auth": { "terminal": true } } })),
            ],
            [
                vec![AGENT_METHOD_ID.to_string()],
                vec![AGENT_METHOD_ID.to_string(), TERMINAL_METHOD_ID.to_string()],
            ]
        );
    }
}
