//! The console-variable commands: `/set`,
//! `/set --global`, `/toggle`, `/alias`, `/cvar` and `/cvar save`, each
//! sent to the session's daemon as a `cvar` command list, plus the one
//! client method a key bind runs its commands through
//! ([`SessionUi::send_cvar_line`]).

use eukhe_types::cvar::{parse_list, render_list, Command};
use eukhe_types::daemon::{CvarFailureData, CvarReply, CvarValue};

use super::{
    AgentView, DaemonCommand, Duration, Map, SessionUi, StatusKind, Value, UI_REQUEST_TIMEOUT_MS,
};

/// Where a cvar line applies.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CvarLineTarget {
    /// The session's own sets and aliases.
    Session,
    /// The global config.cfg (`set` and `toggle` only).
    Global,
}

/// Why a cvar line did not apply.
#[derive(Debug, thiserror::Error)]
pub(crate) enum CvarLineFailure {
    #[error(
        "timed out after {}ms waiting for the Eukhe daemon response",
        timeout.as_millis()
    )]
    TimedOut { timeout: Duration },
    /// The request failed (the connection, a closed link).
    #[error("{0:#}")]
    Request(#[source] anyhow::Error),
    /// The daemon rejected the line: its message, or the typed data of a
    /// rejected command (a failure line with `data` has no `error`: the
    /// typed data carries the message).
    #[error(
        "{}",
        error
            .as_deref()
            .or(data.as_ref().map(|data| data.message.as_str()))
            .unwrap_or("unknown error")
    )]
    Rejected {
        error: Option<String>,
        data: Option<CvarFailureData>,
    },
    #[error("invalid cvar reply: {0}")]
    Malformed(#[source] serde_json::Error),
}

/// A value as a cvar command writes it (a text bare, anything else as
/// JSON).
fn value_text(value: &Value) -> String {
    match value {
        Value::String(text) => text.clone(),
        Value::Null | Value::Bool(_) | Value::Number(_) | Value::Array(_) | Value::Object(_) => {
            value.to_string()
        }
    }
}

impl SessionUi {
    /// Send the command list `line` to the session's daemon (`cvar`):
    /// the session's replicated values after it, or why it did not apply
    /// (then nothing of it applied). Bounded like every key-path request.
    pub(crate) async fn send_cvar_line(
        &self,
        line: &str,
        target: CvarLineTarget,
    ) -> Result<CvarReply, CvarLineFailure> {
        let command = DaemonCommand::Cvar {
            id: None,
            active_session_id: self.active_session_id.clone(),
            line: line.to_string(),
            global: target == CvarLineTarget::Global,
            rest: Map::default(),
        };
        let timeout = Duration::from_millis(UI_REQUEST_TIMEOUT_MS);
        let response = tokio::time::timeout(timeout, self.client.request(command))
            .await
            .map_err(|_| CvarLineFailure::TimedOut { timeout })?
            .map_err(CvarLineFailure::Request)?;
        if !response.success {
            return Err(CvarLineFailure::Rejected {
                error: response.error,
                data: response
                    .data
                    .and_then(|data| serde_json::from_value(data).ok()),
            });
        }
        serde_json::from_value(response.data.unwrap_or(Value::Null))
            .map_err(CvarLineFailure::Malformed)
    }

    /// Run `line` and report it: the new value of `shown` (when the reply
    /// carries it) or the line itself on success, the daemon's message as
    /// an error row on failure.
    pub(crate) async fn run_cvar_line(
        &mut self,
        line: &str,
        target: CvarLineTarget,
        view: &mut AgentView,
    ) -> Option<CvarReply> {
        match self.send_cvar_line(line, target).await {
            Ok(reply) => {
                // The status line follows `terminal.showSpeed` at once.
                if let Some(show) = reply
                    .values
                    .iter()
                    .find(|value| value.id == "terminal.showSpeed")
                    .and_then(|value| value.value.as_bool())
                {
                    view.show_speed = show;
                    self.sync_speed(view);
                }
                // The pinned agents block follows its two settings at once.
                let value_of = |id: &str| {
                    reply
                        .values
                        .iter()
                        .find(|value| value.id == id)
                        .map(|value| &value.value)
                };
                if let Some(mode) = value_of("terminal.pinnedAgents").and_then(Value::as_str) {
                    view.pinned_agents = crate::agents_panel::PinnedAgents::parse(mode);
                }
                if let Some(secs) = value_of("terminal.stuckAfterSecs").and_then(Value::as_u64) {
                    view.stuck_after_secs = secs;
                }
                let shown = parse_list(line)
                    .ok()
                    .and_then(|commands| match commands.as_slice() {
                        [Command::Set { id, .. } | Command::Toggle { id }] => {
                            reply.values.iter().find(|value| value.id == *id).map(
                                |CvarValue { id, value }| format!("{id} = {}", value_text(value)),
                            )
                        }
                        _ => None,
                    });
                let scope = match target {
                    CvarLineTarget::Session => "",
                    CvarLineTarget::Global => " (global)",
                };
                self.plain_row(
                    &format!("{}{scope}", shown.as_deref().unwrap_or(line)),
                    view,
                );
                Some(reply)
            }
            Err(failure) => {
                self.error_row(&failure.to_string(), view);
                None
            }
        }
    }

    /// `/set [--global] <id> <value>`, `/toggle <id>`, `/alias <name>
    /// "<commands>"`, `/cvar [save]`.
    pub(super) async fn handle_cvar_command(
        &mut self,
        name: &str,
        args: &str,
        view: &mut AgentView,
    ) {
        let (args, target) = match args.strip_prefix("--global") {
            Some(rest) if name == "set" && (rest.is_empty() || rest.starts_with(' ')) => {
                (rest.trim(), CvarLineTarget::Global)
            }
            _ => (args, CvarLineTarget::Session),
        };
        if name == "cvar" {
            match args {
                // An empty line changes nothing: the reply is the list.
                "" => match self.send_cvar_line("", CvarLineTarget::Session).await {
                    Ok(reply) => {
                        let rows: Vec<String> = reply
                            .values
                            .iter()
                            .map(|CvarValue { id, value }| format!("{id} = {}", value_text(value)))
                            .collect();
                        self.plain_row(&rows.join("\n"), view);
                    }
                    Err(failure) => self.error_row(&failure.to_string(), view),
                },
                "save" => {
                    let saved = self
                        .bounded_request(
                            Duration::from_millis(UI_REQUEST_TIMEOUT_MS),
                            DaemonCommand::CvarSave {
                                id: None,
                                active_session_id: self.active_session_id.clone(),
                                rest: Map::default(),
                            },
                        )
                        .await;
                    match saved {
                        Ok(_) => {
                            self.plain_row("Saved this session's cvars to its agent cfg", view);
                        }
                        Err(error) => self.error_row(&format!("{error:#}"), view),
                    }
                }
                _ => self.note_as("Usage: /cvar [save]", StatusKind::Warning, view),
            }
            return;
        }
        let usage = match name {
            "set" => "Usage: /set [--global] <id> <value>",
            "toggle" => "Usage: /toggle <id>",
            _ => "Usage: /alias <name> \"<commands>\"",
        };
        // The arguments are one command of the cvar language: `set`,
        // `toggle` or `alias` with its words.
        let parsed = parse_list(&format!("{name} {args}"));
        let Ok([command @ (Command::Set { .. } | Command::Toggle { .. } | Command::Alias { .. })]) =
            parsed.as_deref()
        else {
            self.note_as(usage, StatusKind::Warning, view);
            return;
        };
        let line = render_list(std::slice::from_ref(command));
        self.run_cvar_line(&line, target, view).await;
    }
}
