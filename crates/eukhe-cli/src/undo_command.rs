//! `eukhe undo [<session>]` and `eukhe diff [<session>] [--all]`: a live
//! session's workspace snapshots through the daemon (`undo_turn`,
//! `get_turn_diff`). Without `<session>`, the one live session whose
//! working directory is the current one.

use std::path::PathBuf;

use anyhow::{bail, Context as _, Result};
use eukhe_client::daemon_client::DaemonClient;
use eukhe_types::daemon::DaemonCommand;
use eukhe_types::undo::{diff_text, undo_text, DiffScope, TurnDiffReply, UndoReply};
use serde_json::{Map, Value};

use crate::config::APP_NAME;

/// The command the user typed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Which {
    Undo,
    Diff,
}

/// What the command does.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verb {
    Undo,
    Diff(DiffScope),
}

/// How the answer prints.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Output {
    Text,
    Json,
}

/// The parsed invocation.
#[derive(Debug, Clone, PartialEq, Eq)]
struct UndoCommand {
    verb: Verb,
    /// The session id; `None`: the live session of the current directory.
    session: Option<String>,
    output: Output,
    daemon_socket: Option<String>,
}

fn parse(which: Which, args: &[String]) -> Result<UndoCommand, String> {
    let mut command = UndoCommand {
        verb: match which {
            Which::Undo => Verb::Undo,
            Which::Diff => Verb::Diff(DiffScope::Turn),
        },
        session: None,
        output: Output::Text,
        daemon_socket: None,
    };
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match (arg.as_str(), command.verb) {
            ("--all", Verb::Diff(_)) => command.verb = Verb::Diff(DiffScope::All),
            ("--json", _) => command.output = Output::Json,
            ("--daemon-socket", _) => {
                command.daemon_socket =
                    Some(args.next().ok_or("--daemon-socket needs a path")?.clone());
            }
            (flag, _) if flag.starts_with('-') => return Err(format!("Unknown option: {flag}")),
            (session, _) if command.session.is_none() => command.session = Some(session.to_owned()),
            (extra, _) => return Err(format!("Unexpected argument: {extra}")),
        }
    }
    Ok(command)
}

/// Run `eukhe undo` or `eukhe diff`; the process exit code.
pub(crate) fn run_undo_command(which: Which, args: &[String]) -> i32 {
    let name = match which {
        Which::Undo => "undo",
        Which::Diff => "diff",
    };
    let command = match parse(which, args) {
        Ok(command) => command,
        Err(error) => {
            eprintln!("Error: {error}");
            eprintln!("Run \"{APP_NAME} help {name}\" for usage.");
            return 2;
        }
    };
    match run(&command) {
        Ok(text) => {
            print!("{text}");
            0
        }
        Err(error) => {
            eprintln!("Error: {error:#}");
            1
        }
    }
}

fn run(command: &UndoCommand) -> Result<String> {
    let socket: PathBuf =
        crate::interactive_mode::resolve_socket_path(command.daemon_socket.as_deref());
    let cwd = std::env::current_dir().context("the working directory does not read")?;
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()?;
    runtime.block_on(async {
        let (client, _events) =
            DaemonClient::connect_probe(&socket, crate::daemon_command::HELLO_TIMEOUT_MS)
                .await
                .context("no daemon answers: no session is live")?;
        let listed = client
            .request_ok(DaemonCommand::List {
                id: None,
                all: Some(false),
                cwd: None,
                session_dir: None,
                include_client_owned: None,
                rest: Map::new(),
            })
            .await?;
        let active = live_session(&listed, command.session.as_deref(), &cwd.to_string_lossy())?;
        match command.verb {
            Verb::Undo => Ok(render_undo(
                &client.undo_turn(&active).await?,
                command.output,
            )),
            Verb::Diff(scope) => Ok(render_diff(
                &client.get_turn_diff(&active, scope).await?,
                command.output,
            )),
        }
    })
}

/// The active session id of the live session `session`, or, without
/// one, of the one live session in `cwd`.
fn live_session(listed: &Value, session: Option<&str>, cwd: &str) -> Result<String> {
    let sessions = listed
        .get("sessions")
        .and_then(Value::as_array)
        .map(Vec::as_slice)
        .unwrap_or_default();
    let field = |row: &Value, key: &str| row.get(key).and_then(Value::as_str).map(str::to_owned);
    let live: Vec<(String, String)> = sessions
        .iter()
        .filter(|row| match session {
            Some(id) => field(row, "sessionId").as_deref() == Some(id),
            None => field(row, "cwd").as_deref() == Some(cwd),
        })
        .filter_map(|row| Some((field(row, "sessionId")?, field(row, "activeSessionId")?)))
        .collect();
    match (live.as_slice(), session) {
        ([(_, active)], _) => Ok(active.clone()),
        ([], Some(id)) => bail!("No live session {id}"),
        ([], None) => bail!("No live session in {cwd}: name one"),
        (many, Some(_) | None) => bail!(
            "{} live sessions in {cwd}: name one of {}",
            many.len(),
            many.iter()
                .map(|(id, _)| id.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

fn render_undo(reply: &UndoReply, output: Output) -> String {
    match output {
        Output::Json => format!(
            "{}\n",
            serde_json::to_string_pretty(reply).unwrap_or_default()
        ),
        Output::Text => undo_text(reply),
    }
}

fn render_diff(reply: &TurnDiffReply, output: Output) -> String {
    match output {
        Output::Json => format!(
            "{}\n",
            serde_json::to_string_pretty(reply).unwrap_or_default()
        ),
        Output::Text => diff_text(reply),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn args(words: &[&str]) -> Vec<String> {
        words.iter().map(|word| (*word).to_owned()).collect()
    }

    #[test]
    fn arguments_parse() {
        assert_eq!(
            (
                parse(Which::Diff, &args(&["s1", "--all"])),
                parse(Which::Undo, &args(&[])).map(|command| command.verb),
                parse(Which::Undo, &args(&["--all"])),
                parse(Which::Diff, &args(&["a", "b"])),
            ),
            (
                Ok(UndoCommand {
                    verb: Verb::Diff(DiffScope::All),
                    session: Some("s1".to_owned()),
                    output: Output::Text,
                    daemon_socket: None,
                }),
                Ok(Verb::Undo),
                Err("Unknown option: --all".to_owned()),
                Err("Unexpected argument: b".to_owned()),
            )
        );
    }

    #[test]
    fn the_session_is_named_or_the_one_in_the_directory() {
        let listed = json!({ "sessions": [
            { "sessionId": "a", "activeSessionId": "act-a", "cwd": "/w" },
            { "sessionId": "b", "activeSessionId": "act-b", "cwd": "/v" },
            { "sessionId": "c", "activeSessionId": "act-c", "cwd": "/v" },
        ]});
        let outcome = |session, cwd| live_session(&listed, session, cwd).map_err(|e| e.to_string());
        assert_eq!(
            (
                outcome(Some("b"), "/w"),
                outcome(None, "/w"),
                outcome(None, "/x"),
                outcome(None, "/v"),
            ),
            (
                Ok("act-b".to_owned()),
                Ok("act-a".to_owned()),
                Err("No live session in /x: name one".to_owned()),
                Err("2 live sessions in /v: name one of b, c".to_owned()),
            )
        );
    }
}
