//! `eukhe budget`: read and change a budget account from the command line.
//!
//! An account is the budget a task tree spends from: a session's (named by
//! its session id), or the daemon's (`daemon`, the default), which every
//! provider request that belongs to no task spends from (the shared chat's
//! compactor, `eukhe chat`, `eukhe provider`, the tiny-model commands). A
//! session that runs in a daemon is read and changed through the daemon
//! (`get_budget`, `set_budget`, `add_budget`, `audit_budget`), so its
//! surfaces hear of the change; every other account is read and written in
//! its ledger file (`<agent dir>/budgets/`), under the ledger's lock.

use std::path::{Path, PathBuf};

use anyhow::{Context as _, Result};
use eukhe_client::daemon_client::DaemonClient;
use eukhe_core::durable::budget::{BudgetGate, DAEMON_ACCOUNT};
use eukhe_tui::budget_text::{self, BudgetTextError};
use eukhe_types::budget::{BudgetAmounts, BudgetDimension, BudgetLimits, BudgetReport};
use eukhe_types::daemon::{BudgetAudit, DaemonCommand};
use serde_json::{json, Map, Value};

use crate::config::APP_NAME;

/// What the command does to the account.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verb {
    Show,
    Set,
    Add,
    Audit,
}

/// How the answer prints.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Output {
    Text,
    Json,
}

/// The parsed `eukhe budget` invocation.
#[derive(Debug, PartialEq, Eq)]
struct BudgetCommand {
    verb: Verb,
    /// `daemon` or a session id.
    account: String,
    /// The amounts of `set` and `add` (each named dimension's).
    amounts: BudgetLimits,
    output: Output,
    /// `--daemon-socket`: the daemon a live session is looked up in.
    daemon_socket: Option<String>,
}

/// Why the `budget` arguments do not parse.
#[derive(Debug, PartialEq, Eq, thiserror::Error)]
enum BudgetUsageError {
    #[error("Missing budget command.")]
    Missing,
    #[error(
        "Unknown budget command: {subcommand}{}",
        .suggestion.as_ref().map_or_else(String::new, |s| format!(" (did you mean \"{s}\"?)"))
    )]
    Unknown {
        subcommand: String,
        suggestion: Option<String>,
    },
    #[error("unknown option: {0}")]
    UnknownOption(String),
    #[error("unexpected argument: {0}")]
    Operand(String),
    #[error("{0} requires a value")]
    MissingValue(String),
    #[error("{0} is given twice")]
    Repeated(String),
    #[error("budget {0} takes no amounts")]
    AmountsNotTaken(&'static str),
    #[error("budget {0} needs at least one of --cost, --tokens, --time, --tool-calls, --requests")]
    NoAmount(&'static str),
    #[error(transparent)]
    Amount(#[from] BudgetTextError),
}

/// The dimension an amount option names.
fn amount_option(option: &str) -> Option<BudgetDimension> {
    match option {
        "--cost" => Some(BudgetDimension::Cost),
        "--tokens" => Some(BudgetDimension::Tokens),
        "--time" => Some(BudgetDimension::Time),
        "--tool-calls" => Some(BudgetDimension::ToolCalls),
        "--requests" => Some(BudgetDimension::Requests),
        _ => None,
    }
}

/// Parse the subcommand and its options.
fn parse_budget_command(args: &[String]) -> Result<BudgetCommand, BudgetUsageError> {
    let children: Vec<&str> = crate::command_registry::get_child_command_specs(&["budget"])
        .into_iter()
        .map(|spec| spec.path[spec.path.len() - 1])
        .collect();
    let Some(subcommand) = args.first() else {
        return Err(BudgetUsageError::Missing);
    };
    let verb = match subcommand.as_str() {
        "show" => Verb::Show,
        "set" => Verb::Set,
        "add" => Verb::Add,
        "audit" => Verb::Audit,
        other => {
            return Err(BudgetUsageError::Unknown {
                subcommand: other.to_owned(),
                suggestion: eukhe_bend::rules::slash::suggestion(other, &children)
                    .map(str::to_owned),
            })
        }
    };
    let mut account: Option<String> = None;
    let mut daemon_socket: Option<String> = None;
    let mut amounts = BudgetLimits::default();
    let mut output = Output::Text;
    let mut rest = args[1..].iter();
    while let Some(arg) = rest.next() {
        let (option, inline) = match arg.split_once('=') {
            Some((option, value)) if option.starts_with("--") => (option, Some(value.to_owned())),
            _ => (arg.as_str(), None),
        };
        let mut value = || {
            inline
                .clone()
                .or_else(|| rest.next().cloned())
                .ok_or_else(|| BudgetUsageError::MissingValue(option.to_owned()))
        };
        match option {
            "--json" => output = Output::Json,
            "--account" => {
                if account.replace(value()?).is_some() {
                    return Err(BudgetUsageError::Repeated(option.to_owned()));
                }
            }
            "--daemon-socket" => daemon_socket = Some(value()?),
            _ => match amount_option(option) {
                Some(dimension) => {
                    let amount = budget_text::parse_amount(dimension, option, &value()?)?;
                    if amounts.get(dimension).is_some() {
                        return Err(BudgetUsageError::Repeated(option.to_owned()));
                    }
                    amounts = amounts.with(dimension, Some(amount));
                }
                None if option.starts_with('-') => {
                    return Err(BudgetUsageError::UnknownOption(option.to_owned()));
                }
                None => return Err(BudgetUsageError::Operand(arg.clone())),
            },
        }
    }
    match verb {
        Verb::Show | Verb::Audit if !amounts.is_unlimited() => {
            return Err(BudgetUsageError::AmountsNotTaken(verb_name(verb)));
        }
        Verb::Set | Verb::Add if amounts.is_unlimited() => {
            return Err(BudgetUsageError::NoAmount(verb_name(verb)));
        }
        Verb::Show | Verb::Audit | Verb::Set | Verb::Add => {}
    }
    Ok(BudgetCommand {
        verb,
        account: account.unwrap_or_else(|| DAEMON_ACCOUNT.to_owned()),
        amounts,
        output,
        daemon_socket,
    })
}

/// The subcommand's word.
fn verb_name(verb: Verb) -> &'static str {
    match verb {
        Verb::Show => "show",
        Verb::Set => "set",
        Verb::Add => "add",
        Verb::Audit => "audit",
    }
}

/// The amounts `add` adds: each named dimension's, the rest zero.
fn added(amounts: BudgetLimits) -> BudgetAmounts {
    BudgetDimension::ALL
        .into_iter()
        .fold(BudgetAmounts::default(), |sum, dimension| {
            sum.with(dimension, amounts.get(dimension).unwrap_or(0))
        })
}

/// What the account answered.
#[derive(Debug, Clone, PartialEq, Eq)]
#[expect(
    clippy::large_enum_variant,
    reason = "one answer per command, rendered once: boxing the report saves nothing"
)]
enum Answer {
    /// The budget after the command; `None`: the account has none.
    Report(Option<BudgetReport>),
    Audit(BudgetAudit),
}

/// Run the `budget` command; returns the process exit code.
pub fn run_budget_command(args: &[String]) -> i32 {
    let command = match parse_budget_command(args) {
        Ok(command) => command,
        Err(error) => {
            eprintln!("Error: {error}");
            eprintln!("Run \"{APP_NAME} help budget\" for usage.");
            return 2;
        }
    };
    let answer = through_daemon(&command)
        .unwrap_or_else(|| on_ledger(&command, &crate::config::get_agent_dir()));
    match answer {
        Ok(answer) => {
            println!("{}", render(&command, &answer));
            0
        }
        Err(error) => {
            eprintln!("Error: {error:#}");
            1
        }
    }
}

/// The answer of the daemon for a session's account: `None` for the
/// daemon's account, when no daemon answers on the socket, or when none of
/// its live sessions is the account's.
fn through_daemon(command: &BudgetCommand) -> Option<Result<Answer>> {
    if command.account == DAEMON_ACCOUNT {
        return None;
    }
    let socket: PathBuf =
        crate::interactive_mode::resolve_socket_path(command.daemon_socket.as_deref());
    let runtime = match tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
    {
        Ok(runtime) => runtime,
        Err(error) => return Some(Err(error.into())),
    };
    runtime.block_on(async {
        let (client, _events) =
            DaemonClient::connect_probe(&socket, crate::daemon_command::HELLO_TIMEOUT_MS)
                .await
                .ok()?;
        let listed = client
            .request_ok(DaemonCommand::List {
                id: None,
                all: Some(false),
                cwd: None,
                session_dir: None,
                include_client_owned: None,
                rest: Map::new(),
            })
            .await;
        let active = match listed {
            Ok(data) => live_address(&data, &command.account)?,
            Err(error) => return Some(Err(error)),
        };
        Some(match command.verb {
            Verb::Show => client.get_budget(&active).await.map(Answer::Report),
            Verb::Set => client
                .set_budget(&active, command.amounts)
                .await
                .map(|report| Answer::Report(Some(report))),
            Verb::Add => client
                .add_budget(&active, added(command.amounts))
                .await
                .map(|report| Answer::Report(Some(report))),
            Verb::Audit => client.audit_budget(&active).await.map(Answer::Audit),
        })
    })
}

/// The active session id of the live session whose session id is
/// `session_id`, in a `list` answer.
fn live_address(data: &Value, session_id: &str) -> Option<String> {
    data.get("sessions")?
        .as_array()?
        .iter()
        .find(|session| session.get("sessionId").and_then(Value::as_str) == Some(session_id))?
        .get("activeSessionId")?
        .as_str()
        .map(str::to_owned)
}

/// The command done on the account's ledger file under `agent_dir`.
fn on_ledger(command: &BudgetCommand, agent_dir: &Path) -> Result<Answer> {
    let gate = BudgetGate::side(agent_dir, &command.account);
    let answer = match command.verb {
        Verb::Show => gate.ledger().report(&command.account).map(Answer::Report),
        Verb::Set => gate
            .set(command.amounts)
            .map(|report| Answer::Report(Some(report))),
        Verb::Add => gate
            .add(added(command.amounts))
            .map(|report| Answer::Report(Some(report))),
        Verb::Audit => gate.audit().map(|audit| {
            Answer::Audit(BudgetAudit {
                records: audit.records,
                settled: audit.settled,
                spent: audit.spent,
                exact: audit.exact(),
                first_mismatch: audit.first_mismatch,
            })
        }),
    };
    answer.with_context(|| format!("budget account {}", command.account))
}

/// The answer as the command prints it.
fn render(command: &BudgetCommand, answer: &Answer) -> String {
    match (command.output, answer) {
        (Output::Json, Answer::Report(budget)) => {
            json!({ "account": command.account, "budget": budget }).to_string()
        }
        (Output::Json, Answer::Audit(audit)) => {
            json!({ "account": command.account, "audit": audit }).to_string()
        }
        (Output::Text, Answer::Report(Some(report))) => format!(
            "{}: {}",
            command.account,
            budget_text::report_detail(report, budget_text::now_ms(), " · ")
        ),
        (Output::Text, Answer::Report(None)) => {
            format!("{}: no budget set", command.account)
        }
        (Output::Text, Answer::Audit(audit)) => {
            format!("{}: {}", command.account, budget_text::audit_line(audit))
        }
    }
}

#[cfg(test)]
mod tests;
