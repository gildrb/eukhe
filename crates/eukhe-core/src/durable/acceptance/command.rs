//! `/accept`: the owner's view and change of a conversation's acceptance
//! checks from any surface that sends text (the TUI, print and rpc mode,
//! the daemon's prompt path).
//!
//! ```text
//! /accept                    the checks, their verdicts, the label
//! /accept cmd [--expect <code>] [--timeout <seconds>] [--protect <path>]... <command>
//! /accept judge [--model <provider/id>] <condition>
//! /accept until [--timeout <seconds>] <command>
//! /accept intent [on|off]    the intent judge: the user's messages, judged on the final state
//! /accept returns <n>        the most returns in a row to the worker
//! /accept clear              drop every check
//! ```
//!
//! A check is added to the current ones; the first check brings the
//! intent judge with it (`/accept intent off` drops it). Any change starts
//! a new revision, so every check has to pass again.

use eukhe_types::acceptance::{AcceptanceState, CheckSpec};

use super::verifier::describe;

/// What `/accept` asks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum AcceptCommand {
    /// Show the acceptance.
    Status,
    /// Add this check to the current ones.
    Add(CheckSpec),
    /// Set the most returns in a row.
    Returns(u64),
    /// Add (`true`) or drop the intent check.
    Intent(bool),
    /// Drop every check.
    Clear,
}

/// The usage text of `/accept`.
pub(crate) const ACCEPT_USAGE: &str = "Usage: /accept [status|clear] | /accept cmd [--expect <code>] [--timeout <seconds>] [--protect <path>]... <command> | /accept judge [--model <provider/id>] <condition> | /accept until [--timeout <seconds>] <command> | /accept intent [on|off] | /accept returns <n>";

/// `text` split at its first run of whitespace: the first word and the
/// rest, trimmed.
fn word(text: &str) -> (&str, &str) {
    let text = text.trim_start();
    match text.find(char::is_whitespace) {
        Some(end) => (&text[..end], text[end..].trim_start()),
        None => (text, ""),
    }
}

/// The leading `--flag value` options of `text` among `flags`, then the
/// rest; `None` when a flag has no value or is unknown.
fn options<'a>(mut text: &'a str, flags: &[&str]) -> Option<(Vec<(&'a str, &'a str)>, &'a str)> {
    let mut found = Vec::new();
    loop {
        let (flag, rest) = word(text);
        if !flag.starts_with("--") {
            return Some((found, text.trim()));
        }
        if !flags.contains(&flag) {
            return None;
        }
        let (value, rest) = word(rest);
        if value.is_empty() {
            return None;
        }
        found.push((flag, value));
        text = rest;
    }
}

/// The time limit a `--timeout <seconds>` asks, in milliseconds.
fn timeout_ms(seconds: &str) -> Option<u64> {
    seconds.parse::<u64>().ok()?.checked_mul(1000)
}

/// Parse the arguments of `/accept`; `None` asks for the usage.
pub(crate) fn parse_accept_command(args: &str) -> Option<AcceptCommand> {
    let (verb, rest) = word(args);
    match verb {
        "" | "status" if rest.is_empty() => Some(AcceptCommand::Status),
        "clear" if rest.is_empty() => Some(AcceptCommand::Clear),
        "returns" => rest.parse().ok().map(AcceptCommand::Returns),
        "intent" => match rest {
            "" | "on" => Some(AcceptCommand::Intent(true)),
            "off" => Some(AcceptCommand::Intent(false)),
            _ => None,
        },
        "cmd" => {
            let (found, command) = options(rest, &["--expect", "--timeout", "--protect"])?;
            if command.is_empty() {
                return None;
            }
            let mut expect = 0;
            let mut timeout = None;
            let mut protect = Vec::new();
            for (flag, value) in found {
                match flag {
                    "--expect" => expect = value.parse().ok()?,
                    "--timeout" => timeout = Some(timeout_ms(value)?),
                    // `options` admits only the three flags: this is `--protect`.
                    _ => protect.push(value.to_owned()),
                }
            }
            Some(AcceptCommand::Add(CheckSpec::Command {
                command: command.to_owned(),
                expect,
                timeout_ms: timeout,
                protect,
            }))
        }
        "judge" => {
            let (found, condition) = options(rest, &["--model"])?;
            if condition.is_empty() {
                return None;
            }
            Some(AcceptCommand::Add(CheckSpec::Judge {
                condition: condition.to_owned(),
                evidence: Vec::new(),
                model: found.last().map(|(_, model)| (*model).to_owned()),
            }))
        }
        "until" => {
            let (found, command) = options(rest, &["--timeout"])?;
            if command.is_empty() {
                return None;
            }
            let timeout = match found.last() {
                Some((_, seconds)) => Some(timeout_ms(seconds)?),
                None => None,
            };
            Some(AcceptCommand::Add(CheckSpec::Until {
                command: command.to_owned(),
                timeout_ms: timeout,
            }))
        }
        _ => None,
    }
}

/// The acceptance as text: the label, then each check with its last
/// verdict.
#[must_use]
pub fn format_acceptance_status(state: &AcceptanceState) -> String {
    if state.checks.is_empty() {
        return "Acceptance: unverified (no acceptance checks).".to_owned();
    }
    let mut lines = vec![format!(
        "Acceptance: {} (revision {}, returns {} of {}{}).",
        state.label.slug(),
        state.revision,
        state.tries,
        state.max_returns,
        if state.claimed {
            ", a claim waits for its verdict"
        } else {
            ""
        }
    )];
    for (index, check) in state.checks.iter().enumerate() {
        let verdict = match &check.result {
            None => "not judged".to_owned(),
            Some(result) if result.at == state.state => {
                format!("{}: {}", result.verdict.slug(), result.summary)
            }
            Some(result) => format!(
                "stale ({} on an earlier state: {})",
                result.verdict.slug(),
                result.summary
            ),
        };
        lines.push(format!(
            "{}. {}: {verdict}",
            index + 1,
            describe(&check.spec)
        ));
    }
    lines.join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn accept_arguments_parse_to_checks() {
        assert_eq!(
            [
                parse_accept_command(""),
                parse_accept_command(" status "),
                parse_accept_command("clear"),
                parse_accept_command("returns 5"),
                parse_accept_command("cmd cargo test --workspace"),
                parse_accept_command(
                    "cmd --expect 3 --timeout 90 --protect tests/a.py --protect run.sh ./run.sh  --fast"
                ),
                parse_accept_command("judge --model anthropic/claude-haiku-5-5 the README names the flag"),
                parse_accept_command("until --timeout 5 test -f done.txt"),
                parse_accept_command("intent"),
                parse_accept_command("intent off"),
            ],
            [
                Some(AcceptCommand::Status),
                Some(AcceptCommand::Status),
                Some(AcceptCommand::Clear),
                Some(AcceptCommand::Returns(5)),
                Some(AcceptCommand::Add(CheckSpec::Command {
                    command: "cargo test --workspace".to_owned(),
                    expect: 0,
                    timeout_ms: None,
                    protect: Vec::new(),
                })),
                Some(AcceptCommand::Add(CheckSpec::Command {
                    command: "./run.sh  --fast".to_owned(),
                    expect: 3,
                    timeout_ms: Some(90_000),
                    protect: vec!["tests/a.py".to_owned(), "run.sh".to_owned()],
                })),
                Some(AcceptCommand::Add(CheckSpec::Judge {
                    condition: "the README names the flag".to_owned(),
                    evidence: Vec::new(),
                    model: Some("anthropic/claude-haiku-5-5".to_owned()),
                })),
                Some(AcceptCommand::Add(CheckSpec::Until {
                    command: "test -f done.txt".to_owned(),
                    timeout_ms: Some(5000),
                })),
                Some(AcceptCommand::Intent(true)),
                Some(AcceptCommand::Intent(false)),
            ]
        );
    }

    #[test]
    fn accept_arguments_that_name_no_check_ask_for_the_usage() {
        for args in [
            "cmd",
            "cmd --expect",
            "cmd --expect x true",
            "cmd --retries 2 true",
            "judge",
            "until",
            "returns",
            "returns many",
            "status now",
            "intent maybe",
            "verify",
        ] {
            assert_eq!(parse_accept_command(args), None, "{args}");
        }
    }
}
