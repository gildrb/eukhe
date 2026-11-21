//! `/accept`: the owner's view and change of a conversation's acceptance
//! checks from any surface that sends text (the TUI, print and rpc mode,
//! the daemon's prompt path).
//!
//! ```text
//! /accept                    the checks, their verdicts, their strength, the label
//! /accept cmd [--expect <code>] [--timeout <seconds>] [--protect <path>]... [--strength <percent>] <command>
//! /accept judge [--model <provider/id>] <condition>
//! /accept until [--timeout <seconds>] [--strength <percent>] <command>
//! /accept bend [--strength <percent>] [<entry>]   `bend <entry>` (PROOF.bend), its laws protected
//! /accept intent [on|off]    the intent judge: the user's messages, judged on the final state
//! /accept returns <n>        the most returns in a row to the worker
//! /accept clear              drop every check
//! ```
//!
//! A check is added to the current ones; the first check brings the
//! intent judge with it (`/accept intent off` drops it). Any change starts
//! a new revision, so every check has to pass again. `--strength` is the
//! share of deliberate breaks of the changed code the check must catch
//! before it certifies done (default 80; 0 waives it).

use std::path::Path;

use eukhe_durable::session::SessionResult;
use eukhe_types::acceptance::{AcceptanceState, CheckSpec};

use super::verifier::{describe, judges_only, strength_text};

/// What `/accept` asks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum AcceptCommand {
    /// Show the acceptance.
    Status,
    /// Add this check to the current ones.
    Add(CheckSpec),
    /// Add the check of a Bend project: `bend <entry>`, its law files
    /// protected (resolved in the workspace by [`bend_check`]).
    Bend {
        entry: String,
        strength: Option<u32>,
    },
    /// Set the most returns in a row.
    Returns(u64),
    /// Add (`true`) or drop the intent check.
    Intent(bool),
    /// Drop every check.
    Clear,
}

/// The usage text of `/accept`.
pub(crate) const ACCEPT_USAGE: &str = "Usage: /accept [status|clear] | /accept cmd [--expect <code>] [--timeout <seconds>] [--protect <path>]... [--strength <percent>] <command> | /accept judge [--model <provider/id>] <condition> | /accept until [--timeout <seconds>] [--strength <percent>] <command> | /accept bend [--strength <percent>] [<entry>] | /accept intent [on|off] | /accept returns <n>";

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

/// The share a `--strength <percent>` asks: 0 to 100.
fn strength(percent: &str) -> Option<u32> {
    percent.parse::<u32>().ok().filter(|pct| *pct <= 100)
}

/// The default entry of `/accept bend`.
const BEND_ENTRY: &str = "PROOF.bend";

/// The check of the Bend project at `cwd` whose proofs `entry` checks:
/// `bend <entry>`, with the law index (`LAWS.bend`), the lock
/// (`LAWS.lock`) and every `.bend` file that holds a `law` block
/// protected, so the worker can neither weaken a law nor its lock.
///
/// # Errors
///
/// The entry does not exist, or no `.bend` file holds a law.
pub(crate) fn bend_check(
    cwd: &Path,
    entry: &str,
    strength: Option<u32>,
) -> Result<CheckSpec, String> {
    if !cwd.join(entry).is_file() {
        return Err(format!(
            "/accept bend: {entry} does not exist in {}",
            cwd.display()
        ));
    }
    let mut protect: Vec<String> = ["LAWS.bend", "LAWS.lock"]
        .into_iter()
        .filter(|file| cwd.join(file).is_file())
        .map(str::to_owned)
        .collect();
    let mut laws = law_files(cwd, cwd);
    laws.sort();
    laws.retain(|file| !protect.contains(file));
    protect.extend(laws);
    if !protect
        .iter()
        .any(|file| Path::new(file).extension().is_some_and(|ext| ext == "bend"))
    {
        return Err("/accept bend: no .bend file holds a `law` block".to_owned());
    }
    Ok(CheckSpec::Command {
        command: format!("bend {entry}"),
        expect: 0,
        timeout_ms: None,
        protect,
        strength,
    })
}

/// The `.bend` files under `dir` (relative to `root`) that hold a `law`
/// block; build output, dependency stores and hidden directories skipped.
fn law_files(root: &Path, dir: &Path) -> Vec<String> {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return Vec::new();
    };
    let mut found = Vec::new();
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name();
        let name = name.to_string_lossy();
        let Ok(kind) = entry.file_type() else {
            continue;
        };
        if kind.is_dir() {
            if !name.starts_with('.') && name != "target" && name != "node_modules" {
                found.extend(law_files(root, &path));
            }
        } else if kind.is_file()
            && name.ends_with(".bend")
            && std::fs::read_to_string(&path)
                .is_ok_and(|text| text.lines().any(|line| line.starts_with("law ")))
        {
            if let Ok(relative) = path.strip_prefix(root) {
                found.push(relative.to_string_lossy().replace('\\', "/"));
            }
        }
    }
    found
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
            let (found, command) =
                options(rest, &["--expect", "--timeout", "--protect", "--strength"])?;
            if command.is_empty() {
                return None;
            }
            let mut expect = 0;
            let mut timeout = None;
            let mut protect = Vec::new();
            let mut bar = None;
            for (flag, value) in found {
                match flag {
                    "--expect" => expect = value.parse().ok()?,
                    "--timeout" => timeout = Some(timeout_ms(value)?),
                    "--strength" => bar = Some(strength(value)?),
                    // `options` admits only the four flags: this is `--protect`.
                    _ => protect.push(value.to_owned()),
                }
            }
            Some(AcceptCommand::Add(CheckSpec::Command {
                command: command.to_owned(),
                expect,
                timeout_ms: timeout,
                protect,
                strength: bar,
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
            let (found, command) = options(rest, &["--timeout", "--strength"])?;
            if command.is_empty() {
                return None;
            }
            let mut timeout = None;
            let mut bar = None;
            for (flag, value) in found {
                match flag {
                    "--timeout" => timeout = Some(timeout_ms(value)?),
                    // `options` admits only the two flags: this is `--strength`.
                    _ => bar = Some(strength(value)?),
                }
            }
            Some(AcceptCommand::Add(CheckSpec::Until {
                command: command.to_owned(),
                timeout_ms: timeout,
                strength: bar,
            }))
        }
        "bend" => {
            let (found, entry) = options(rest, &["--strength"])?;
            if entry.split_whitespace().nth(1).is_some() {
                return None;
            }
            let bar = match found.last() {
                Some((_, value)) => Some(strength(value)?),
                None => None,
            };
            Some(AcceptCommand::Bend {
                entry: if entry.is_empty() {
                    BEND_ENTRY.to_owned()
                } else {
                    entry.to_owned()
                },
                strength: bar,
            })
        }
        _ => None,
    }
}

/// The acceptance as text: the label, then each check with its last
/// verdict and, for a check with code to break, its strength.
///
/// # Errors
///
/// A compiled-core failure.
pub fn format_acceptance_status(state: &AcceptanceState) -> SessionResult<String> {
    if state.checks.is_empty() {
        return Ok("Acceptance: unverified (no acceptance checks).".to_owned());
    }
    let mut lines = vec![format!(
        "Acceptance: {} (revision {}, returns {} of {}{}).",
        state.label.text(),
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
        let strength = match strength_text(check, state.state)? {
            Some(text) => format!("; strength: {text}"),
            None => String::new(),
        };
        lines.push(format!(
            "{}. {}: {verdict}{strength}",
            index + 1,
            describe(&check.spec)
        ));
    }
    Ok(lines.join("\n"))
}

/// The end line of a headless run whose checks all passed while done is
/// not certified (exit 3): the work is done, and why it is not certified
/// (`done; not certified: only the intent check ran`).
#[must_use]
pub fn uncertified_line(state: &AcceptanceState) -> String {
    format!(
        "done; not certified: {}",
        judges_only(&state.checks).unwrap_or("the checks were not shown to catch broken code")
    )
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
                parse_accept_command("cmd --strength 90 pytest -q"),
                parse_accept_command("until --strength 0 test -f done.txt"),
                parse_accept_command("bend"),
                parse_accept_command("bend --strength 95 site/PROOF.bend"),
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
                    strength: None,
                })),
                Some(AcceptCommand::Add(CheckSpec::Command {
                    command: "./run.sh  --fast".to_owned(),
                    expect: 3,
                    timeout_ms: Some(90_000),
                    protect: vec!["tests/a.py".to_owned(), "run.sh".to_owned()],
                    strength: None,
                })),
                Some(AcceptCommand::Add(CheckSpec::Judge {
                    condition: "the README names the flag".to_owned(),
                    evidence: Vec::new(),
                    model: Some("anthropic/claude-haiku-5-5".to_owned()),
                })),
                Some(AcceptCommand::Add(CheckSpec::Until {
                    command: "test -f done.txt".to_owned(),
                    timeout_ms: Some(5000),
                    strength: None,
                })),
                Some(AcceptCommand::Add(CheckSpec::Command {
                    command: "pytest -q".to_owned(),
                    expect: 0,
                    timeout_ms: None,
                    protect: Vec::new(),
                    strength: Some(90),
                })),
                Some(AcceptCommand::Add(CheckSpec::Until {
                    command: "test -f done.txt".to_owned(),
                    timeout_ms: None,
                    strength: Some(0),
                })),
                Some(AcceptCommand::Bend {
                    entry: "PROOF.bend".to_owned(),
                    strength: None,
                }),
                Some(AcceptCommand::Bend {
                    entry: "site/PROOF.bend".to_owned(),
                    strength: Some(95),
                }),
                Some(AcceptCommand::Intent(true)),
                Some(AcceptCommand::Intent(false)),
            ]
        );
    }

    #[test]
    fn the_bend_check_runs_the_proofs_and_protects_every_law_and_the_lock() {
        let dir = tempfile::tempdir().expect("dir");
        let root = dir.path();
        for (path, text) in [
            ("PROOF.bend", "import ./LAWS.bend as L\n"),
            ("LAWS.bend", "import ./laws/a.bend as A\n"),
            ("LAWS.lock", "{}\n"),
            (
                "laws/a.bend",
                "# the law\nlaw a_holds:\n  {1n == 1n : Nat}\n",
            ),
            ("bend/a.bend", "def a() -> Nat:\n  1n\n"),
        ] {
            std::fs::create_dir_all(root.join(path).parent().expect("parent")).expect("dir");
            std::fs::write(root.join(path), text).expect("write");
        }
        assert_eq!(
            bend_check(root, "PROOF.bend", Some(90)),
            Ok(CheckSpec::Command {
                command: "bend PROOF.bend".to_owned(),
                expect: 0,
                timeout_ms: None,
                protect: vec![
                    "LAWS.bend".to_owned(),
                    "LAWS.lock".to_owned(),
                    "laws/a.bend".to_owned()
                ],
                strength: Some(90),
            })
        );
        assert!(bend_check(root, "MISSING.bend", None).is_err());
        std::fs::remove_file(root.join("laws/a.bend")).expect("remove");
        std::fs::remove_file(root.join("LAWS.bend")).expect("remove");
        assert_eq!(
            bend_check(root, "PROOF.bend", None),
            Err("/accept bend: no .bend file holds a `law` block".to_owned())
        );
    }

    #[test]
    fn accept_arguments_that_name_no_check_ask_for_the_usage() {
        for args in [
            "cmd",
            "cmd --expect",
            "cmd --expect x true",
            "cmd --retries 2 true",
            "cmd --strength 101 true",
            "until --strength x true",
            "bend two entries",
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
