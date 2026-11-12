//! `/loop` arguments and the lines a loop reports: `/loop [count|duration]
//! [--while|--until '<command>'] [prompt]`, plus two spellings that are not
//! flags of a loop: `/loop --stop` (end the loop, never start one) and
//! `/loop --status`.

use eukhe_bend::wire::NAT_MAX;
use eukhe_types::loop_mode::{LoopCondition, LoopEnd, LoopEvidence, LoopLimit, LoopPhase};

use super::docs::LoopDoc;

/// The usage line every malformed-arguments message ends with.
const LOOP_USAGE: &str = "Usage: /loop [count|duration] [--while|--until '<command>'] [prompt]. Examples: /loop 10, /loop 10m, /loop 20 --until 'bun test' fix the failing tests.";

/// The largest integer a limit may be (2^53 - 1, exact in any client's
/// double-precision number).
const MAX_SAFE_INTEGER: u64 = 9_007_199_254_740_991;

/// How long one run of the condition command may take.
pub(crate) const CONDITION_TIMEOUT_MS: u64 = 30_000;

/// How many chars of a command or of its output a status line quotes.
const PREVIEW_CHARS: usize = 60;

/// A parsed `/loop` command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum LoopCommand {
    /// `/loop --stop`.
    Stop,
    /// `/loop --status`.
    Status,
    /// `/loop [count|duration] [--while|--until '<command>'] [prompt]`.
    Enter {
        limit: Option<LoopLimit>,
        condition: Option<LoopCondition>,
        prompt: Option<String>,
    },
}

/// Parse the arguments of `/loop`.
///
/// # Errors
///
/// The malformed-arguments message for the malformed part: a limit-shaped
/// token that is no limit, an unknown flag, a flag without a command, an
/// unterminated quote, both polarities.
pub(crate) fn parse_loop_command(args: &str) -> Result<LoopCommand, String> {
    let trimmed = args.trim();
    match trimmed {
        "--stop" => return Ok(LoopCommand::Stop),
        "--status" => return Ok(LoopCommand::Status),
        _ => {}
    }
    if trimmed.is_empty() {
        return Ok(LoopCommand::Enter {
            limit: None,
            condition: None,
            prompt: None,
        });
    }
    let (limit, rest) = take_limit(trimmed)?;
    let (condition, rest) = take_condition(&rest)?;
    Ok(LoopCommand::Enter {
        limit,
        condition,
        prompt: (!rest.is_empty()).then_some(rest),
    })
}

fn unit_ms(unit: &str) -> Option<u64> {
    match unit {
        "s" | "sec" | "secs" | "second" | "seconds" => Some(1_000),
        "m" | "min" | "mins" | "minute" | "minutes" => Some(60_000),
        "h" | "hr" | "hrs" | "hour" | "hours" => Some(3_600_000),
        _ => None,
    }
}

/// A positive amount JavaScript holds exactly and the wire can carry.
fn amount(digits: &str) -> Option<u64> {
    digits
        .parse::<u64>()
        .ok()
        .filter(|n| *n > 0 && *n <= MAX_SAFE_INTEGER && *n <= NAT_MAX)
}

fn iterations(digits: &str) -> Result<LoopLimit, String> {
    amount(digits)
        .map(|iterations| LoopLimit::Iterations { iterations })
        .ok_or_else(|| "Loop count must be a positive integer.".to_owned())
}

fn duration(digits: &str, unit: u64) -> Result<u64, String> {
    amount(digits)
        .and_then(|n| n.checked_mul(unit))
        .filter(|ms| *ms <= NAT_MAX)
        .ok_or_else(|| "Loop duration must be positive.".to_owned())
}

/// A compact duration (`10m`, `1h30m`); `None` when the token is not
/// duration-shaped.
fn compound_duration(token: &str) -> Option<Result<LoopLimit, String>> {
    let mut segments = Vec::new();
    let mut rest = token;
    while !rest.is_empty() {
        let digits = rest.len() - rest.trim_start_matches(|c: char| c.is_ascii_digit()).len();
        let after = &rest[digits..];
        let letters = after.len()
            - after
                .trim_start_matches(|c: char| c.is_ascii_lowercase())
                .len();
        if digits == 0 || letters == 0 {
            return None;
        }
        segments.push((&rest[..digits], &after[..letters]));
        rest = &after[letters..];
    }
    if segments.is_empty() {
        return None;
    }
    let mut total: u64 = 0;
    for (digits, unit) in segments {
        let Some(unit) = unit_ms(unit) else {
            return Some(Err(
                "Loop duration unit must be seconds, minutes, or hours.".to_owned(),
            ));
        };
        let ms = match duration(digits, unit) {
            Ok(ms) => ms,
            Err(error) => return Some(Err(error)),
        };
        total = match total.checked_add(ms).filter(|sum| *sum <= NAT_MAX) {
            Some(sum) => sum,
            None => return Some(Err("Loop duration must be positive.".to_owned())),
        };
    }
    Some(Ok(LoopLimit::Duration { duration_ms: total }))
}

/// Split an optional leading limit token off `input`.
fn take_limit(input: &str) -> Result<(Option<LoopLimit>, String), String> {
    let (first, rest) = match input.find(char::is_whitespace) {
        Some(at) => {
            let space = input[at..].chars().next().map_or(1, char::len_utf8);
            (&input[..at], input[at + space..].trim())
        }
        None => (input, ""),
    };
    let token = first.to_lowercase();
    let mut chars = token.chars();
    let limit_shaped = match chars.next() {
        Some('+' | '-') => chars.next().is_some_and(|c| c.is_ascii_digit()),
        Some(c) => c.is_ascii_digit(),
        None => false,
    };
    if !limit_shaped {
        return Ok((None, input.to_owned()));
    }
    if token.chars().all(|c| c.is_ascii_digit()) {
        let unit_token = rest.split(char::is_whitespace).next().unwrap_or("");
        if let Some(unit) = unit_ms(&unit_token.to_lowercase()) {
            let duration_ms = duration(&token, unit)?;
            return Ok((
                Some(LoopLimit::Duration { duration_ms }),
                rest[unit_token.len()..].trim().to_owned(),
            ));
        }
        return Ok((Some(iterations(&token)?), rest.to_owned()));
    }
    match compound_duration(&token) {
        Some(limit) => Ok((Some(limit?), rest.to_owned())),
        None => Err(LOOP_USAGE.to_owned()),
    }
}

fn is_shell_space(c: char) -> bool {
    matches!(c, ' ' | '\t' | '\n' | '\r')
}

/// One shell word from the start of `text`: quoted and unquoted runs
/// concatenate; no escapes in single quotes; `\"`, `\\`, `\$`, `` \` `` in
/// double quotes; a backslash escapes the next char
/// unquoted; the word ends at unquoted whitespace. `Ok(None)`: no word.
///
/// # Errors
///
/// An unclosed quote.
fn read_shell_word(text: &str) -> Result<Option<(String, String)>, ()> {
    let text = text.trim_start_matches(is_shell_space);
    if text.is_empty() {
        return Ok(None);
    }
    let mut value = String::new();
    let mut single = false;
    let mut double = false;
    let mut chars = text.char_indices().peekable();
    let mut end = text.len();
    while let Some((at, c)) = chars.next() {
        if single {
            if c == '\'' {
                single = false;
            } else {
                value.push(c);
            }
            continue;
        }
        if double {
            if c == '\\' {
                if let Some((_, next)) = chars.peek().copied() {
                    if matches!(next, '"' | '\\' | '$' | '`') {
                        value.push(next);
                        chars.next();
                        continue;
                    }
                }
            }
            if c == '"' {
                double = false;
            } else {
                value.push(c);
            }
            continue;
        }
        match c {
            '\'' => single = true,
            '"' => double = true,
            '\\' => match chars.next() {
                Some((_, next)) => value.push(next),
                None => value.push(c),
            },
            c if is_shell_space(c) => {
                end = at;
                break;
            }
            c => value.push(c),
        }
    }
    if single || double {
        return Err(());
    }
    Ok(Some((value, text[end..].trim().to_owned())))
}

/// The flag name at the start of `rest`: `--` then a lowercase letter then
/// lowercase letters or dashes, followed by whitespace, `=`, or the end.
fn flag_name(rest: &str) -> Option<&str> {
    let body = rest.strip_prefix("--")?;
    if !body.starts_with(|c: char| c.is_ascii_lowercase()) {
        return None;
    }
    let len = body.len()
        - body
            .trim_start_matches(|c: char| c.is_ascii_lowercase() || c == '-')
            .len();
    let name = &rest[..2 + len];
    match rest[2 + len..].chars().next() {
        None => Some(name),
        Some(c) if c == '=' || c.is_whitespace() => Some(name),
        Some(_) => None,
    }
}

/// Split an optional leading `--while` / `--until` flag off `input`.
fn take_condition(input: &str) -> Result<(Option<LoopCondition>, String), String> {
    let mut rest = input.trim().to_owned();
    let mut condition: Option<LoopCondition> = None;
    while rest.starts_with("--") {
        let name = flag_name(&rest);
        let until = match name {
            Some("--until") => true,
            Some("--while") => false,
            Some(_) | None => {
                let shown = name.unwrap_or_else(|| rest.split_whitespace().next().unwrap_or(""));
                return Err(format!("Unknown /loop flag {shown}. {LOOP_USAGE}"));
            }
        };
        let name = if until { "--until" } else { "--while" };
        if condition.is_some() {
            return Err("Use only one of --while or --until.".to_owned());
        }
        let after = &rest[name.len()..];
        let value_text = after.strip_prefix('=').unwrap_or(after);
        let needs = || {
            format!(
                "{name} needs a shell command. Quote it when it contains spaces: /loop {name} 'bun test'."
            )
        };
        let Some((value, left)) = read_shell_word(value_text)
            .map_err(|()| format!("{name} has an unterminated quote."))?
        else {
            return Err(needs());
        };
        if value.trim().is_empty() || value_text.trim().starts_with('-') {
            return Err(needs());
        }
        condition = Some(LoopCondition {
            command: value.trim().to_owned(),
            until,
        });
        rest = left;
    }
    Ok((condition, rest))
}

/// `n` of a unit, spelled out.
fn budget(duration_ms: u64) -> String {
    let spell = |n: u64, unit: &str| format!("{n} {unit}{}", if n == 1 { "" } else { "s" });
    if duration_ms.is_multiple_of(3_600_000) {
        spell(duration_ms / 3_600_000, "hour")
    } else if duration_ms.is_multiple_of(60_000) {
        spell(duration_ms / 60_000, "minute")
    } else if duration_ms.is_multiple_of(1_000) {
        spell(duration_ms / 1_000, "second")
    } else {
        // The parser takes no unit finer than a second; this arm still
        // spells any other span exactly.
        format!("{duration_ms} ms")
    }
}

fn iterations_word(n: u64) -> &'static str {
    if n == 1 {
        "iteration"
    } else {
        "iterations"
    }
}

/// The command quoted for a status line: one line, bounded.
fn quote_command(command: &str) -> String {
    format!("`{}`", preview(command))
}

/// The first line of `text` with content, control chars dropped, bounded.
pub(crate) fn preview(text: &str) -> String {
    let line = text
        .lines()
        .map(str::trim)
        .find(|line| !line.is_empty())
        .unwrap_or("");
    let clean: String = line.chars().filter(|c| !c.is_control()).collect();
    if clean.chars().count() > PREVIEW_CHARS {
        let mut cut: String = clean.chars().take(PREVIEW_CHARS - 1).collect();
        cut.push('…');
        cut
    } else {
        clean
    }
}

/// The condition as a status line reads it: `until|while '<command>' succeeds`.
pub(crate) fn describe_condition(condition: &LoopCondition) -> String {
    format!(
        "{} {} succeeds",
        if condition.until { "until" } else { "while" },
        quote_command(&condition.command)
    )
}

/// The line of a loop that just started.
pub(crate) fn enabled_message(doc: &LoopDoc) -> String {
    let limit = match doc.limit {
        None => String::new(),
        Some(LoopLimit::Iterations { iterations }) => format!(
            " Limited to {iterations} {word}. {iterations} of {iterations} {word} remaining.",
            word = iterations_word(iterations)
        ),
        Some(LoopLimit::Duration { duration_ms }) => {
            let spelled = budget(duration_ms);
            format!(" Limited to {spelled}. {spelled} limit.")
        }
    };
    let condition = doc
        .state
        .condition
        .as_ref()
        .map_or_default(|condition| format!(" Continuing {}.", describe_condition(condition)));
    let tail = if doc.state.prompt.is_empty() {
        "Your next prompt will repeat after each turn."
    } else {
        "Repeating it after each turn."
    };
    format!(
        "Loop mode enabled.{limit}{condition} {tail} Esc suspends the ongoing loop; /loop again to disable."
    )
}

/// The line of a loop that ended: why it ended (stopped, satisfied, broken
/// check, out of turns or time, failed turns, budget).
pub(crate) fn end_message(doc: &LoopDoc, end: LoopEnd) -> String {
    let command = doc
        .state
        .condition
        .as_ref()
        .map_or_default(|condition| quote_command(&condition.command));
    match end {
        LoopEnd::Stopped => "Loop mode disabled.".to_owned(),
        LoopEnd::OutOfTurns => "Loop limit reached. Loop mode disabled.".to_owned(),
        LoopEnd::OutOfTime => "Loop time limit reached. Loop mode disabled.".to_owned(),
        LoopEnd::TurnsFailed => {
            "Loop stopped: 3 turns failed in a row. Loop mode disabled.".to_owned()
        }
        LoopEnd::OutOfBudget => {
            "Loop stopped: the budget funds no further turn. Loop mode disabled.".to_owned()
        }
        LoopEnd::Satisfied => {
            let until = doc.state.condition.as_ref().is_none_or(|c| c.until);
            if until {
                format!("Loop condition {command} is now satisfied. Loop mode disabled.")
            } else {
                format!("Loop condition {command} no longer holds. Loop mode disabled.")
            }
        }
        LoopEnd::CheckBroke => {
            let detail = doc
                .check_output
                .as_deref()
                .map(preview)
                .filter(|line| !line.is_empty())
                .map_or_default(|line| format!(": {line}"));
            match doc.state.last_check.map(|check| check.evidence) {
                Some(LoopEvidence::TimedOut) => format!(
                    "Loop condition {command} timed out after {}s. Loop mode disabled.",
                    CONDITION_TIMEOUT_MS / 1_000
                ),
                Some(LoopEvidence::SpawnFailed) => {
                    format!("Loop condition {command} could not run{detail}. Loop mode disabled.")
                }
                Some(LoopEvidence::Exited { code }) => format!(
                    "Loop condition {command} failed (exit {code}){detail}. Loop mode disabled."
                ),
                Some(LoopEvidence::NoStatus | LoopEvidence::Cancelled) | None => format!(
                    "Loop condition {command} failed (no exit status){detail}. Loop mode disabled."
                ),
            }
        }
    }
}

/// `/loop --status`: where the loop is and why.
pub(crate) fn status_message(doc: &LoopDoc, now_ms: u64) -> String {
    let state = &doc.state;
    let head = match state.phase {
        LoopPhase::Off => return "Loop: off".to_owned(),
        LoopPhase::Ended { .. } => {
            return match &doc.message {
                Some(message) => format!("Loop: off. Last loop: {message}"),
                None => "Loop: off".to_owned(),
            }
        }
        LoopPhase::Armed => "Loop: next prompt repeats".to_owned(),
        LoopPhase::Paused => "Loop: paused (the next prompt you send repeats)".to_owned(),
        LoopPhase::Turn => format!("Loop: running iteration {}", state.iteration),
        LoopPhase::Judging => format!("Loop: checking after iteration {}", state.iteration),
    };
    let mut parts = vec![head];
    if let (Some(remaining), Some(LoopLimit::Iterations { iterations })) =
        (state.remaining, doc.limit)
    {
        parts.push(format!(
            "{remaining} of {iterations} {} remaining",
            iterations_word(iterations)
        ));
    }
    if let Some(deadline) = state.deadline_ms {
        parts.push(format!(
            "{}s left",
            deadline.saturating_sub(now_ms).div_ceil(1_000)
        ));
    }
    if let Some(condition) = &state.condition {
        parts.push(describe_condition(condition));
    }
    if let Some(check) = state.last_check {
        let evidence = match check.evidence {
            LoopEvidence::Exited { code } => format!("exit {code}"),
            LoopEvidence::NoStatus => "no exit status".to_owned(),
            LoopEvidence::TimedOut => "timed out".to_owned(),
            LoopEvidence::SpawnFailed => "could not run".to_owned(),
            LoopEvidence::Cancelled => "cancelled".to_owned(),
        };
        parts.push(format!(
            "last check after iteration {}: {evidence}",
            check.iteration
        ));
    }
    if state.failures > 0 {
        parts.push(format!("{} failed in a row", state.failures));
    }
    parts.join(", ")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[allow(clippy::unnecessary_wraps)]
    fn enter(
        limit: Option<LoopLimit>,
        condition: Option<(&str, bool)>,
        prompt: Option<&str>,
    ) -> Result<LoopCommand, String> {
        Ok(LoopCommand::Enter {
            limit,
            condition: condition.map(|(command, until)| LoopCondition {
                command: command.to_owned(),
                until,
            }),
            prompt: prompt.map(str::to_owned),
        })
    }

    const COUNT_20: Option<LoopLimit> = Some(LoopLimit::Iterations { iterations: 20 });
    const TEN_MINUTES: Option<LoopLimit> = Some(LoopLimit::Duration {
        duration_ms: 600_000,
    });

    /// The reference rows of the loop syntax ("loop limit parsing" and
    /// "loop condition parsing"): each argument string, its parse or its
    /// message.
    #[test]
    fn arguments_parse_as_the_reference_rows() {
        let rows: Vec<(&str, Result<LoopCommand, String>)> = vec![
            ("", enter(None, None, None)),
            (
                "10",
                enter(Some(LoopLimit::Iterations { iterations: 10 }), None, None),
            ),
            ("10min", enter(TEN_MINUTES, None, None)),
            ("10 minutes", enter(TEN_MINUTES, None, None)),
            (
                "1h30m",
                enter(
                    Some(LoopLimit::Duration {
                        duration_ms: 5_400_000,
                    }),
                    None,
                    None,
                ),
            ),
            (
                "3 keep polishing",
                enter(
                    Some(LoopLimit::Iterations { iterations: 3 }),
                    None,
                    Some("keep polishing"),
                ),
            ),
            (
                "10m fix the build",
                enter(TEN_MINUTES, None, Some("fix the build")),
            ),
            ("keep going", enter(None, None, Some("keep going"))),
            (
                "0",
                Err("Loop count must be a positive integer.".to_owned()),
            ),
            ("-1", Err(LOOP_USAGE.to_owned())),
            ("1.5h", Err(LOOP_USAGE.to_owned())),
            ("10x10", Err(LOOP_USAGE.to_owned())),
            (
                "10fortnights",
                Err("Loop duration unit must be seconds, minutes, or hours.".to_owned()),
            ),
            ("10m", enter(TEN_MINUTES, None, None)),
            (
                "2h30min",
                enter(
                    Some(LoopLimit::Duration {
                        duration_ms: 9_000_000,
                    }),
                    None,
                    None,
                ),
            ),
            (
                "10m keep refactoring",
                enter(TEN_MINUTES, None, Some("keep refactoring")),
            ),
            (
                "5 fix the bug",
                enter(
                    Some(LoopLimit::Iterations { iterations: 5 }),
                    None,
                    Some("fix the bug"),
                ),
            ),
            (
                "10 minutes keep going",
                enter(TEN_MINUTES, None, Some("keep going")),
            ),
            ("   ", enter(None, None, None)),
            ("0m", Err("Loop duration must be positive.".to_owned())),
            (
                "20 --until 'bun test' fix the failing tests",
                enter(
                    COUNT_20,
                    Some(("bun test", true)),
                    Some("fix the failing tests"),
                ),
            ),
            (
                "--until 'bun test'",
                enter(None, Some(("bun test", true)), None),
            ),
            (
                "--while 'test -f GO'",
                enter(None, Some(("test -f GO", false)), None),
            ),
            (
                "--until='bun test'",
                enter(None, Some(("bun test", true)), None),
            ),
            (
                "--until \"bun test\"",
                enter(None, Some(("bun test", true)), None),
            ),
            (
                "--until true keep going",
                enter(None, Some(("true", true)), Some("keep going")),
            ),
            ("--until '--foo'", enter(None, Some(("--foo", true)), None)),
            (
                "10 minutes --until \"a  b\" go",
                enter(TEN_MINUTES, Some(("a  b", true)), Some("go")),
            ),
            (
                "10m --until \"a  b\" go",
                enter(TEN_MINUTES, Some(("a  b", true)), Some("go")),
            ),
            (
                "--until 'bun test",
                Err("--until has an unterminated quote.".to_owned()),
            ),
            (
                "--until 'a' --while 'b'",
                Err("Use only one of --while or --until.".to_owned()),
            ),
            (
                "keep going --until it works",
                enter(None, None, Some("keep going --until it works")),
            ),
            (
                "--until \"node -e \\\"process.exit(0)\\\"\" fix it",
                enter(
                    None,
                    Some(("node -e \"process.exit(0)\"", true)),
                    Some("fix it"),
                ),
            ),
            (
                "--while \"test \\\"$READY\\\" = yes\" continue",
                enter(
                    None,
                    Some(("test \"$READY\" = yes", false)),
                    Some("continue"),
                ),
            ),
            (
                "--until 'bun test'\nfix the tests",
                enter(None, Some(("bun test", true)), Some("fix the tests")),
            ),
            ("--stop", Ok(LoopCommand::Stop)),
            ("--status", Ok(LoopCommand::Status)),
        ];
        for (args, expected) in rows {
            assert_eq!(parse_loop_command(args), expected, "/loop {args}");
        }
    }

    /// The malformed-flag rows: the message names the flag and the fix.
    #[test]
    fn malformed_flags_are_refused_naming_the_fix() {
        let needs = "needs a shell command";
        let rows = [
            ("--until --while 'bun test'", needs),
            ("--until -f GO keep going", needs),
            ("--until", needs),
            ("--until ''", needs),
            ("--untl 'bun test'", "Unknown /loop flag --untl"),
            ("--until-ish 'bun test'", "Unknown /loop flag --until-ish"),
            ("--until123 fix", "Unknown /loop flag --until123"),
            ("--until, keep going", "Unknown /loop flag --until,"),
            ("--stop now", "Unknown /loop flag --stop"),
        ];
        for (args, part) in rows {
            let error = parse_loop_command(args).expect_err(args);
            assert!(error.contains(part), "/loop {args}: {error}");
        }
    }
}
