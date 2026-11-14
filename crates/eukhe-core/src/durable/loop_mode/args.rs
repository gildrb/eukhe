//! `/loop` arguments and the lines a loop reports: `/loop [count|duration]
//! [--while|--until '<command>'|<condition in words>] [prompt]`, plus two
//! spellings that are not flags of a loop: `/loop --stop` (end the loop,
//! never start one) and `/loop --status`.

use eukhe_bend::rules::loop_mode::{classify, ConditionText};
use eukhe_bend::wire::NAT_MAX;
use eukhe_types::loop_mode::{LoopCondition, LoopEnd, LoopEvidence, LoopLimit, LoopPhase};

use super::docs::LoopDoc;

/// The usage line every malformed-arguments message ends with.
const LOOP_USAGE: &str = "Usage: /loop [count|duration] [--while|--until '<command>'|<condition in words>] [prompt]. A count N repeats the prompt at most N times after the first turn: N+1 turns at most. Examples: /loop 10, /loop 10m, /loop 20 --until 'bun test' fix the failing tests, /loop 5 --until the README explains every flag.";

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
    /// `/loop [count|duration] [--while|--until <condition>] [prompt]`.
    Enter {
        limit: Option<LoopLimit>,
        condition: Option<ConditionArg>,
        /// The text after the condition's first word.
        prompt: Option<String>,
    },
}

/// The text after `--until` / `--while`, before it is classified: a
/// command or a condition in words.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ConditionArg {
    /// The flag was `--until`.
    pub(crate) until: bool,
    /// The first shell word, quotes removed.
    pub(crate) word: String,
    /// The whole text after the flag.
    pub(crate) raw: String,
    /// Some part of the first word was quoted or escaped.
    pub(crate) quoted: bool,
}

/// The condition of `arg` and the loop's prompt, once the shell's lookup
/// of its first word is known (`found`: an executable on PATH or a shell
/// builtin). The compiled core classifies: a command is the first word,
/// and the prompt the text after it; a stated condition is the whole text,
/// and the prompt is that text too.
///
/// # Errors
///
/// The core's refusal (a text past the wire's bound).
pub(crate) fn resolve_condition(
    arg: &ConditionArg,
    prompt: Option<String>,
    found: bool,
) -> Result<(LoopCondition, Option<String>), String> {
    let condition = classify(&ConditionText {
        until: arg.until,
        word: &arg.word,
        raw: &arg.raw,
        quoted: arg.quoted,
        found,
    })
    .map_err(|error| format!("The loop condition could not be read: {error}"))?;
    let prompt = if condition.stated {
        Some(condition.command.clone())
    } else {
        prompt
    };
    Ok((condition, prompt))
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
/// Answers the word, the text after it, and whether any part of the word
/// was quoted or escaped.
///
/// # Errors
///
/// An unclosed quote.
fn read_shell_word(text: &str) -> Result<Option<(String, String, bool)>, ()> {
    let text = text.trim_start_matches(is_shell_space);
    if text.is_empty() {
        return Ok(None);
    }
    let mut value = String::new();
    let mut single = false;
    let mut double = false;
    let mut quoted = false;
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
            '\'' => (single, quoted) = (true, true),
            '"' => (double, quoted) = (true, true),
            '\\' => {
                quoted = true;
                match chars.next() {
                    Some((_, next)) => value.push(next),
                    None => value.push(c),
                }
            }
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
    Ok(Some((value, text[end..].trim().to_owned(), quoted)))
}

/// The first word of `text` as written, up to whitespace: a word with an
/// apostrophe or an unpaired quote inside it (`don't`) is prose, never
/// shell syntax.
fn plain_word(text: &str) -> (String, String) {
    let text = text.trim_start_matches(is_shell_space);
    let end = text.find(is_shell_space).unwrap_or(text.len());
    (text[..end].to_owned(), text[end..].trim().to_owned())
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

/// Split an optional leading `--while` / `--until` flag off `input`: the
/// text after it, its first word, and the text after that word (the
/// prompt of a command condition).
fn take_condition(input: &str) -> Result<(Option<ConditionArg>, String), String> {
    let mut rest = input.trim().to_owned();
    let mut condition: Option<ConditionArg> = None;
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
                "{name} needs a condition: a quoted command (/loop {name} 'bun test') or the condition in words (/loop {name} the tests pass)."
            )
        };
        let raw = value_text.trim();
        // A quote that opens the text starts a command; one inside the
        // first word (an apostrophe) is prose.
        let word = match read_shell_word(value_text) {
            Ok(word) => word,
            Err(()) if raw.starts_with(['\'', '"']) => {
                return Err(format!("{name} has an unterminated quote."));
            }
            Err(()) => {
                let (word, left) = plain_word(value_text);
                Some((word, left, false))
            }
        };
        let Some((value, left, quoted)) = word else {
            return Err(needs());
        };
        if value.trim().is_empty() || raw.starts_with('-') {
            return Err(needs());
        }
        condition = Some(ConditionArg {
            until,
            word: value.trim().to_owned(),
            raw: raw.to_owned(),
            quoted,
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

fn repeats_word(n: u64) -> &'static str {
    if n == 1 {
        "repeat"
    } else {
        "repeats"
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

/// The condition as a status line reads it: `until|while '<command>'
/// succeeds`, or for a stated condition `until|while (judged): <text>`.
pub(crate) fn describe_condition(condition: &LoopCondition) -> String {
    let polarity = if condition.until { "until" } else { "while" };
    if condition.stated {
        format!("{polarity} (judged): {}", preview(&condition.command))
    } else {
        format!("{polarity} {} succeeds", quote_command(&condition.command))
    }
}

/// The line of a loop that just started.
pub(crate) fn enabled_message(doc: &LoopDoc) -> String {
    let limit = match doc.limit {
        None => String::new(),
        Some(LoopLimit::Iterations { iterations }) => format!(
            " Limited to {iterations} {word} after the first turn ({total} turns at most). {iterations} of {iterations} {word} remaining.",
            word = repeats_word(iterations),
            total = iterations.saturating_add(1)
        ),
        Some(LoopLimit::Duration { duration_ms }) => {
            let spelled = budget(duration_ms);
            format!(" Limited to {spelled}. {spelled} limit.")
        }
    };
    let keys = "Esc suspends the ongoing loop; /loop again to disable.";
    if let Some(condition) = doc.state.condition.as_ref().filter(|c| c.stated) {
        return format!(
            "Loop on: repeats after each turn {} a model judge finds this met: \"{}\".{limit} {keys}",
            if condition.until { "until" } else { "while" },
            preview(&condition.command)
        );
    }
    let condition = doc
        .state
        .condition
        .as_ref()
        .map(|condition| format!(" Continuing {}.", describe_condition(condition)))
        .unwrap_or_default();
    let tail = if doc.state.prompt.is_empty() {
        "Your next prompt will repeat after each turn."
    } else {
        "Repeating it after each turn."
    };
    format!("Loop mode enabled.{limit}{condition} {tail} {keys}")
}

/// ` (<the first line of the check's output>)`, or nothing.
fn in_parens(output: Option<&str>) -> String {
    output
        .map(preview)
        .filter(|line| !line.is_empty())
        .map(|line| format!(" ({line})"))
        .unwrap_or_default()
}

/// The line of a loop that ended: why it ended (stopped, satisfied, broken
/// check, out of turns or time, failed turns, budget).
pub(crate) fn end_message(doc: &LoopDoc, end: LoopEnd) -> String {
    let condition = doc.state.condition.as_ref();
    let stated = condition.is_some_and(|c| c.stated);
    let command = condition
        .map(|condition| quote_command(&condition.command))
        .unwrap_or_default();
    match end {
        LoopEnd::Stopped => "Loop mode disabled.".to_owned(),
        LoopEnd::OutOfTurns => "Loop limit reached. Loop mode disabled.".to_owned(),
        LoopEnd::OutOfTime => "Loop time limit reached. Loop mode disabled.".to_owned(),
        LoopEnd::TurnsFailed => "Loop stopped: 3 turns failed in a row.".to_owned(),
        LoopEnd::OutOfBudget => "Loop stopped: the budget funds no further turn.".to_owned(),
        LoopEnd::Satisfied => {
            let until = condition.is_none_or(|c| c.until);
            let reason = in_parens(doc.check_output.as_deref());
            match (stated, until) {
                (true, true) => {
                    format!("Loop done: a model judge found the condition met{reason}.")
                }
                (true, false) => {
                    format!("Loop done: a model judge found the condition no longer met{reason}.")
                }
                (false, true) => {
                    format!("Loop condition {command} is now satisfied. Loop mode disabled.")
                }
                (false, false) => {
                    format!("Loop condition {command} no longer holds. Loop mode disabled.")
                }
            }
        }
        LoopEnd::CheckBroke if stated => format!(
            "Loop stopped: the judge could not decide{}.",
            in_parens(doc.check_output.as_deref())
        ),
        LoopEnd::CheckBroke => {
            let detail = doc
                .check_output
                .as_deref()
                .map(preview)
                .filter(|line| !line.is_empty())
                .map(|line| format!(": {line}"))
                .unwrap_or_default();
            let head = format!("Loop stopped: the condition command {command}");
            match doc.state.last_check.map(|check| check.evidence) {
                Some(LoopEvidence::TimedOut) => {
                    format!("{head} timed out after {}s.", CONDITION_TIMEOUT_MS / 1_000)
                }
                Some(LoopEvidence::SpawnFailed) => format!("{head} could not start{detail}."),
                Some(LoopEvidence::Exited { code: 127 }) => {
                    format!("{head} could not run (exit 127: command not found).")
                }
                Some(LoopEvidence::Exited { code: 126 }) => {
                    format!("{head} could not run (exit 126: not executable).")
                }
                Some(LoopEvidence::Exited { code }) => {
                    format!("{head} failed (exit {code}){detail}.")
                }
                Some(
                    LoopEvidence::NoStatus
                    | LoopEvidence::Cancelled
                    | LoopEvidence::Ruled { .. }
                    | LoopEvidence::Unruled,
                )
                | None => format!("{head} ended with no exit status{detail}."),
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
            repeats_word(iterations)
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
            LoopEvidence::Ruled { met: true } => "a model judge found it met".to_owned(),
            LoopEvidence::Ruled { met: false } => "a model judge found it not met".to_owned(),
            LoopEvidence::Unruled => "the judge could not decide".to_owned(),
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

    /// A `/loop` command once its condition is classified.
    #[derive(Debug, PartialEq, Eq)]
    enum Parsed {
        Stop,
        Status,
        Enter {
            limit: Option<LoopLimit>,
            condition: Option<LoopCondition>,
            prompt: Option<String>,
        },
    }

    /// Parse `args` and classify its condition, the shell finding exactly
    /// the words `true`, `test`, `bun` and `node`.
    fn parse(args: &str) -> Result<Parsed, String> {
        Ok(match parse_loop_command(args)? {
            LoopCommand::Stop => Parsed::Stop,
            LoopCommand::Status => Parsed::Status,
            LoopCommand::Enter {
                limit,
                condition: None,
                prompt,
            } => Parsed::Enter {
                limit,
                condition: None,
                prompt,
            },
            LoopCommand::Enter {
                limit,
                condition: Some(arg),
                prompt,
            } => {
                let found = matches!(arg.word.as_str(), "true" | "test" | "bun" | "node");
                let (condition, prompt) = resolve_condition(&arg, prompt, found)?;
                Parsed::Enter {
                    limit,
                    condition: Some(condition),
                    prompt,
                }
            }
        })
    }

    /// A loop whose condition is `text` in words, and whose prompt is that
    /// text too.
    #[allow(clippy::unnecessary_wraps)]
    fn stated(limit: Option<LoopLimit>, text: &str, until: bool) -> Result<Parsed, String> {
        Ok(Parsed::Enter {
            limit,
            condition: Some(LoopCondition {
                command: text.to_owned(),
                until,
                stated: true,
            }),
            prompt: Some(text.to_owned()),
        })
    }

    #[allow(clippy::unnecessary_wraps)]
    fn enter(
        limit: Option<LoopLimit>,
        condition: Option<(&str, bool)>,
        prompt: Option<&str>,
    ) -> Result<Parsed, String> {
        Ok(Parsed::Enter {
            limit,
            condition: condition.map(|(command, until)| LoopCondition {
                command: command.to_owned(),
                until,
                stated: false,
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
        let rows: Vec<(&str, Result<Parsed, String>)> = vec![
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
            // The owner's message: a condition in words, never the
            // command `you`.
            (
                "--until you should definitely be iterating on that skill until it works reliably. you should and could test this out on the https://github.com/gildrb/dotfiles repository.",
                stated(
                    None,
                    "you should definitely be iterating on that skill until it works reliably. you should and could test this out on the https://github.com/gildrb/dotfiles repository.",
                    true,
                ),
            ),
            (
                "20 --until the tests pass and the README says so",
                stated(COUNT_20, "the tests pass and the README says so", true),
            ),
            (
                "--while the build is still red",
                stated(None, "the build is still red", false),
            ),
            (
                "--until=everything is green",
                stated(None, "everything is green", true),
            ),
            (
                "--until it's done, keep fixing \"edge\" cases",
                stated(None, "it's done, keep fixing \"edge\" cases", true),
            ),
            (
                "--until test -f DONE keep going",
                enter(None, Some(("test", true)), Some("-f DONE keep going")),
            ),
            ("--stop", Ok(Parsed::Stop)),
            ("--status", Ok(Parsed::Status)),
        ];
        for (args, expected) in rows {
            assert_eq!(parse(args), expected, "/loop {args}");
        }
    }

    /// The malformed-flag rows: the message names the flag and the fix.
    #[test]
    fn malformed_flags_are_refused_naming_the_fix() {
        let needs = "needs a condition: a quoted command";
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

    fn ended(condition: LoopCondition, evidence: LoopEvidence, output: &str) -> LoopDoc {
        let mut doc = LoopDoc::default();
        doc.state.condition = Some(condition);
        doc.state.last_check = Some(eukhe_types::loop_mode::LoopCheck {
            iteration: 1,
            evidence,
        });
        doc.check_output = Some(output.to_owned());
        doc
    }

    /// The lines of a stated condition name the judge, never a command;
    /// a command that is not found says so plainly.
    #[test]
    fn the_lines_name_who_decided() {
        let words = LoopCondition {
            command: "the tests pass".to_owned(),
            until: true,
            stated: true,
        };
        let mut doc = LoopDoc::default();
        doc.state.condition = Some(words.clone());
        doc.state.prompt = "the tests pass".to_owned();
        assert_eq!(
            enabled_message(&doc),
            "Loop on: repeats after each turn until a model judge finds this met: \"the tests pass\". Esc suspends the ongoing loop; /loop again to disable."
        );
        assert_eq!(describe_condition(&words), "until (judged): the tests pass");
        assert_eq!(
            end_message(
                &ended(
                    words.clone(),
                    LoopEvidence::Ruled { met: true },
                    "the diff adds the test and the answer shows it green"
                ),
                LoopEnd::Satisfied
            ),
            "Loop done: a model judge found the condition met (the diff adds the test and the answer shows it green)."
        );
        assert_eq!(
            end_message(
                &ended(words, LoopEvidence::Unruled, "the judge's request failed"),
                LoopEnd::CheckBroke
            ),
            "Loop stopped: the judge could not decide (the judge's request failed)."
        );
        let you = LoopCondition {
            command: "you".to_owned(),
            until: true,
            stated: false,
        };
        assert_eq!(
            end_message(
                &ended(
                    you,
                    LoopEvidence::Exited { code: 127 },
                    "bash: line 1: you: command not found"
                ),
                LoopEnd::CheckBroke
            ),
            "Loop stopped: the condition command `you` could not run (exit 127: command not found)."
        );
    }
}
