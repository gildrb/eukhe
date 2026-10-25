//! The arguments of the session slash commands `/goal` and `/autonomous`,
//! a goal objective, and the quote-aware words of a command's argument text
//! (`bend/slash_args.bend`, entry `bend/ffi_slash_args.bend`;
//! `laws/slash_args.bend`). Rust sends the text and reads the answer; the
//! numbers come back as digits the core checked to fit a `u64`.

use crate::wire::{Reader, WireError, Writer};
use crate::{call, expect_core, Entry, Error};

/// What `/goal <args>` asks, or a goal objective's verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GoalArgs {
    Status,
    Clear,
    Pause,
    Resume,
    /// The objective (trimmed) and the token budget, if one was named.
    Start {
        objective: String,
        token_budget: Option<u64>,
    },
    /// The user-facing usage or validation error.
    Error(String),
}

/// A limit named by an `/autonomous on` option.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Limit {
    Unlimited,
    Value(u64),
}

/// The gate options named by `/autonomous on`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GateOptions {
    /// The `--gate` commands in order; `None` when none was named.
    pub commands: Option<Vec<String>>,
    pub max_retries: Option<u64>,
    pub timeout_ms: Option<u64>,
}

/// The options of `/autonomous on`: once one limit is named, every other
/// limit comes back [`Limit::Unlimited`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AutonomousOptions {
    pub max_continuations: Option<Limit>,
    pub max_turns: Option<Limit>,
    pub max_tokens: Option<Limit>,
    pub timeout_ms: Option<Limit>,
    pub gates: Option<GateOptions>,
    pub subagent_keep_alive_ms: Option<u64>,
}

/// What `/autonomous <args>` asks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AutonomousArgs {
    Status,
    On(AutonomousOptions),
    Off,
    /// The user-facing usage or validation error.
    Error(String),
}

/// The question tags of the entry.
const GOAL: u32 = 0;
const AUTONOMOUS: u32 = 1;
const WORDS: u32 = 2;
const OBJECTIVE: u32 = 3;

fn ask(tag: u32, text: &str) -> Result<String, Error> {
    Ok(call(
        Entry::SlashArgs,
        &Writer::new().tag(tag).str(text).finish()?,
    )?)
}

/// What `/goal <args>` asks.
#[must_use]
pub fn goal(args: &str) -> GoalArgs {
    expect_core(Entry::SlashArgs, goal_call(GOAL, args))
}

/// A goal objective (as a goal tool gives it): trimmed, or the
/// user-facing reason it is refused (empty, or past its char limit).
///
/// # Errors
///
/// The refusal's text.
pub fn objective(text: &str) -> Result<String, String> {
    expect_core(Entry::SlashArgs, objective_call(text))
}

/// What `/autonomous <args>` asks.
#[must_use]
pub fn autonomous(args: &str) -> AutonomousArgs {
    expect_core(Entry::SlashArgs, autonomous_call(args))
}

/// The words of a command's argument text: whitespace splits outside
/// quotes; `"` or `'` quotes, kept chars and all; a quoted word counts even
/// when empty.
#[must_use]
pub fn words(args: &str) -> Vec<String> {
    expect_core(Entry::SlashArgs, words_call(args))
}

fn goal_call(tag: u32, text: &str) -> Result<GoalArgs, Error> {
    let reply = ask(tag, text)?;
    let mut reader = Reader::reply(&reply)?;
    let answer = match reader.tag_of(6, "a goal answer")? {
        0 => GoalArgs::Status,
        1 => GoalArgs::Clear,
        2 => GoalArgs::Pause,
        3 => GoalArgs::Resume,
        4 => {
            let objective = reader.str()?.to_string();
            let token_budget = if reader.maybe()? {
                Some(digits(reader.str()?)?)
            } else {
                None
            };
            GoalArgs::Start {
                objective,
                token_budget,
            }
        }
        // `tag_of` answers a tag below 6: this is 5.
        _ => GoalArgs::Error(reader.str()?.to_string()),
    };
    reader.end()?;
    Ok(answer)
}

fn objective_call(text: &str) -> Result<Result<String, String>, Error> {
    match goal_call(OBJECTIVE, text)? {
        GoalArgs::Start {
            objective,
            token_budget: None,
        } => Ok(Ok(objective)),
        GoalArgs::Error(reason) => Ok(Err(reason)),
        GoalArgs::Status
        | GoalArgs::Clear
        | GoalArgs::Pause
        | GoalArgs::Resume
        | GoalArgs::Start {
            token_budget: Some(_),
            ..
        } => Err(WireError::Malformed {
            at: 0,
            expected: "an objective or its refusal",
        }
        .into()),
    }
}

fn autonomous_call(args: &str) -> Result<AutonomousArgs, Error> {
    let reply = ask(AUTONOMOUS, args)?;
    let mut reader = Reader::reply(&reply)?;
    let answer = match reader.tag_of(4, "an autonomous answer")? {
        0 => AutonomousArgs::Status,
        1 => AutonomousArgs::On(options(&mut reader)?),
        2 => AutonomousArgs::Off,
        // `tag_of` answers a tag below 4: this is 3.
        _ => AutonomousArgs::Error(reader.str()?.to_string()),
    };
    reader.end()?;
    Ok(answer)
}

fn words_call(args: &str) -> Result<Vec<String>, Error> {
    let reply = ask(WORDS, args)?;
    let mut reader = Reader::reply(&reply)?;
    let words = strings(&mut reader)?;
    reader.end()?;
    Ok(words)
}

fn options(reader: &mut Reader<'_>) -> Result<AutonomousOptions, WireError> {
    let max_continuations = limit(reader)?;
    let max_turns = limit(reader)?;
    let max_tokens = limit(reader)?;
    let timeout_ms = limit(reader)?;
    let gates = if reader.maybe()? {
        let commands = if reader.maybe()? {
            Some(strings(reader)?)
        } else {
            None
        };
        Some(GateOptions {
            commands,
            max_retries: maybe_digits(reader)?,
            timeout_ms: maybe_digits(reader)?,
        })
    } else {
        None
    };
    Ok(AutonomousOptions {
        max_continuations,
        max_turns,
        max_tokens,
        timeout_ms,
        gates,
        subagent_keep_alive_ms: maybe_digits(reader)?,
    })
}

fn limit(reader: &mut Reader<'_>) -> Result<Option<Limit>, WireError> {
    if !reader.maybe()? {
        return Ok(None);
    }
    Ok(Some(match reader.tag_of(2, "a limit")? {
        0 => Limit::Unlimited,
        // `tag_of` answers a tag below 2: this is 1.
        _ => Limit::Value(digits(reader.str()?)?),
    }))
}

fn maybe_digits(reader: &mut Reader<'_>) -> Result<Option<u64>, WireError> {
    if reader.maybe()? {
        Ok(Some(digits(reader.str()?)?))
    } else {
        Ok(None)
    }
}

fn strings(reader: &mut Reader<'_>) -> Result<Vec<String>, WireError> {
    let count = reader.count()?;
    (0..count)
        .map(|_| reader.str().map(str::to_string))
        .collect()
}

/// Digits the core checked to fit a `u64`.
fn digits(text: &str) -> Result<u64, WireError> {
    text.parse().map_err(|_| WireError::Malformed {
        at: 0,
        expected: "the digits of a u64",
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The answers come from the compiled core: a budgeted goal, named
    /// limits with the others unlimited, quoted words.
    #[test]
    fn the_core_reads_slash_command_arguments() {
        assert_eq!(
            goal("--budget 5000 keep going"),
            GoalArgs::Start {
                objective: "keep going".to_string(),
                token_budget: Some(5000),
            }
        );
        assert_eq!(
            autonomous("on --max-turns 5 --gate 'npm test'"),
            AutonomousArgs::On(AutonomousOptions {
                max_continuations: Some(Limit::Unlimited),
                max_turns: Some(Limit::Value(5)),
                max_tokens: Some(Limit::Unlimited),
                timeout_ms: Some(Limit::Unlimited),
                gates: Some(GateOptions {
                    commands: Some(vec!["npm test".to_string()]),
                    max_retries: None,
                    timeout_ms: None,
                }),
                subagent_keep_alive_ms: None,
            })
        );
        assert_eq!(words("a \"b c\" ''"), ["a", "b c", ""]);
    }
}
