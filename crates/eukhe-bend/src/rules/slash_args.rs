//! The arguments of the session slash command `/auto` (typed as `/auto` or
//! `/autonomous`), the one answer of the removed `/goal` and the
//! quote-aware words of a command's argument text (`bend/slash_args.bend`,
//! entry `bend/ffi_slash_args.bend`; `laws/slash_args/`). Rust sends the
//! text and reads the answer; the numbers come back as digits the core
//! checked to fit a `u64`.

use crate::wire::{Reader, WireError, Writer};
use crate::{call, expect_core, Entry, Error};

/// The name `/auto` was typed as.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AutoName {
    Auto,
    Autonomous,
}

/// A limit named by an `/auto on` option.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Limit {
    Unlimited,
    Value(u64),
}

/// The gate options named by `/auto on`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GateOptions {
    /// The `--gate` commands in order; `None` when none was named.
    pub commands: Option<Vec<String>>,
    pub max_retries: Option<u64>,
    pub timeout_ms: Option<u64>,
}

/// The options of `/auto on`: once one limit is named, every other limit
/// comes back [`Limit::Unlimited`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AutonomousOptions {
    pub max_continuations: Option<Limit>,
    pub max_turns: Option<Limit>,
    pub max_tokens: Option<Limit>,
    pub timeout_ms: Option<Limit>,
    pub gates: Option<GateOptions>,
    pub subagent_keep_alive_ms: Option<u64>,
}

/// What `/auto <args>` asks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AutoArgs {
    Status,
    On(AutonomousOptions),
    Off,
    /// Turn autonomous mode on and send `text` as the user's message.
    Task {
        text: String,
    },
    /// The user-facing usage or validation error.
    Error(String),
}

/// The question tags of the entry (3, the removed goal objective's
/// question, stays unused: the core refuses it).
const GOAL: u32 = 0;
const AUTO: u32 = 1;
const WORDS: u32 = 2;
const AUTONOMOUS: u32 = 4;

fn ask(tag: u32, text: &str) -> Result<String, Error> {
    Ok(call(
        Entry::SlashArgs,
        &Writer::new().tag(tag).str(text).finish()?,
    )?)
}

/// What `/auto <args>` asks, typed as `name`.
#[must_use]
pub fn auto(name: AutoName, args: &str) -> AutoArgs {
    expect_core(Entry::SlashArgs, auto_call(name, args))
}

/// The one answer of the removed `/goal <args>`, whatever the args: the
/// text pointing to `/auto`.
#[must_use]
pub fn goal_pointer(args: &str) -> String {
    expect_core(Entry::SlashArgs, goal_pointer_call(args))
}

/// The words of a command's argument text: whitespace splits outside
/// quotes; `"` or `'` quotes, kept chars and all; a quoted word counts even
/// when empty.
#[must_use]
pub fn words(args: &str) -> Vec<String> {
    expect_core(Entry::SlashArgs, words_call(args))
}

fn name_tag(name: AutoName) -> u32 {
    match name {
        AutoName::Auto => AUTO,
        AutoName::Autonomous => AUTONOMOUS,
    }
}

fn auto_call(name: AutoName, args: &str) -> Result<AutoArgs, Error> {
    let reply = ask(name_tag(name), args)?;
    let mut reader = Reader::reply(&reply)?;
    let args = answer(&mut reader)?;
    reader.end()?;
    Ok(args)
}

fn goal_pointer_call(args: &str) -> Result<String, Error> {
    let reply = ask(GOAL, args)?;
    let mut reader = Reader::reply(&reply)?;
    let pointer = reader.str()?.to_string();
    reader.end()?;
    Ok(pointer)
}

fn answer(reader: &mut Reader<'_>) -> Result<AutoArgs, WireError> {
    Ok(match reader.tag_of(5, "an /auto answer")? {
        0 => AutoArgs::Status,
        1 => AutoArgs::On(options(reader)?),
        2 => AutoArgs::Off,
        3 => AutoArgs::Error(reader.str()?.to_string()),
        // `tag_of` answers a tag below 5: this is 4.
        _ => AutoArgs::Task {
            text: reader.str()?.to_string(),
        },
    })
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

    /// The answers come from the compiled core: a task, `/autonomous` read
    /// as `/auto` with named limits (the others unlimited), the `/goal`
    /// pointer whatever its args, quoted words.
    #[test]
    fn the_core_reads_slash_command_arguments() {
        let on = AutoArgs::On(AutonomousOptions {
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
        });
        assert_eq!(
            [
                auto(AutoName::Auto, "fix the 'red build'"),
                auto(AutoName::Autonomous, "on --max-turns 5 --gate 'npm test'"),
            ],
            [
                AutoArgs::Task {
                    text: "fix the 'red build'".to_string(),
                },
                on,
            ]
        );
        assert_eq!(
            [goal_pointer(""), goal_pointer("--budget 5000 keep going")],
            ["/goal is removed: use /auto", "/goal is removed: use /auto"]
        );
        assert_eq!(words("a \"b c\" ''"), ["a", "b c", ""]);
    }
}
