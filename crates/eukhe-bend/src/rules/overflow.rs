//! Whether a model reply is a context overflow (`bend/overflow.bend`,
//! entry `bend/ffi_overflow.bend`; `laws/overflow.bend`): an error whose
//! message a provider writes for an input past the model's window (the
//! patterns of `bend/overflow.bend`, searched case-insensitively by
//! `bend/text_pat.bend`), a stop whose usage passes the window, or a
//! length stop with no output that fills 99% of it; and whether a length
//! stop is worth one compact-and-retry.

use crate::wire::{Reader, Writer, NAT_MAX, STR_MAX};
use crate::{call, expect_core, Entry, Error};

/// How a reply stopped, as the rule tells the cases apart.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stop {
    Stop,
    Length,
    /// A tool use or an abort.
    Other,
    Error,
}

impl Stop {
    const fn tag(self) -> u32 {
        match self {
            Stop::Stop => 0,
            Stop::Length => 1,
            Stop::Other => 2,
            Stop::Error => 3,
        }
    }
}

/// One finished reply, as the overflow rule reads it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Reply<'a> {
    pub stop: Stop,
    /// The error message; empty when there is none.
    pub message: &'a str,
    pub provider: &'a str,
    /// The model's context window; 0 when unknown.
    pub window: u64,
    pub input: u64,
    pub cache_read: u64,
    pub output: u64,
}

/// Whether `reply` is a context overflow.
#[must_use]
pub fn is_overflow(reply: &Reply<'_>) -> bool {
    expect_core(Entry::Overflow, overflow_call(reply))
}

fn overflow_call(reply: &Reply<'_>) -> Result<bool, Error> {
    let mut request = Writer::new();
    request
        .tag(0)
        .tag(reply.stop.tag())
        .str(wire_text(reply.message))
        .str(wire_text(reply.provider))
        .nat(reply.window.min(NAT_MAX))
        .nat(reply.input.min(NAT_MAX))
        .nat(reply.cache_read.min(NAT_MAX))
        .nat(reply.output.min(NAT_MAX));
    answer(&request.finish()?)
}

/// Whether a reply that stopped with `stop` and `output` tokens ended
/// below the intended output limit `desired` (0: none).
#[must_use]
pub fn is_recoverable_length(stop: Stop, desired: u64, output: u64) -> bool {
    expect_core(Entry::Overflow, recoverable_call(stop, desired, output))
}

fn recoverable_call(stop: Stop, desired: u64, output: u64) -> Result<bool, Error> {
    let mut request = Writer::new();
    request
        .tag(1)
        .tag(stop.tag())
        .nat(desired.min(NAT_MAX))
        .nat(output.min(NAT_MAX));
    answer(&request.finish()?)
}

fn answer(request: &str) -> Result<bool, Error> {
    let reply = call(Entry::Overflow, request)?;
    let mut reader = Reader::reply(&reply)?;
    let verdict = reader.bool()?;
    reader.end()?;
    Ok(verdict)
}

/// A text as the wire carries it: its first [`STR_MAX`] chars (a pattern
/// that starts past them is not searched for).
fn wire_text(text: &str) -> &str {
    text.char_indices()
        .nth(STR_MAX)
        .map_or(text, |(end, _)| &text[..end])
}

#[cfg(test)]
mod tests {
    use super::*;

    fn error(message: &str, provider: &str) -> bool {
        is_overflow(&Reply {
            stop: Stop::Error,
            message,
            provider,
            window: 200_000,
            input: 0,
            cache_read: 0,
            output: 0,
        })
    }

    /// The verdict comes from the compiled core: a provider's overflow
    /// text (in any case, a Kelvin sign for the k), a calm text, and
    /// Cerebras' bodyless 400 only from Cerebras.
    #[test]
    fn the_core_decides_the_overflow() {
        assert_eq!(
            [
                error("400 Prompt is too long", "zai"),
                error("CONTEXT_LENGTH_EXCEEDED", "x"),
                error("exceeded model to\u{212a}en limit", "x"),
                error("Rate limit exceeded: too many tokens", "x"),
                error("400 status code (no body)", "cerebras"),
                error("400 status code (no body)", "openai"),
                is_recoverable_length(Stop::Length, 128, 16),
            ],
            [true, true, true, false, true, false, true]
        );
    }
}
