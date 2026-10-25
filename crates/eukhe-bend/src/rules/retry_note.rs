//! The note at the end of a retry's request (`bend/retry_note.bend`, entry
//! `bend/ffi_retry_note.bend`; `laws/retry_note.bend`): the text that names
//! the retry's attempt, what went wrong with the noted reply, and what the
//! model should do instead. [`text`] encodes the attempt and the cause,
//! calls [`Entry::RetryNote`] and decodes the text.

use crate::wire::{Reader, Writer};
use crate::{call, Entry, Error};

/// One call of a repeated round (`Rn.Call`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Call<'a> {
    pub tool: &'a str,
    /// The call's arguments as the note shows them.
    pub arguments: &'a str,
}

/// What went wrong with the noted reply (`Rn.Cause`). `row` counts the
/// notes of a recovery in a row, this one included; `cap` is that
/// recovery's limit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cause<'a> {
    /// The reply repeated a cycle of `period` lines ending with `line`,
    /// already quoted.
    Repeated { period: u32, line: &'a str },
    /// The reply had no text and no tool call.
    NoAnswer,
    /// The reply hit the output limit (`tokens`, 0 when none was
    /// reported) while it still reasoned.
    Length { tokens: u64, row: u32, cap: u32 },
    /// The reply wrote tool calls as `markup` text that could not be read,
    /// for `reason`.
    Leaked {
        markup: &'a str,
        reason: &'a str,
        row: u32,
        cap: u32,
    },
    /// The reply would have made `calls` `rounds` rounds in a row with the
    /// same results.
    Redirect {
        calls: &'a [Call<'a>],
        rounds: u32,
        row: u32,
        cap: u32,
    },
    /// The stream sent no event for `idle_ms`.
    Stalled { idle_ms: u64 },
}

/// The note of the retry of `attempt` after a reply that went wrong for
/// `cause` (`Rn.text`): "Harness note, attempt <attempt>: " and the
/// cause's text.
///
/// # Errors
///
/// [`Error::Wire`] when a number is past [`crate::wire::NAT_MAX`] or a text
/// past [`crate::wire::STR_MAX`] chars; else only from an inconsistent
/// build (see [`crate::expect_core`]).
pub fn text(attempt: u64, cause: &Cause<'_>) -> Result<String, Error> {
    let mut request = Writer::new();
    request.nat(attempt);
    match *cause {
        Cause::Repeated { period, line } => {
            request.tag(0).nat(period.into()).str(line);
        }
        Cause::NoAnswer => {
            request.tag(1);
        }
        Cause::Length { tokens, row, cap } => {
            request.tag(2).nat(tokens).nat(row.into()).nat(cap.into());
        }
        Cause::Leaked {
            markup,
            reason,
            row,
            cap,
        } => {
            request
                .tag(3)
                .str(markup)
                .str(reason)
                .nat(row.into())
                .nat(cap.into());
        }
        Cause::Redirect {
            calls,
            rounds,
            row,
            cap,
        } => {
            request.tag(4).count(calls.len());
            for repeated in calls {
                request.str(repeated.tool).str(repeated.arguments);
            }
            request.nat(rounds.into()).nat(row.into()).nat(cap.into());
        }
        Cause::Stalled { idle_ms } => {
            request.tag(5).nat(idle_ms);
        }
    }
    let reply = call(Entry::RetryNote, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let text = reply.str()?.to_string();
    reply.end()?;
    Ok(text)
}

#[cfg(test)]
mod tests {
    use super::{text, Call, Cause};

    #[test]
    fn the_codec_carries_each_cause_through_the_core() {
        let calls = [
            Call {
                tool: "read",
                arguments: "{}",
            },
            Call {
                tool: "ls",
                arguments: "{}",
            },
        ];
        let redirect = Cause::Redirect {
            calls: &calls,
            rounds: 3,
            row: 1,
            cap: 2,
        };
        assert_eq!(
            text(5, &redirect).unwrap(),
            "Harness note, attempt 5: you made the same tool calls 3 times in a row, and they \
             gave the same results each time: `read` with `{}`; `ls` with `{}`. The harness did \
             not run them again. Do not make these calls with these arguments again in this \
             turn. Use different arguments, use a different tool, or give your answer with what \
             you found. Redirect note 1 of 2."
        );
        assert_eq!(
            text(2, &Cause::Stalled { idle_ms: 90_500 }).unwrap(),
            "Harness note, attempt 2: your previous reply produced no output for 90 s, so the \
             harness cut it. Reason briefly, then act: give the answer or call the tool of the \
             next step."
        );
    }
}
