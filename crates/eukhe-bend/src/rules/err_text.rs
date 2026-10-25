//! What a provider's error text says (`bend/err_text.bend`, entry
//! `bend/ffi_err_text.bend`; `laws/err_text.bend`): each rule is a table
//! of explicit phrases (`bend/phrase.bend`: literal chars, an optional
//! gap char, a run of digits, whole-word edges) searched in the text
//! folded for case (`bend/text_pat.bend` `fold_str`).

use crate::wire::{Reader, Writer, STR_MAX};
use crate::{call, expect_core, Entry, Error};

/// The rules of the entry, each one table of phrases.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rule {
    /// A quota, billing or admission limit, or the HTTP layer's refused
    /// server wait: a retry cannot cure it (eukhe-ai `utils/retry.rs`).
    Limit,
    /// A transient provider or transport failure, its status codes and
    /// transport words as whole words (eukhe-ai `utils/retry.rs`).
    Transient,
    /// The Codex client's terminal rate limit of a 429.
    CodexTerminal,
    /// The Codex client's retryable text.
    CodexRetryable,
    /// The Codex client's usage-limit error code.
    CodexUsageCode,
    /// A timeout in the Anthropic client's send error.
    Timeout,
}

impl Rule {
    const fn tag(self) -> u32 {
        match self {
            Rule::Limit => 0,
            Rule::Transient => 1,
            Rule::CodexTerminal => 2,
            Rule::CodexRetryable => 3,
            Rule::CodexUsageCode => 4,
            Rule::Timeout => 5,
        }
    }
}

/// Whether `rule` holds for one of `texts`.
#[must_use]
pub fn holds(rule: Rule, texts: &[&str]) -> bool {
    expect_core(Entry::ErrText, holds_call(rule, texts))
}

fn holds_call(rule: Rule, texts: &[&str]) -> Result<bool, Error> {
    let mut request = Writer::new();
    request.tag(rule.tag()).count(texts.len());
    for text in texts {
        request.str(wire_text(text));
    }
    let reply = call(Entry::ErrText, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let verdict = reader.bool()?;
    reader.end()?;
    Ok(verdict)
}

/// A text as the wire carries it: its first [`STR_MAX`] chars (a phrase
/// that starts past them is not searched for).
fn wire_text(text: &str) -> &str {
    text.char_indices()
        .nth(STR_MAX)
        .map_or(text, |(end, _)| &text[..end])
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The verdicts come from the compiled core: a phrase in any case, a
    /// status code only as a whole word, a gap char that is no line
    /// terminator, a Kelvin sign for the k.
    #[test]
    fn the_core_reads_the_error_text() {
        assert_eq!(
            [
                holds(Rule::Limit, &["x", "Quota exceeded"]),
                holds(
                    Rule::Limit,
                    &["Server requested 120s retry delay (max: 60s)"]
                ),
                holds(Rule::Transient, &["status 429"]),
                holds(Rule::Transient, &["limit 5242880 bytes"]),
                holds(Rule::Transient, &["soc\u{212a}et hang up"]),
                holds(Rule::CodexRetryable, &["Rate-Limit"]),
                holds(Rule::CodexRetryable, &["rate\u{2028}limit"]),
                holds(Rule::CodexUsageCode, &["USAGE_NOT_INCLUDED"]),
                holds(Rule::CodexTerminal, &["billing"]),
                holds(Rule::Timeout, &["request TimedOut"]),
                holds(Rule::Timeout, &[]),
            ],
            [true, true, true, false, true, true, false, true, true, true, false]
        );
    }
}
