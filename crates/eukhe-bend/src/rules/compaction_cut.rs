//! Where a compaction cuts the model context and what the summarizer's
//! answer is (`bend/compaction_cut.bend`, entry `bend/ffi_compaction_cut.bend`;
//! `laws/compaction_cut.bend`): walking back from the newest contribution
//! until the tokens kept reach the limit, the first candidate at or after
//! that contribution (else the last candidate), when something comes before
//! it; and whether an answer is a summary, else its failure text. The caller
//! gives each contribution's estimated tokens and its messages' facts
//! ([`Fact`], call ids interned across the whole context), and the answer's
//! stop reason, tool call, non-blank text and error message.

use eukhe_types::pi_ai::StopReason;

use crate::rules::context_order::{put_facts, stop_tag, Fact};
use crate::wire::{Reader, WireError, Writer, NAT_MAX};
use crate::{call, expect_core, Entry, Error};

/// When the walk back from the newest contribution stops (`Cc.Limit`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Limit {
    /// It never stops: there is no cut.
    Never,
    /// At the first contribution where the tokens kept are this many or
    /// more.
    Below(u64),
}

impl Limit {
    /// The limit of the walk that keeps going while `kept < keep_recent_tokens`
    /// (the tokens kept, a whole JS number, against the keep window). For a
    /// whole `kept` and a finite `k > 0`, `kept < k` is `kept < ceil(k)`;
    /// for NaN and `k <= 0` (`-inf` included) it never holds, the walk stops
    /// at once: `Below(0)`; for `+inf` it always holds: `Never`. A ceiling
    /// past [`NAT_MAX`] (10^14 tokens, 400 TB of text) is clamped to it.
    #[must_use]
    pub fn of_keep(keep_recent_tokens: f64) -> Limit {
        if keep_recent_tokens.is_nan() || keep_recent_tokens <= 0.0 {
            return Limit::Below(0);
        }
        if keep_recent_tokens.is_infinite() {
            return Limit::Never;
        }
        let ceiling = keep_recent_tokens.ceil();
        #[expect(
            clippy::cast_precision_loss,
            reason = "NAT_MAX is below 2^53, where the conversion is exact"
        )]
        let max = NAT_MAX as f64;
        if ceiling >= max {
            Limit::Below(NAT_MAX)
        } else {
            #[expect(
                clippy::cast_possible_truncation,
                clippy::cast_sign_loss,
                reason = "a whole number in 1..NAT_MAX converts exactly"
            )]
            Limit::Below(ceiling as u64)
        }
    }
}

/// A contribution of the context: an active entry's messages (the head
/// marker's first when there is one).
#[derive(Clone, Copy, Debug)]
pub struct Contribution<'a> {
    /// Its estimated tokens; saturated at [`NAT_MAX`].
    pub tokens: u64,
    pub facts: &'a [Fact],
}

/// The summarizer's answer as the core sees it.
#[derive(Clone, Copy, Debug)]
pub struct Answer<'a> {
    pub stop: StopReason,
    /// Whether it called a tool.
    pub calls: bool,
    /// Whether its text, joined and trimmed as JS does, is not blank.
    pub text: bool,
    pub error: Option<&'a str>,
}

/// What the summarizer's answer is (`Cc.Outcome`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome {
    Summary,
    /// Not a summary: the failure's text.
    Failed(String),
}

/// The index of the first contribution a compaction keeps, or `None` when
/// there is nothing to compact; `head`: the first contribution is the head
/// marker's.
///
/// # Panics
/// When the compiled core fails (an inconsistent build).
#[must_use]
pub fn cut(head: bool, limit: Limit, contributions: &[Contribution<'_>]) -> Option<usize> {
    expect_core(Entry::CompactionCut, call_cut(head, limit, contributions))
}

/// Whether `answer` is a summary, else its failure text.
///
/// # Panics
/// When the compiled core fails (an inconsistent build), or the error
/// message is past the wire's longest string.
#[must_use]
pub fn summary(answer: Answer<'_>) -> Outcome {
    expect_core(Entry::CompactionCut, call_summary(answer))
}

fn call_cut(
    head: bool,
    limit: Limit,
    contributions: &[Contribution<'_>],
) -> Result<Option<usize>, Error> {
    let mut request = Writer::new();
    request.tag(0).bool(head);
    match limit {
        Limit::Never => {
            request.tag(0);
        }
        Limit::Below(k) => {
            request.tag(1).nat(k.min(NAT_MAX));
        }
    }
    request.count(contributions.len());
    for contribution in contributions {
        request.nat(contribution.tokens.min(NAT_MAX));
        put_facts(&mut request, contribution.facts);
    }
    let reply = call(Entry::CompactionCut, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let cut = if reply.maybe()? {
        let index = usize::try_from(reply.nat()?)
            .ok()
            .filter(|&index| index < contributions.len())
            .ok_or(WireError::Malformed {
                at: 0,
                expected: "a contribution's index",
            })?;
        Some(index)
    } else {
        None
    };
    reply.end()?;
    Ok(cut)
}

fn call_summary(answer: Answer<'_>) -> Result<Outcome, Error> {
    let mut request = Writer::new();
    request
        .tag(1)
        .tag(stop_tag(answer.stop))
        .bool(answer.calls)
        .bool(answer.text);
    match answer.error {
        None => {
            request.none();
        }
        Some(error) => {
            request.some().str(error);
        }
    }
    let reply = call(Entry::CompactionCut, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let failed = reply.tag_of(2, "an outcome")? == 1;
    let outcome = if failed {
        Outcome::Failed(reply.str()?.to_owned())
    } else {
        Outcome::Summary
    };
    reply.end()?;
    Ok(outcome)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The keep window as the f64 comparison reads it: NaN and `k <= 0`
    /// never keep walking, `+inf` always does, a fraction rounds up.
    #[test]
    fn the_keep_window_is_the_limit_the_f64_comparison_gives() {
        let limits: Vec<Limit> = [
            f64::NAN,
            f64::NEG_INFINITY,
            -1.0,
            0.0,
            0.25,
            150.0,
            150.2,
            1e300,
            f64::INFINITY,
        ]
        .into_iter()
        .map(Limit::of_keep)
        .collect();
        assert_eq!(
            limits,
            vec![
                Limit::Below(0),
                Limit::Below(0),
                Limit::Below(0),
                Limit::Below(0),
                Limit::Below(1),
                Limit::Below(150),
                Limit::Below(151),
                Limit::Below(NAT_MAX),
                Limit::Never,
            ]
        );
    }

    /// The cut and the summarizer's answer run in the compiled core: the
    /// walk reaches 50 tokens at the fourth contribution, a candidate; an
    /// error answer fails with its message.
    #[test]
    fn the_cut_and_the_answer_run_in_the_compiled_core() {
        let user = [Fact::User];
        let calling = [Fact::Assistant {
            stop: StopReason::ToolUse,
            calls: vec![1],
        }];
        let result = [Fact::Result { call: 1 }];
        let answer = [Fact::Assistant {
            stop: StopReason::Stop,
            calls: vec![],
        }];
        let contributions = [
            Contribution {
                tokens: 100,
                facts: &user,
            },
            Contribution {
                tokens: 10,
                facts: &calling,
            },
            Contribution {
                tokens: 10,
                facts: &result,
            },
            Contribution {
                tokens: 100,
                facts: &user,
            },
            Contribution {
                tokens: 10,
                facts: &answer,
            },
        ];
        assert_eq!(
            (
                cut(false, Limit::Below(50), &contributions),
                summary(Answer {
                    stop: StopReason::Error,
                    calls: false,
                    text: false,
                    error: Some("boom"),
                }),
            ),
            (
                Some(3),
                Outcome::Failed("Summarization failed: boom".to_owned())
            )
        );
    }
}
