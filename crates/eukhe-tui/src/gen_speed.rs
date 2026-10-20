//! The status line's generation speed (`terminal.showSpeed`): the phase of
//! the model request that streams now (prefill until the first token, then
//! decode) and, after it, the rates of the last response.
//!
//! The live phase uses what the client sees: the turn start, the server's
//! prompt progress (llama.cpp), and the streamed message. The summary uses
//! what the provider reported: the usage and the stream marks
//! (`ResponseTiming`) on the settled message.

use std::time::{Duration, Instant};

use eukhe_types::ai::{AssistantMessage, StopReason, Usage};
use eukhe_types::pi_ai::{PromptProgress, ResponseTiming};
use eukhe_types::token_estimate::chars_to_tokens;

/// The decode rate shows after this much decode time; before it, the rate
/// of the first deltas is noise.
const DECODE_RATE_AFTER: Duration = Duration::from_millis(250);

/// TS `formatRate`: whole numbers at 100 tok/s and above, one decimal
/// below.
pub(crate) fn format_rate(tokens_per_second: f64) -> String {
    if tokens_per_second >= 100.0 {
        format!("{tokens_per_second:.0}")
    } else {
        format!("{tokens_per_second:.1}")
    }
}

/// Seconds for a span: two decimals under 1 s, one under 10 s, whole above.
fn format_seconds(span: Duration) -> String {
    let seconds = span.as_secs_f64();
    if seconds < 1.0 {
        format!("{seconds:.2}s")
    } else if seconds < 10.0 {
        format!("{seconds:.1}s")
    } else {
        format!("{seconds:.0}s")
    }
}

/// `tokens` over `span` per second; `None` for an empty span.
fn per_second(tokens: u64, span: Duration) -> Option<f64> {
    let seconds = span.as_secs_f64();
    (seconds > 0.0).then(|| tokens as f64 / seconds)
}

/// What one settled response gives the rates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct SpeedSample {
    /// Prompt tokens the server processed: the input plus the cache write
    /// (the wire `input` excludes the cache).
    pub(crate) uncached: u64,
    /// Prompt tokens the server read from its cache.
    pub(crate) cache_read: u64,
    /// Output tokens.
    pub(crate) output: u64,
    /// From the request start to the first token.
    pub(crate) ttft: Duration,
    /// From the first token to the last token.
    pub(crate) decode: Duration,
}

impl SpeedSample {
    /// The sample of `usage` with the stream marks of `timing`; `None`
    /// without a first token.
    pub(crate) fn of(usage: &Usage, timing: &ResponseTiming) -> Option<Self> {
        let first = timing.first_token_ms?;
        let last = timing.last_token_ms.unwrap_or(first).max(first);
        Some(Self {
            uncached: usage.input.saturating_add(usage.cache_write),
            cache_read: usage.cache_read,
            output: usage.output,
            ttft: Duration::from_millis(first),
            decode: Duration::from_millis(last - first),
        })
    }
}

/// The prefill side of a [`ResponseSpeed`].
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Prefill {
    /// Uncached prompt tokens per second over the time to first token.
    Rate(f64),
    /// The cache gave 95 % or more of the prompt: no rate to show.
    Cached,
    /// The provider reported no prompt tokens.
    Unknown,
}

/// The rates of one response.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ResponseSpeed {
    /// From the request start to the first token.
    pub ttft: Duration,
    pub prefill: Prefill,
    /// Output tokens after the first one, per second of the time after the
    /// first token; `None` for fewer than two tokens or no decode time.
    pub decode_tokens_per_second: Option<f64>,
}

impl ResponseSpeed {
    /// The rates of `sample`: prefill = uncached prompt tokens / TTFT,
    /// decode = (output - 1) / (last token - first token).
    pub(crate) fn of(sample: SpeedSample) -> Self {
        let prompt = sample.uncached.saturating_add(sample.cache_read);
        let prefill = if prompt == 0 {
            Prefill::Unknown
        } else if sample.uncached.saturating_mul(20) <= prompt {
            Prefill::Cached
        } else {
            per_second(sample.uncached, sample.ttft).map_or(Prefill::Unknown, Prefill::Rate)
        };
        let decode_tokens_per_second = (sample.output >= 2)
            .then(|| per_second(sample.output - 1, sample.decode))
            .flatten();
        Self {
            ttft: sample.ttft,
            prefill,
            decode_tokens_per_second,
        }
    }

    /// `prefill X tok/s (TTFT Ys) · decode Z tok/s`; `cached` in place of
    /// the prefill rate when the cache gave nearly all of the prompt.
    pub(crate) fn summary(&self) -> String {
        let ttft = format_seconds(self.ttft);
        let prefill = match self.prefill {
            Prefill::Rate(rate) => format!("prefill {} tok/s (TTFT {ttft})", format_rate(rate)),
            Prefill::Cached => format!("prefill cached (TTFT {ttft})"),
            Prefill::Unknown => format!("TTFT {ttft}"),
        };
        match self.decode_tokens_per_second {
            Some(rate) => format!("{prefill} · decode {} tok/s", format_rate(rate)),
            None => prefill,
        }
    }
}

/// Where the model request of the turn is, for the status line.
#[derive(Debug, Clone, PartialEq)]
pub enum SpeedPhase {
    /// The request is out and no token came back yet.
    Prefill {
        since: Instant,
        /// The server's own progress through the prompt (llama.cpp).
        progress: Option<PromptProgress>,
        /// The prompt tokens the cache likely does not hold: the last
        /// response's output and what the session added since, at the one
        /// token estimate ([`chars_to_tokens`]). `None` before the first
        /// response.
        uncached_estimate: Option<u64>,
    },
    /// Tokens stream.
    Decode {
        since: Instant,
        first_token: Instant,
        /// Output tokens so far: the provider's count when it streams one,
        /// else the content at the one token estimate.
        tokens: u64,
    },
    /// The last response settled.
    Done(ResponseSpeed),
}

impl SpeedPhase {
    /// The status line text at `now`.
    #[must_use]
    pub fn text(&self, now: Instant) -> String {
        match self {
            Self::Prefill {
                progress: Some(progress),
                ..
            } => format!("prefill {}/{} tokens", progress.processed, progress.total),
            Self::Prefill {
                since,
                progress: None,
                uncached_estimate,
            } => {
                let elapsed = format!(
                    "{:.1}s",
                    now.saturating_duration_since(*since).as_secs_f64()
                );
                match uncached_estimate {
                    Some(tokens) => format!(
                        "prefill {elapsed} (~{} tok)",
                        crate::status_line::format_count(*tokens)
                    ),
                    None => format!("prefill {elapsed}"),
                }
            }
            Self::Decode {
                first_token,
                tokens,
                ..
            } => {
                let elapsed = now.saturating_duration_since(*first_token);
                match (elapsed >= DECODE_RATE_AFTER)
                    .then(|| per_second(tokens.saturating_sub(1), elapsed))
                    .flatten()
                {
                    Some(rate) => format!("decode {} tok/s", format_rate(rate)),
                    None => "decode".to_string(),
                }
            }
            Self::Done(speed) => speed.summary(),
        }
    }
}

/// The phase machine behind [`SpeedPhase`], fed by the session's events.
#[derive(Debug, Default)]
pub(crate) struct SpeedClock {
    phase: Option<SpeedPhase>,
    /// Prompt characters (UTF-16 code units) the session added since the
    /// last response (the user's text, tool results).
    added_chars: u64,
    /// The output tokens of the last response; `None` before the first.
    last_output: Option<u64>,
}

impl SpeedClock {
    /// The phase to show; `None` before the first request and after a
    /// failed one.
    pub(crate) fn phase(&self) -> Option<&SpeedPhase> {
        self.phase.as_ref()
    }

    /// A turn started: its model request goes out now.
    pub(crate) fn request_started(&mut self, now: Instant) {
        self.phase = Some(SpeedPhase::Prefill {
            since: now,
            progress: None,
            uncached_estimate: self
                .last_output
                .map(|output| output + chars_to_tokens(self.added_chars)),
        });
    }

    /// The session added `chars` characters (UTF-16 code units) of prompt
    /// (user text, a tool result) for the next request.
    pub(crate) fn prompt_added(&mut self, chars: u64) {
        self.added_chars = self.added_chars.saturating_add(chars);
        if let (
            Some(SpeedPhase::Prefill {
                uncached_estimate: Some(estimate),
                ..
            }),
            Some(output),
        ) = (&mut self.phase, self.last_output)
        {
            *estimate = output + chars_to_tokens(self.added_chars);
        }
    }

    /// The server reported its progress through the prompt.
    pub(crate) fn prompt_progress(&mut self, update: PromptProgress) {
        if let Some(SpeedPhase::Prefill { progress, .. }) = &mut self.phase {
            *progress = Some(update);
        }
    }

    /// The streaming message has `tokens` output tokens at `now` (zero
    /// while it shows no content yet).
    pub(crate) fn streamed(&mut self, now: Instant, tokens: u64) {
        match &mut self.phase {
            Some(SpeedPhase::Prefill { since, .. }) if tokens > 0 => {
                self.phase = Some(SpeedPhase::Decode {
                    since: *since,
                    first_token: now,
                    tokens,
                });
            }
            Some(SpeedPhase::Decode {
                tokens: current, ..
            }) => *current = (*current).max(tokens),
            Some(SpeedPhase::Prefill { .. } | SpeedPhase::Done(_)) | None => {}
        }
    }

    /// The response settled at `now`: the rates from the provider's usage
    /// and stream marks, else from what the client saw. A failed or
    /// aborted response shows nothing.
    pub(crate) fn settled(&mut self, message: &AssistantMessage, now: Instant) {
        self.added_chars = 0;
        self.last_output = Some(message.usage.output);
        let sample = match message.stop_reason {
            StopReason::Error | StopReason::Aborted => None,
            StopReason::Stop | StopReason::Length | StopReason::ToolUse => message
                .timing
                .as_ref()
                .and_then(|timing| SpeedSample::of(&message.usage, timing))
                .or_else(|| match self.phase {
                    Some(SpeedPhase::Decode {
                        since, first_token, ..
                    }) => Some(SpeedSample {
                        uncached: message
                            .usage
                            .input
                            .saturating_add(message.usage.cache_write),
                        cache_read: message.usage.cache_read,
                        output: message.usage.output,
                        ttft: first_token.saturating_duration_since(since),
                        decode: now.saturating_duration_since(first_token),
                    }),
                    Some(SpeedPhase::Prefill { .. } | SpeedPhase::Done(_)) | None => None,
                }),
        };
        self.phase = sample.map(|sample| SpeedPhase::Done(ResponseSpeed::of(sample)));
    }
}

#[cfg(test)]
mod tests;
