//! eukhe addition: the repetition guard of chat streams (`bend/infer.bend`
//! §4, `guard`).
//!
//! A model caught in a loop emits the same line, or the same block of
//! lines, over and over until its output budget runs out. Every chat stream
//! `Models` dispatches is watched in one place, whatever its provider: the
//! stream's text and thinking are read as chunks, and the chunk that makes
//! the last `k` chunks periodic, with a period of at most `k / 4` chunks (at
//! least 1: four full repetitions of the cycle), aborts the request and ends
//! the stream with a
//! [`StreamFailureKind::StreamRepeating`](eukhe_types::pi_ai::StreamFailureKind)
//! error, which the caller's retry policy re-issues like a stall. Period 1
//! is one chunk `k` times in a row.
//!
//! A chunk is one complete output line of a text or thinking block: the
//! text up to (not including) a `\n`. A partial last line is not a chunk
//! until its newline arrives, and a line that is empty or only whitespace
//! is not a chunk. A line longer than [`MAX_CHUNK_BYTES`] ends a chunk at
//! that length (on a character boundary), and the rest of the line starts
//! the next one: a loop with no newline (`abab…`) is still cut, and a
//! guard never buffers more than one partial chunk per block. Each content
//! block keeps its own partial line, so interleaved blocks never merge
//! lines; the complete lines of every block count in one sequence, in
//! arrival order.
//!
//! The guard keeps the last `k / 4` chunks and one counter per period: the
//! counter of period `p` is how many chunks in a row, up to the newest,
//! each equal the chunk `p` before it. The last `k` chunks are periodic
//! with period `p` exactly when that counter is at least `k - p`. Its
//! memory is thus bounded by `k / 4` chunks, whatever the stream's length.

use std::collections::{HashMap, VecDeque};

use eukhe_chord::context::{AbortController, AbortSignal};
use eukhe_types::pi_ai::AssistantMessageEvent;

use super::stream_failure::{stream_repeating_failure, ProviderError};
use crate::types::ProviderRequestOptions;

/// Default of `ProviderRequestOptions::stream_repeat_limit`: a window of 64
/// lines that repeats with a period of at most 16 lines (one line 64 times
/// in a row, or a block of up to 16 lines four times), far beyond what real
/// output repeats (table rows and the like differ, and blank lines do not
/// count).
pub const DEFAULT_STREAM_REPEAT_LIMIT: u32 = 64;

/// The longest chunk, in bytes: a longer line is cut into chunks of at
/// most this length.
pub const MAX_CHUNK_BYTES: usize = 4096;

/// Where a [`RepetitionGuard`] cut its stream: model `CutAt{at}`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RepetitionCut {
    /// The chunks read, including the one that completed the window.
    pub chunks: u64,
    /// The shortest period of the window, in chunks (1: one chunk repeated).
    pub period: u32,
    /// The chunk that completed the window.
    pub line: String,
}

/// The repetition guard of one stream: model `guard(xs, k)`, fed one delta
/// at a time. The chunk that makes the last `k` chunks periodic, with a
/// period of at most `max(1, k / 4)`, cuts the stream (a `k` of at most 1
/// cuts at the first chunk). A stream with no such window of `k` chunks is
/// never cut. Stop feeding it at the first cut.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RepetitionGuard {
    limit: u32,
    /// The longest period checked: `max(1, limit / 4)`.
    periods: usize,
    /// The partial last line of each content block, by content index.
    partial: HashMap<usize, String>,
    /// The last chunks, newest first; at most `periods` of them.
    history: VecDeque<String>,
    /// The counter of each period `q + 1`, for every period that has a
    /// chunk in `history` to compare with: how many chunks in a row, up to
    /// the newest, each equal the chunk `q + 1` before them (model
    /// `cycle(seen, q)`).
    counters: Vec<u32>,
    chunks: u64,
}

impl RepetitionGuard {
    /// A guard that cuts at a periodic window of `limit` chunks.
    #[must_use]
    pub fn new(limit: u32) -> Self {
        Self {
            limit,
            periods: usize::try_from((limit / 4).max(1)).unwrap_or(usize::MAX),
            partial: HashMap::new(),
            history: VecDeque::new(),
            counters: Vec::new(),
            chunks: 0,
        }
    }

    /// The number of chunks in the window that cuts the stream.
    #[must_use]
    pub const fn limit(&self) -> u32 {
        self.limit
    }

    /// Read `delta`, the next output of content block `content_index`;
    /// returns the cut when one of the chunks it completes makes the last
    /// `limit` chunks periodic.
    pub fn push(&mut self, content_index: usize, delta: &str) -> Option<RepetitionCut> {
        let mut rest = delta;
        loop {
            let partial = self.partial.entry(content_index).or_default();
            let room = MAX_CHUNK_BYTES.saturating_sub(partial.len());
            match rest.find('\n') {
                Some(end) if end <= room => {
                    partial.push_str(&rest[..end]);
                    rest = &rest[end + 1..];
                }
                Some(_) | None if rest.len() > room => {
                    // The line fills the chunk: end it at the last character
                    // boundary within the room.
                    let end = (0..=room)
                        .rev()
                        .find(|&at| rest.is_char_boundary(at))
                        .unwrap_or(0);
                    partial.push_str(&rest[..end]);
                    rest = &rest[end..];
                }
                Some(_) | None => {
                    partial.push_str(rest);
                    return None;
                }
            }
            let line = std::mem::take(partial);
            if line.trim().is_empty() {
                continue;
            }
            self.chunks += 1;
            // A period with no chunk that far back has a counter of 0; it
            // completes a window only when `limit <= period`, which a
            // period of at most `max(1, limit / 4)` allows only for a
            // `limit` of at most 1: that window is this chunk alone.
            let mut period = (self.limit <= 1).then_some(1);
            for ((seen, counter), p) in self.history.iter().zip(&mut self.counters).zip(1u32..) {
                *counter = if *seen == line {
                    counter.saturating_add(1)
                } else {
                    0
                };
                if period.is_none() && self.limit.saturating_sub(p) <= *counter {
                    period = Some(p);
                }
            }
            if let Some(period) = period {
                return Some(RepetitionCut {
                    chunks: self.chunks,
                    period,
                    line,
                });
            }
            if self.history.len() < self.periods {
                self.counters.push(0);
            } else {
                self.history.pop_back();
            }
            self.history.push_front(line);
        }
    }
}

/// The repetition guard of one chat stream: its guard, and the abort of its
/// request.
#[derive(Debug)]
pub(crate) struct StreamRepeat {
    guard: RepetitionGuard,
    cut: AbortController,
    /// The request signal the guard's signal wraps, held for the stream's
    /// life: an `AbortSignal::any` follows its sources weakly, so a wrapped
    /// signal nothing else holds (the stream-idle deadline's combined
    /// signal) would drop and stop relaying the caller's abort.
    #[expect(dead_code, reason = "held only to keep the wrapped signal alive")]
    wrapped: Option<AbortSignal>,
}

impl StreamRepeat {
    /// Arm the guard `request.stream_repeat_limit` selects (absent or `0`:
    /// [`DEFAULT_STREAM_REPEAT_LIMIT`]). The request's signal becomes one
    /// that also aborts on a cut.
    pub(crate) fn arm<M>(request: &mut ProviderRequestOptions<M>) -> Self {
        let limit = request
            .stream_repeat_limit
            .filter(|limit| *limit > 0)
            .unwrap_or(DEFAULT_STREAM_REPEAT_LIMIT);
        let cut = AbortController::new();
        let wrapped = request.signal.take();
        request.signal = Some(match &wrapped {
            Some(caller) => AbortSignal::any(&[caller.clone(), cut.signal()]),
            None => cut.signal(),
        });
        Self {
            guard: RepetitionGuard::new(limit),
            cut,
            wrapped,
        }
    }

    /// Read a stream event; on a cut, abort the request and return its
    /// failure.
    pub(crate) fn watch(&mut self, event: &AssistantMessageEvent) -> Option<ProviderError> {
        let cut = match event {
            AssistantMessageEvent::TextDelta {
                content_index,
                delta,
                ..
            }
            | AssistantMessageEvent::ThinkingDelta {
                content_index,
                delta,
                ..
            } => self.guard.push(*content_index, delta)?,
            AssistantMessageEvent::Start { .. }
            | AssistantMessageEvent::PromptProgress { .. }
            | AssistantMessageEvent::TextStart { .. }
            | AssistantMessageEvent::TextEnd { .. }
            | AssistantMessageEvent::ThinkingStart { .. }
            | AssistantMessageEvent::ThinkingEnd { .. }
            | AssistantMessageEvent::ToolCallStart { .. }
            | AssistantMessageEvent::ToolCallDelta { .. }
            | AssistantMessageEvent::ToolCallEnd { .. }
            | AssistantMessageEvent::Done { .. }
            | AssistantMessageEvent::Error { .. } => return None,
        };
        let limit = self.guard.limit();
        tracing::debug!(
            limit,
            chunks = cut.chunks,
            period = cut.period,
            "stream repetition guard cut the stream"
        );
        self.cut.abort(None);
        Some(ProviderError::StreamFailure(stream_repeating_failure(
            limit, cut.period, &cut.line,
        )))
    }
}

#[cfg(test)]
mod tests;
