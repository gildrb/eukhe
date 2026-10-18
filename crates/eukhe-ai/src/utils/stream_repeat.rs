//! eukhe addition: the repetition guard of chat streams (`bend/infer.bend`
//! §4, `guard`).
//!
//! A model caught in a loop emits the same line over and over until its
//! output budget runs out. Every chat stream `Models` dispatches is watched
//! in one place, whatever its provider: the stream's text and thinking are
//! read as chunks, and the chunk that makes one chunk come `k` times in a
//! row aborts the request and ends the stream with a
//! [`StreamFailureKind::StreamRepeating`](eukhe_types::pi_ai::StreamFailureKind)
//! error, which the caller's retry policy re-issues like a stall.
//!
//! A chunk is one complete output line of a text or thinking block: the
//! text up to (not including) a `\n`. A partial last line is not a chunk
//! until its newline arrives, and a line that is empty or only whitespace
//! is not a chunk. A line longer than [`MAX_CHUNK_BYTES`] ends a chunk at
//! that length (on a character boundary), and the rest of the line starts
//! the next one: a loop with no newline (`abab…`) is still cut, and a
//! guard never buffers more than one chunk per block. Each content block
//! keeps its own partial line, so interleaved blocks never merge lines;
//! the complete lines of every block count in one run, in arrival order.

use std::collections::HashMap;

use eukhe_chord::context::{AbortController, AbortSignal};
use eukhe_types::pi_ai::AssistantMessageEvent;

use super::stream_failure::{stream_repeating_failure, ProviderError};
use crate::types::ProviderRequestOptions;

/// Default of `ProviderRequestOptions::stream_repeat_limit`: 64 equal lines
/// in a row, far beyond what real output repeats (table rows and the like
/// differ, and blank lines do not count).
pub const DEFAULT_STREAM_REPEAT_LIMIT: u32 = 64;

/// The longest chunk, in bytes: a longer line is cut into chunks of at
/// most this length.
pub const MAX_CHUNK_BYTES: usize = 4096;

/// Where a [`RepetitionGuard`] cut its stream: model `CutAt{at}`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RepetitionCut {
    /// The chunks read, including the one that completed the run.
    pub chunks: u64,
    /// The repeated chunk.
    pub line: String,
}

/// The repetition guard of one stream: model `guard(xs, k)`, fed one delta
/// at a time. It counts how many times in a row the same chunk came; the
/// chunk that brings the run to `k` cuts the stream (a `k` of at most 1
/// cuts at the first chunk). A stream that never repeats one chunk `k`
/// times in a row is never cut. Stop feeding it at the first cut.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RepetitionGuard {
    limit: u32,
    /// The partial last line of each content block, by content index.
    partial: HashMap<usize, String>,
    previous: Option<String>,
    run: u32,
    chunks: u64,
}

impl RepetitionGuard {
    /// A guard that cuts at `limit` equal chunks in a row.
    #[must_use]
    pub fn new(limit: u32) -> Self {
        Self {
            limit,
            partial: HashMap::new(),
            previous: None,
            run: 0,
            chunks: 0,
        }
    }

    /// The number of equal chunks in a row that cuts the stream.
    #[must_use]
    pub const fn limit(&self) -> u32 {
        self.limit
    }

    /// Read `delta`, the next output of content block `content_index`;
    /// returns the cut when one of the chunks it completes makes the run.
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
            self.run = if self.previous.as_deref() == Some(line.as_str()) {
                self.run.saturating_add(1)
            } else {
                1
            };
            if self.run >= self.limit {
                return Some(RepetitionCut {
                    chunks: self.chunks,
                    line,
                });
            }
            self.previous = Some(line);
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
            "stream repetition guard cut the stream"
        );
        self.cut.abort(None);
        Some(ProviderError::StreamFailure(stream_repeating_failure(
            limit, &cut.line,
        )))
    }
}

#[cfg(test)]
mod tests;
