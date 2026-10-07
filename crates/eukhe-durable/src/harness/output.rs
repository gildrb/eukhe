//! Bounded tool output and adaptive progress commits. Port of
//! `harness/output.ts`.

use std::future::Future;
use std::sync::{Arc, Mutex, PoisonError};

use futures::future::BoxFuture;
use tokio::sync::{oneshot, Notify};
use tokio::time::{Duration, Instant};

use crate::env::{ShellOutputSkip, Utf8Decoder};
use crate::harness::types::{OutputRetain, ToolOutputChunk};
use crate::session::SessionError;

/// Retention limits of one tool's output.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OutputLimits {
    pub max_bytes: usize,
    pub max_lines: usize,
    pub retain: OutputRetain,
}

/// Retained output and what the limits dropped.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoundedOutput {
    pub text: String,
    pub dropped_bytes: usize,
    pub dropped_lines: usize,
}

/// An exact slice of the input within the limits, and what it left out.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OutputSlice {
    pub text: String,
    pub bytes: usize,
    pub dropped_bytes: usize,
    pub dropped_lines: usize,
}

const NEWLINE: u8 = 0x0a;

fn is_invalid_output(c: char) -> bool {
    matches!(c, '\x00'..='\x08' | '\x0b'..='\x1f' | '\u{fff9}'..='\u{fffb}')
}

/// Remove control characters that break display and transcripts; tabs and
/// newlines stay.
#[must_use]
pub fn sanitize_output(text: &str) -> String {
    text.chars().filter(|&c| !is_invalid_output(c)).collect()
}

/// Bound `text` to whole lines within the limits: the first lines for
/// `head`, the last lines for `tail`. The result is an exact slice, trailing
/// newline included. A single line longer than `max_bytes` is cut at the
/// byte limit on a character boundary.
#[must_use]
pub fn bound_output(text: &str, limits: &OutputLimits) -> OutputSlice {
    let bytes = text.as_bytes();
    let (from, to) = match limits.retain {
        OutputRetain::Head => head_range(bytes, limits),
        OutputRetain::Tail => tail_range(bytes, limits),
    };
    let kept = &text[from..to];
    OutputSlice {
        text: kept.to_owned(),
        bytes: kept.len(),
        dropped_bytes: bytes.len() - kept.len(),
        dropped_lines: line_count(bytes) - line_count(kept.as_bytes()),
    }
}

fn index_of(bytes: &[u8], from: usize) -> Option<usize> {
    bytes
        .get(from..)?
        .iter()
        .position(|&b| b == NEWLINE)
        .map(|i| i + from)
}

/// JS `lastIndexOf(NEWLINE, from)`: searches at or before `from` (clamped).
fn last_index_of(bytes: &[u8], from: usize) -> Option<usize> {
    if bytes.is_empty() {
        return None;
    }
    let end = from.min(bytes.len() - 1);
    bytes[..=end].iter().rposition(|&b| b == NEWLINE)
}

fn head_range(bytes: &[u8], limits: &OutputLimits) -> (usize, usize) {
    if limits.max_lines == 0 || limits.max_bytes == 0 {
        return (0, 0);
    }
    let mut end = bytes.len();
    let mut lines = 0;
    let mut index = index_of(bytes, 0);
    while let Some(at) = index {
        lines += 1;
        if lines == limits.max_lines {
            end = at + 1;
            break;
        }
        index = index_of(bytes, at + 1);
    }
    if end > limits.max_bytes {
        end = match last_index_of(bytes, limits.max_bytes - 1) {
            None => character_end(bytes, limits.max_bytes),
            Some(newline) => newline + 1,
        };
    }
    (0, end)
}

fn tail_range(bytes: &[u8], limits: &OutputLimits) -> (usize, usize) {
    let length = bytes.len();
    if limits.max_lines == 0 || limits.max_bytes == 0 {
        return (length, length);
    }
    // A trailing newline ends the last line rather than starting another.
    let last = if bytes.last() == Some(&NEWLINE) {
        length.checked_sub(2)
    } else {
        length.checked_sub(1)
    };
    let mut start = 0;
    let mut lines = 1;
    let mut index = last.and_then(|last| last_index_of(bytes, last));
    while let Some(at) = index {
        if lines == limits.max_lines {
            start = at + 1;
            break;
        }
        lines += 1;
        index = if at == 0 {
            None
        } else {
            last_index_of(bytes, at - 1)
        };
    }
    if length - start > limits.max_bytes {
        let from = length - limits.max_bytes;
        // JS `indexOf(NEWLINE, from - 1)`; a negative start searches from 0.
        let newline = index_of(bytes, from.saturating_sub(1));
        // The first line starting inside the byte window, or a cut of the last
        // line when it alone is too long.
        start = match newline {
            Some(newline) if newline + 1 < length => newline + 1,
            _ => character_start(bytes, from),
        };
    }
    (start, length)
}

/// The last character boundary at or before `index`.
#[must_use]
pub fn character_end(bytes: &[u8], index: usize) -> usize {
    let mut end = index;
    while end > 0 && (bytes.get(end).copied().unwrap_or(0) & 0xc0) == 0x80 {
        end -= 1;
    }
    end
}

/// The first character boundary at or after `index`.
fn character_start(bytes: &[u8], index: usize) -> usize {
    let mut start = index;
    while start < bytes.len() && (bytes[start] & 0xc0) == 0x80 {
        start += 1;
    }
    start
}

fn line_count(bytes: &[u8]) -> usize {
    if bytes.is_empty() {
        return 0;
    }
    #[expect(clippy::naive_bytecount, reason = "no dependency for one byte count")]
    let newlines = bytes.iter().filter(|&&b| b == NEWLINE).count();
    newlines + usize::from(bytes.last() != Some(&NEWLINE))
}

#[derive(Debug, Clone)]
struct StoredChunk {
    text: String,
    bytes: usize,
    newlines: usize,
}

/// Bounded running output of one tool call. Accepting a chunk costs time
/// proportional to the chunk: head retention stops storing once the window
/// is full, and tail retention drops stored text the window no longer needs
/// when it snapshots. Counts of the whole stream are kept so the dropped
/// totals stay exact.
#[derive(Debug, Clone)]
pub struct OutputBuffer {
    limits: OutputLimits,
    /// Decoder of byte chunks. A string chunk or a skip ends an incomplete
    /// character of earlier bytes (it becomes U+FFFD); the next byte chunk
    /// then starts a new character. Only a byte-order mark at the very start
    /// of the output is dropped, never a U+FEFF later in it.
    decoder: Utf8Decoder,
    started: bool,
    /// Stored chunks: for head the start of the stream, for tail a suffix
    /// that still contains the next window.
    chunks: Vec<StoredChunk>,
    stored_bytes: usize,
    stored_newlines: usize,
    full: bool,
    total_bytes: usize,
    total_newlines: usize,
    ends_with_newline: bool,
}

/// Error of [`OutputBuffer::push`] with a skip under head retention.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("Skipped output requires tail retention")]
pub struct SkipRequiresTail;

impl OutputBuffer {
    #[must_use]
    pub fn new(limits: OutputLimits) -> Self {
        Self {
            limits,
            decoder: Utf8Decoder::new(),
            started: false,
            chunks: Vec::new(),
            stored_bytes: 0,
            stored_newlines: 0,
            full: false,
            total_bytes: 0,
            total_newlines: 0,
            ends_with_newline: true,
        }
    }

    /// Bytes currently held; bounded by the limits plus one chunk. Only the
    /// tests read it (TS exposes it as a getter no caller uses).
    #[cfg(test)]
    #[must_use]
    pub fn stored_bytes(&self) -> usize {
        self.stored_bytes
    }

    /// Accept a chunk; returns whether anything was accepted. `skipped` is
    /// output omitted right before the chunk, which must be more than the
    /// tail window by at least one byte or line (`ShellOutputInfo.skipped`);
    /// only tail retention accepts it.
    ///
    /// # Errors
    /// [`SkipRequiresTail`] for a skip under head retention.
    pub fn push(
        &mut self,
        chunk: ToolOutputChunk<'_>,
        skipped: Option<&ShellOutputSkip>,
    ) -> Result<bool, SkipRequiresTail> {
        let is_text = matches!(chunk, ToolOutputChunk::Text(_));
        // Bytes of an incomplete character from an earlier byte chunk come first.
        let pending = if is_text || skipped.is_some() {
            self.decoder.finish()
        } else {
            String::new()
        };
        let mut text = match chunk {
            ToolOutputChunk::Text(text) => text.to_owned(),
            ToolOutputChunk::Bytes(bytes) => self.decoder.decode_chunk(bytes),
        };
        let first = !self.started && pending.is_empty() && skipped.is_none();
        if !pending.is_empty() || !text.is_empty() || skipped.is_some() {
            self.started = true;
        }
        if first && !is_text && text.starts_with('\u{feff}') {
            text.drain(..'\u{feff}'.len_utf8());
        }
        let Some(skipped) = skipped else {
            return Ok(self.accept(pending + &text));
        };
        if self.limits.retain != OutputRetain::Tail {
            return Err(SkipRequiresTail);
        }
        self.accept(pending);
        self.skip(skipped);
        self.accept(text);
        Ok(true)
    }

    /// Count omitted output; nothing stored before it can be in the window
    /// once the text after it arrives.
    fn skip(&mut self, skipped: &ShellOutputSkip) {
        if skipped.bytes == 0 {
            return;
        }
        self.total_bytes += usize::try_from(skipped.bytes).unwrap_or(usize::MAX);
        self.total_newlines += usize::try_from(skipped.newlines).unwrap_or(usize::MAX);
        self.ends_with_newline = skipped.ends_with_newline;
        self.chunks.clear();
        self.stored_bytes = 0;
        self.stored_newlines = 0;
    }

    /// Flush an incomplete trailing character as a replacement character;
    /// call when the stream ends.
    pub fn end(&mut self) {
        let text = self.decoder.finish();
        self.accept(text);
    }

    fn accept(&mut self, text: String) -> bool {
        if text.is_empty() {
            return false;
        }
        let bytes = text.len();
        let newlines = count_newlines(&text);
        self.total_bytes += bytes;
        self.total_newlines += newlines;
        self.ends_with_newline = text.ends_with('\n');
        if self.full {
            return true;
        }
        self.chunks.push(StoredChunk {
            text,
            bytes,
            newlines,
        });
        self.stored_bytes += bytes;
        self.stored_newlines += newlines;
        if self.limits.retain == OutputRetain::Head {
            // Nothing past a full window is ever needed.
            self.full = self.stored_bytes > self.limits.max_bytes
                || self.stored_newlines >= self.limits.max_lines;
            return true;
        }
        // Drop leading chunks while the rest still holds more than a window:
        // more than `max_bytes` bytes or `max_lines` newlines, plus one, so the
        // window's line start can still be found. Each chunk is dropped once.
        let mut drop = 0;
        while self.chunks.len() - drop > 1 {
            let first = &self.chunks[drop];
            let bytes_after = self.stored_bytes - first.bytes;
            let newlines_after = self.stored_newlines - first.newlines;
            if bytes_after <= self.limits.max_bytes.saturating_add(1)
                && newlines_after <= self.limits.max_lines.saturating_add(1)
            {
                break;
            }
            drop += 1;
            self.stored_bytes = bytes_after;
            self.stored_newlines = newlines_after;
        }
        self.chunks.drain(..drop);
        true
    }

    /// Retained, sanitized output and what the limits dropped from the whole
    /// stream.
    pub fn snapshot(&mut self) -> BoundedOutput {
        let stored = if self.chunks.len() == 1 {
            self.chunks[0].text.clone()
        } else {
            self.chunks
                .iter()
                .map(|chunk| chunk.text.as_str())
                .collect::<String>()
        };
        let kept = bound_output(&stored, &self.limits);
        let stored_lines = lines(
            self.stored_newlines,
            stored.is_empty() || stored.ends_with('\n'),
        );
        let kept_lines = stored_lines - kept.dropped_lines;
        // Tail windows never reach back before this one, but finding a later
        // window's first line needs what precedes it: keep the shortest suffix
        // longer than the window by a byte or a line, as `accept` does.
        let tail = self.limits.retain == OutputRetain::Tail;
        if tail || self.chunks.len() > 1 {
            let text = if tail {
                tail_margin(&stored, &self.limits).to_owned()
            } else {
                stored
            };
            let bytes = if tail { text.len() } else { self.stored_bytes };
            let newlines = count_newlines(&text);
            self.chunks = if text.is_empty() {
                Vec::new()
            } else {
                vec![StoredChunk {
                    text,
                    bytes,
                    newlines,
                }]
            };
            self.stored_bytes = bytes;
            self.stored_newlines = self.chunks.first().map_or(0, |chunk| chunk.newlines);
        }
        BoundedOutput {
            text: sanitize_output(&kept.text),
            dropped_bytes: self.total_bytes - kept.bytes,
            dropped_lines: lines(self.total_newlines, self.ends_with_newline) - kept_lines,
        }
    }
}

/// The shortest suffix of `text` with more than `max_bytes` bytes or more
/// than `max_lines` newlines, or all of it. The tail window of any text that
/// ends with this suffix, followed by anything, is the same as of `text`
/// followed by it.
fn tail_margin<'a>(text: &'a str, limits: &OutputLimits) -> &'a str {
    let bytes = text.as_bytes();
    let byte_start = if bytes.len() > limits.max_bytes {
        character_end(bytes, bytes.len() - limits.max_bytes - 1)
    } else {
        0
    };
    let mut line_start = 0;
    let mut newlines = 0;
    let mut index = bytes.iter().rposition(|&b| b == NEWLINE);
    while let Some(at) = index {
        newlines += 1;
        if newlines > limits.max_lines {
            line_start = at;
            break;
        }
        if at == 0 {
            break;
        }
        index = last_index_of(bytes, at - 1);
    }
    &text[byte_start.max(line_start)..]
}

/// Lines of text with `newlines` newlines; a final unterminated line counts.
fn lines(newlines: usize, terminated: bool) -> usize {
    newlines + usize::from(!terminated)
}

fn count_newlines(text: &str) -> usize {
    text.bytes().filter(|&b| b == NEWLINE).count()
}

/// Each progress commit also buys a pause proportional to what it wrote.
pub const PROGRESS_BYTES_PER_SECOND: f64 = 100.0 * 1024.0;

/// One commit of [`Progress`]: called synchronously when the commit starts
/// (so it can capture state), its future resolves with the bytes written.
pub type ProgressWrite =
    Box<dyn Fn() -> BoxFuture<'static, Result<usize, SessionError>> + Send + Sync>;

/// A `mark_and_wait` waiter; [`Progress::stop`] hands the unsettled ones back.
pub type ProgressWaiter = oneshot::Sender<Result<(), SessionError>>;

struct ProgressState {
    waiters: Vec<ProgressWaiter>,
    timer: Option<tokio::task::JoinHandle<()>>,
    in_flight: bool,
    next_at: Option<Instant>,
    dirty: bool,
    stopped: bool,
}

struct ProgressInner {
    write: ProgressWrite,
    on_error: Box<dyn Fn(SessionError) + Send + Sync>,
    min_interval_ms: f64,
    state: Mutex<ProgressState>,
    settled: Notify,
}

/// Adaptive progress commits: the first change after an idle period commits
/// at once; each commit then delays the next by at least `min_interval_ms`
/// and by its written size at 100 KiB/s. At most one commit is in flight;
/// changes made meanwhile coalesce into the next one.
#[derive(Clone)]
pub struct Progress {
    inner: Arc<ProgressInner>,
}

impl Progress {
    pub fn new(
        write: ProgressWrite,
        on_error: Box<dyn Fn(SessionError) + Send + Sync>,
        min_interval_ms: f64,
    ) -> Self {
        Self {
            inner: Arc::new(ProgressInner {
                write,
                on_error,
                min_interval_ms,
                state: Mutex::new(ProgressState {
                    waiters: Vec::new(),
                    timer: None,
                    in_flight: false,
                    next_at: None,
                    dirty: false,
                    stopped: false,
                }),
                settled: Notify::new(),
            }),
        }
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, ProgressState> {
        self.inner
            .state
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
    }

    /// Schedule a commit.
    pub fn mark(&self) {
        self.lock().dirty = true;
        self.schedule();
    }

    /// Schedule a commit; the future settles with the commit that includes
    /// this change.
    pub fn mark_and_wait(&self) -> impl Future<Output = Result<(), SessionError>> + Send {
        let (sender, receiver) = oneshot::channel();
        self.lock().waiters.push(sender);
        self.mark();
        async move {
            // A dropped waiter means its owner discarded it without settling.
            receiver.await.unwrap_or(Ok(()))
        }
    }

    /// Stop committing and wait for the commit in flight; returns the
    /// waiters the final commit must settle.
    pub async fn stop(&self) -> Vec<ProgressWaiter> {
        {
            let mut state = self.lock();
            state.stopped = true;
            if let Some(timer) = state.timer.take() {
                timer.abort();
            }
        }
        loop {
            let notified = self.inner.settled.notified();
            tokio::pin!(notified);
            notified.as_mut().enable();
            if !self.lock().in_flight {
                break;
            }
            notified.await;
        }
        std::mem::take(&mut self.lock().waiters)
    }

    fn schedule(&self) {
        let wait = {
            let state = self.lock();
            if state.stopped || state.timer.is_some() || state.in_flight {
                return;
            }
            state
                .next_at
                .and_then(|at| at.checked_duration_since(Instant::now()))
                .filter(|wait| !wait.is_zero())
        };
        let Some(wait) = wait else {
            self.flush();
            return;
        };
        let progress = self.clone();
        let mut state = self.lock();
        state.timer = Some(tokio::spawn(async move {
            tokio::time::sleep(wait).await;
            progress.lock().timer = None;
            progress.flush();
        }));
    }

    fn flush(&self) {
        let waiters = {
            let mut state = self.lock();
            if state.stopped || !state.dirty {
                return;
            }
            state.dirty = false;
            state.in_flight = true;
            std::mem::take(&mut state.waiters)
        };
        let started = Instant::now();
        let write = (self.inner.write)();
        let progress = self.clone();
        tokio::spawn(async move {
            let result = write.await;
            let min = progress.inner.min_interval_ms;
            match result {
                Ok(bytes) => {
                    #[allow(clippy::cast_precision_loss)]
                    // reason: JS number arithmetic on byte counts
                    let pause = min.max(bytes as f64 * 1000.0 / PROGRESS_BYTES_PER_SECOND);
                    progress.lock().next_at = Some(started + duration_ms(pause));
                    for waiter in waiters {
                        let _ = waiter.send(Ok(()));
                    }
                }
                Err(error) => {
                    progress.lock().next_at = Some(started + duration_ms(min));
                    for waiter in waiters {
                        let _ = waiter.send(Err(error.clone()));
                    }
                    (progress.inner.on_error)(error);
                }
            }
            let dirty = {
                let mut state = progress.lock();
                state.in_flight = false;
                state.dirty
            };
            progress.inner.settled.notify_waiters();
            if dirty {
                progress.schedule();
            }
        });
    }
}

fn duration_ms(ms: f64) -> Duration {
    Duration::from_secs_f64(ms.max(0.0) / 1000.0)
}

#[cfg(test)]
mod tests;
