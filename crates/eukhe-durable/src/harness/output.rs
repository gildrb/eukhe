//! Bounded tool output and adaptive progress publications. Port of
//! `harness/output.ts`.

use std::future::Future;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_bend::rules::bound;
use eukhe_types::output::{DEFAULT_MAX_BYTES, DEFAULT_MAX_LINES};
use futures::future::BoxFuture;
use tokio::sync::{oneshot, Notify};
use tokio::time::{Duration, Instant};

use crate::env::{ShellOutputSkip, Utf8Decoder};
use crate::harness::types::{OutputRetain, ToolOutputChunk};
use crate::session::SessionError;

/// Retention limits of one tool's output. The default is the default bound
/// (`DEFAULT_MAX_BYTES`, `DEFAULT_MAX_LINES`), keeping the head.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OutputLimits {
    pub max_bytes: usize,
    pub max_lines: usize,
    pub retain: OutputRetain,
}

#[expect(
    clippy::cast_possible_truncation,
    reason = "the default bound is 50 KiB and 2000 lines"
)]
impl Default for OutputLimits {
    fn default() -> Self {
        Self {
            max_bytes: DEFAULT_MAX_BYTES as usize,
            max_lines: DEFAULT_MAX_LINES as usize,
            retain: OutputRetain::Head,
        }
    }
}

/// Whether an output is bounded: the one limits value of a tool call, a
/// cell, or a job (docs/runtime.md S2). Truncation is on by default, with
/// the default limits; `Off` is the explicit opt-out, which keeps every
/// byte. Every truncation is visible: the bytes kept and the bytes counted
/// as dropped are every byte the output produced.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Truncation {
    /// Keep at most these limits; count the rest as dropped.
    On(OutputLimits),
    /// The explicit opt-out: keep all of the output.
    Off,
}

impl Default for Truncation {
    fn default() -> Self {
        Self::On(OutputLimits::default())
    }
}

impl Truncation {
    /// The byte cap: `None` for the opt-out.
    #[must_use]
    pub fn max_bytes(self) -> Option<usize> {
        match self {
            Self::On(limits) => Some(limits.max_bytes),
            Self::Off => None,
        }
    }

    /// The limits: `None` for the opt-out.
    #[must_use]
    pub fn limits(self) -> Option<OutputLimits> {
        match self {
            Self::On(limits) => Some(limits),
            Self::Off => None,
        }
    }
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

fn is_invalid_output(c: char) -> bool {
    matches!(c, '\x00'..='\x08' | '\x0b'..='\x1f' | '\u{fff9}'..='\u{fffb}')
}

/// Remove control characters that break display and transcripts; tabs and
/// newlines stay.
#[must_use]
pub fn sanitize_output(text: &str) -> String {
    text.chars().filter(|&c| !is_invalid_output(c)).collect()
}

/// The cap of `limits` in the compiled core.
fn cap_of(limits: &OutputLimits) -> bound::Cap {
    bound::Cap {
        bytes: limits.max_bytes,
        lines: limits.max_lines,
        tail: limits.retain == OutputRetain::Tail,
    }
}

/// Bound `text` to whole lines within the limits: the first lines for
/// `head`, the last lines for `tail`. The result is an exact slice, trailing
/// newline included. A single line longer than `max_bytes` is cut at the
/// byte limit on a character boundary. The compiled core decides the
/// window (`bend/bound.bend` `slice`).
#[must_use]
pub fn bound_output(text: &str, limits: &OutputLimits) -> OutputSlice {
    let window = bound::slice(text, cap_of(limits));
    let kept = &text[window.from..window.to];
    OutputSlice {
        text: kept.to_owned(),
        bytes: kept.len(),
        dropped_bytes: window.dropped_bytes,
        dropped_lines: window.dropped_lines,
    }
}

/// Bounded running output of one tool call. Accepting a chunk costs time
/// proportional to the chunk: the compiled core (`bend/bound.bend`, the
/// stream) counts the whole stream and decides what is stored: head
/// retention stops storing once the window is full, and tail retention
/// trims the stored text to what every later window still needs. Under
/// [`Truncation::Off`] it keeps everything.
#[derive(Debug)]
pub struct OutputBuffer {
    /// The bounder of the output; `None` under the opt-out.
    bound: Option<bound::Stream>,
    /// Decoder of byte chunks. A string chunk or a skip ends an incomplete
    /// character of earlier bytes (it becomes U+FFFD); the next byte chunk
    /// then starts a new character. Only a byte-order mark at the very start
    /// of the output is dropped, never a U+FEFF later in it.
    decoder: Utf8Decoder,
    started: bool,
    /// The stored output: for head the start of the stream, for tail an end
    /// that still holds every later window, all of it under the opt-out.
    stored: String,
}

/// Error of [`OutputBuffer::push`] with a skip under head retention.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("Skipped output requires tail retention")]
pub struct SkipRequiresTail;

impl OutputBuffer {
    #[must_use]
    pub fn new(truncation: Truncation) -> Self {
        Self {
            bound: truncation
                .limits()
                .map(|limits| bound::Stream::open(cap_of(&limits))),
            decoder: Utf8Decoder::new(),
            started: false,
            stored: String::new(),
        }
    }

    /// Bytes currently held; bounded by twice the limits plus one chunk.
    /// Only the tests read it (TS exposes it as a getter no caller uses).
    #[cfg(test)]
    #[must_use]
    pub fn stored_bytes(&self) -> usize {
        self.stored.len()
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
            return Ok(self.accept(&(pending + &text)));
        };
        let Some(bound) = self.bound.as_mut().filter(|bound| bound.takes_skips()) else {
            return Err(SkipRequiresTail);
        };
        let _accepted = Self::take(bound, &mut self.stored, &pending);
        if bound.skip(skipped.bytes, skipped.newlines, !skipped.ends_with_newline) {
            // Nothing stored before the skip is in a window once the text after it arrives.
            self.stored.clear();
        }
        let _accepted = Self::take(bound, &mut self.stored, &text);
        Ok(true)
    }

    /// Flush an incomplete trailing character as a replacement character;
    /// call when the stream ends.
    pub fn end(&mut self) {
        let text = self.decoder.finish();
        self.accept(&text);
    }

    fn accept(&mut self, text: &str) -> bool {
        if let Some(bound) = &mut self.bound {
            return Self::take(bound, &mut self.stored, text);
        }
        self.stored.push_str(text);
        !text.is_empty()
    }

    /// Feed a text to the bounder and store it as it decides.
    fn take(bound: &mut bound::Stream, stored: &mut String, text: &str) -> bool {
        if text.is_empty() {
            return false;
        }
        let newlines = count_newlines(text);
        match bound.out(text.len(), newlines, !text.ends_with('\n')) {
            bound::Act::Drop => {}
            bound::Act::Store => stored.push_str(text),
            bound::Act::Trim => {
                stored.push_str(text);
                let cut = bound.look(stored).cut;
                stored.drain(..cut);
            }
        }
        true
    }

    /// Retained, sanitized output and what the limits dropped from the whole
    /// stream.
    pub fn snapshot(&mut self) -> BoundedOutput {
        let Some(bound) = &mut self.bound else {
            return BoundedOutput {
                text: sanitize_output(&self.stored),
                dropped_bytes: 0,
                dropped_lines: 0,
            };
        };
        let look = bound.look(&self.stored);
        let text = sanitize_output(&self.stored[look.from..look.to]);
        self.stored.drain(..look.cut);
        BoundedOutput {
            text,
            dropped_bytes: look.dropped_bytes,
            dropped_lines: look.dropped_lines,
        }
    }
}

fn count_newlines(text: &str) -> usize {
    text.bytes().filter(|&b| b == b'\n').count()
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
