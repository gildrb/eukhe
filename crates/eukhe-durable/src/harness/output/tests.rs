//! Port of `test/harness-output.test.ts` and
//! `test/harness-output-skip.test.ts`.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use futures::future::FutureExt;
use tokio::time::{Duration, Instant};

use super::{bound_output, sanitize_output, BoundedOutput, OutputBuffer, OutputLimits, Progress};
use crate::env::ShellOutputSkip;
use crate::harness::types::{OutputRetain, ToolOutputChunk};
use crate::session::SessionError;

fn head(max_lines: usize, max_bytes: usize) -> OutputLimits {
    OutputLimits {
        max_bytes,
        max_lines,
        retain: OutputRetain::Head,
    }
}

fn tail(max_lines: usize, max_bytes: usize) -> OutputLimits {
    OutputLimits {
        max_bytes,
        max_lines,
        retain: OutputRetain::Tail,
    }
}

fn bounded(text: &str, dropped_bytes: usize, dropped_lines: usize) -> BoundedOutput {
    BoundedOutput {
        text: text.to_owned(),
        dropped_bytes,
        dropped_lines,
    }
}

fn push_text(buffer: &mut OutputBuffer, text: &str) {
    buffer
        .push(ToolOutputChunk::Text(text), None)
        .expect("push without skip");
}

fn push_bytes(buffer: &mut OutputBuffer, bytes: &[u8]) {
    buffer
        .push(ToolOutputChunk::Bytes(bytes), None)
        .expect("push without skip");
}

/// JS strings may hold lone surrogates; `Buffer.from(string, "utf8")` encodes
/// each as U+FFFD, which is what a lossy UTF-16 decode yields in Rust.
fn js_string(units: &[u16]) -> String {
    String::from_utf16_lossy(units)
}

fn buffer_tail(content: &str, max_bytes: usize) -> &str {
    let bytes = content.as_bytes();
    if bytes.len() <= max_bytes {
        return content;
    }
    let mut start = bytes.len() - max_bytes;
    while start < bytes.len() && (bytes[start] & 0xc0) == 0x80 {
        start += 1;
    }
    &content[start..]
}

/// A single line longer than the byte limit is cut like Buffer's tail slice
/// on a character boundary.
fn assert_matches_buffer_tail(input: &str, max_byte_values: Option<&[usize]>) {
    let total_bytes = input.len();
    let all: Vec<usize> = (0..total_bytes + 5).collect();
    let values = max_byte_values.unwrap_or(&all);
    for &max_bytes in values {
        let kept = bound_output(input, &tail(10, max_bytes)).text;
        let expected = buffer_tail(input, max_bytes);
        assert_eq!(
            kept, expected,
            "tail mismatch input={input:?} maxBytes={max_bytes} expected={expected:?} actual={kept:?}"
        );
        assert!(
            kept.len() <= max_bytes,
            "tail output exceeded {max_bytes} bytes"
        );
    }
}

fn sampled_byte_limits(input: &str) -> Vec<usize> {
    #[allow(clippy::cast_possible_wrap)] // reason: test inputs are far below isize::MAX bytes
    let total = input.len() as i64;
    let candidates = [
        0,
        1,
        2,
        3,
        4,
        5,
        8,
        total / 2,
        total - 4,
        total - 1,
        total,
        total + 1,
    ];
    let mut values: Vec<usize> = candidates
        .iter()
        .filter_map(|&value| usize::try_from(value).ok())
        .collect();
    values.sort_unstable();
    values.dedup();
    values
}

fn bound(text: &str, limits: &OutputLimits) -> (String, usize, usize) {
    let slice = bound_output(text, limits);
    (slice.text, slice.dropped_bytes, slice.dropped_lines)
}

fn kept(text: &str, dropped_bytes: usize, dropped_lines: usize) -> (String, usize, usize) {
    (text.to_owned(), dropped_bytes, dropped_lines)
}

// tool output bounds

#[test]
fn removes_control_characters_but_keeps_tabs_newlines_and_other_text() {
    assert_eq!(
        sanitize_output("a\0b\tc\nd\re\u{0007}f\u{fff9}g\u{fffb}h😀"),
        "ab\tc\ndefgh😀"
    );
}

#[test]
fn keeps_output_within_the_limits_unchanged() {
    assert_eq!(bound("a\nb\n", &head(2, 1000)), kept("a\nb\n", 0, 0));
    assert_eq!(bound("a\nb", &tail(2, 1000)), kept("a\nb", 0, 0));
    assert_eq!(bound("", &tail(2, 1000)), kept("", 0, 0));
}

#[test]
fn keeps_nothing_with_a_zero_limit() {
    assert_eq!(bound("ab\ncd\n", &head(10, 0)), kept("", 6, 2));
    assert_eq!(bound("ab\ncd\n", &tail(0, 1000)), kept("", 6, 2));
}

#[test]
fn keeps_exact_slices_of_whole_lines_trailing_newline_included() {
    assert_eq!(bound("a\nb\nc\n", &head(2, 1000)), kept("a\nb\n", 2, 1));
    assert_eq!(bound("a\nb\nc\n", &tail(2, 1000)), kept("b\nc\n", 2, 1));
    assert_eq!(bound("a\nb\nc", &tail(2, 1000)), kept("b\nc", 2, 1));
    // Blank lines are lines.
    assert_eq!(bound("a\nb\nc\n\n", &tail(3, 1000)), kept("b\nc\n\n", 2, 1));
}

#[test]
fn cuts_at_the_byte_limit_on_whole_lines_when_possible() {
    assert_eq!(bound("aa\nbb\ncc\n", &head(10, 7)), kept("aa\nbb\n", 3, 1));
    assert_eq!(bound("aa\nbb\ncc\n", &tail(10, 7)), kept("bb\ncc\n", 3, 1));
}

#[test]
fn cuts_a_single_line_longer_than_the_byte_limit_on_a_character_boundary() {
    // "é" is two bytes; five bytes hold two whole characters.
    assert_eq!(bound("ééé\n", &head(10, 5)), kept("éé", 3, 0));
    assert_eq!(bound("x\néééé", &tail(10, 5)), kept("éé", 6, 1));
}

#[test]
fn keeps_a_u_feff_at_the_start_of_a_kept_slice() {
    assert_eq!(bound("x\u{feff}a", &tail(10, 4)), kept("\u{feff}a", 1, 0));
}

#[test]
fn cuts_tails_of_surrogate_edge_cases_exactly_like_buffer() {
    let inputs: [&[u16]; 6] = [
        &[0x61, 0xd83d],
        &[0xde42, 0x62],
        &[0x61, 0xde42, 0x62],
        &[0xd83d, 0xd83d, 0xde42],
        &[0xd83d, 0xde42, 0xde42],
        &[0xd83d, 0xdc69, 0x200d, 0xd83d, 0xdcbb],
    ];
    for input in inputs {
        assert_matches_buffer_tail(&js_string(input), None);
    }
}

fn check_exhaustive(alphabet: &[&[u16]], prefix: &[u16], depth: usize) {
    let input = js_string(prefix);
    assert_matches_buffer_tail(&input, Some(&sampled_byte_limits(&input)));
    if depth == 0 {
        return;
    }
    for character in alphabet {
        check_exhaustive(alphabet, &[prefix, character].concat(), depth - 1);
    }
}

#[test]
fn cuts_tails_exactly_like_buffer_across_deterministic_fuzz_cases() {
    let alphabet: [&[u16]; 15] = [
        &[0x61],
        &[0x7f],
        &[0x80],
        &[0xe9],
        &[0x07ff],
        &[0x0800],
        &[0x4e2d],
        &[0xd7ff],
        &[0xd800],
        &[0xd83d],
        &[0xdc00],
        &[0xde42],
        &[0xd83d, 0xde42],
        &[0xe000],
        &[0xffff],
    ];
    check_exhaustive(&alphabet, &[], 3);
    let mut seed: u32 = 0x1234_5678;
    let mut random = || {
        seed = seed.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
        f64::from(seed) / 4_294_967_296.0
    };
    for _ in 0..1_000 {
        let mut units = Vec::new();
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        // reason: JS Math.floor of a value in [0, 80)
        let length = (random() * 80.0).floor() as usize;
        for _ in 0..length {
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            // reason: JS Math.floor of an index in range
            let index = (random() * 15.0).floor() as usize;
            units.extend_from_slice(alphabet[index]);
        }
        let input = js_string(&units);
        assert_matches_buffer_tail(&input, Some(&sampled_byte_limits(&input)));
    }
}

// OutputBuffer

#[test]
fn keeps_exact_totals_across_chunks_and_decodes_utf8_split_across_byte_chunks() {
    let mut buffer = OutputBuffer::new(tail(2, 1000));
    let bytes = "😀\n".as_bytes();
    push_text(&mut buffer, "a\nb\n");
    push_bytes(&mut buffer, &bytes[..2]);
    push_bytes(&mut buffer, &bytes[2..]);
    assert_eq!(buffer.snapshot(), bounded("b\n😀\n", 2, 1));
}

#[test]
fn sanitizes_the_retained_text_but_counts_the_raw_stream() {
    let mut buffer = OutputBuffer::new(tail(1, 1000));
    push_text(&mut buffer, "a\u{0007}\n");
    assert_eq!(buffer.snapshot(), bounded("a\n", 0, 0));
    push_text(&mut buffer, "b\u{001b}\n");
    assert_eq!(buffer.snapshot(), bounded("b\n", 3, 1));
}

#[test]
fn drops_a_byte_order_mark_only_at_the_start_of_the_output() {
    let bom = [0xef, 0xbb, 0xbf];
    let mut buffer = OutputBuffer::new(tail(10, 1000));
    push_bytes(&mut buffer, &bom[..1]);
    push_bytes(&mut buffer, &[0xbb, 0xbf, 0x61]);
    push_text(&mut buffer, "b");
    // A U+FEFF after a string chunk is text.
    push_bytes(&mut buffer, &[0xef, 0xbb, 0xbf, 0x63]);
    buffer.end();
    assert_eq!(buffer.snapshot().text, "ab\u{feff}c");
}

#[test]
fn flushes_an_incomplete_character_before_a_string_chunk_and_at_the_end() {
    let mut buffer = OutputBuffer::new(tail(10, 1000));
    let euro = "€".as_bytes();
    push_bytes(&mut buffer, &euro[..1]);
    push_text(&mut buffer, "x");
    push_bytes(&mut buffer, &euro[..2]);
    buffer.end();
    assert_eq!(buffer.snapshot().text, "\u{fffd}x\u{fffd}");
}

#[test]
fn matches_bounding_the_whole_stream_when_several_chunks_arrive_between_snapshots() {
    for limits in [head(3, 40), tail(3, 40), head(50, 25), tail(50, 25)] {
        let mut buffer = OutputBuffer::new(limits);
        let mut stream = String::new();
        for index in 0..300 {
            let chunk = if index % 7 == 0 {
                format!("{}\n", "é".repeat(index % 30))
            } else {
                format!("line {index}\n")
            };
            stream.push_str(&chunk);
            push_text(&mut buffer, &chunk);
            if index % 5 != 4 {
                continue;
            }
            let expected = bound_output(&stream, &limits);
            assert_eq!(
                buffer.snapshot(),
                BoundedOutput {
                    text: expected.text,
                    dropped_bytes: expected.dropped_bytes,
                    dropped_lines: expected.dropped_lines,
                }
            );
        }
    }
}

#[test]
fn stops_storing_head_output_once_the_window_is_full() {
    let mut buffer = OutputBuffer::new(head(2, 1000));
    for index in 0..1000 {
        push_text(&mut buffer, &format!("line {index}\n"));
    }
    assert!(buffer.stored_bytes() < 20);
    assert_eq!(buffer.snapshot(), bounded("line 0\nline 1\n", 8876, 998));
}

#[test]
fn stores_only_the_tail_window_after_each_snapshot() {
    let mut buffer = OutputBuffer::new(tail(3, 100));
    let mut stream = String::new();
    for index in 0..2000 {
        let chunk = format!("line {index}\n\n");
        stream.push_str(&chunk);
        push_text(&mut buffer, &chunk);
        let snapshot = buffer.snapshot();
        assert!(buffer.stored_bytes() <= 100);
        assert_eq!(snapshot.text, bound_output(&stream, &tail(3, 100)).text);
    }
}

// Progress

/// `vi.advanceTimersByTimeAsync`: move paused time and let woken tasks run.
/// Sleeping (with auto-advance) rather than `tokio::time::advance` lands on
/// the timer wheel's millisecond ticks, so deadlines the code under test
/// rounded up to a tick fire at the same step they would in vitest.
async fn advance(ms: u64) {
    tokio::time::sleep(Duration::from_millis(ms)).await;
    for _ in 0..16 {
        tokio::task::yield_now().await;
    }
}

fn elapsed_ms(start: Instant) -> u128 {
    start.elapsed().as_millis()
}

fn commits(log: &Mutex<Vec<u128>>) -> Vec<u128> {
    log.lock().unwrap_or_else(PoisonError::into_inner).clone()
}

#[tokio::test(start_paused = true)]
async fn commits_the_first_change_at_once_then_waits_at_least_100_ms_and_the_written_size_at_100_kib_s(
) {
    let start = Instant::now();
    let log = Arc::new(Mutex::new(Vec::new()));
    let size = Arc::new(AtomicUsize::new(50 * 1024));
    let progress = Progress::new(
        Box::new({
            let log = Arc::clone(&log);
            let size = Arc::clone(&size);
            move || {
                log.lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push(elapsed_ms(start));
                let size = size.load(Ordering::SeqCst);
                async move { Ok(size) }.boxed()
            }
        }),
        Box::new(|_| {}),
        100.0,
    );
    progress.mark();
    advance(0).await;
    assert_eq!(commits(&log), [0]);
    // 50 KiB buys 500 ms; changes meanwhile coalesce into one commit.
    size.store(10, Ordering::SeqCst);
    progress.mark();
    progress.mark();
    advance(499).await;
    assert_eq!(commits(&log), [0]);
    advance(1).await;
    assert_eq!(commits(&log), [0, 500]);
    // A small commit still waits the minimum 100 ms.
    progress.mark();
    advance(99).await;
    assert_eq!(commits(&log), [0, 500]);
    advance(1).await;
    assert_eq!(commits(&log), [0, 500, 600]);
}

#[tokio::test(start_paused = true)]
async fn waits_the_configured_minimum_interval_between_small_commits() {
    let start = Instant::now();
    let log = Arc::new(Mutex::new(Vec::new()));
    let progress = Progress::new(
        Box::new({
            let log = Arc::clone(&log);
            move || {
                log.lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push(elapsed_ms(start));
                async { Ok(10) }.boxed()
            }
        }),
        Box::new(|_| {}),
        500.0,
    );
    progress.mark();
    advance(0).await;
    progress.mark();
    advance(499).await;
    assert_eq!(commits(&log), [0]);
    advance(1).await;
    assert_eq!(commits(&log), [0, 500]);
}

#[tokio::test]
async fn rejects_the_waiters_of_a_failed_commit_and_reports_its_error() {
    let failure: Arc<str> = Arc::from("commit failed");
    let errors = Arc::new(Mutex::new(Vec::<SessionError>::new()));
    let progress = Progress::new(
        Box::new({
            let failure = Arc::clone(&failure);
            move || {
                let failure = Arc::clone(&failure);
                async move { Err(SessionError::Error(failure)) }.boxed()
            }
        }),
        Box::new({
            let errors = Arc::clone(&errors);
            move |error| {
                errors
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push(error);
            }
        }),
        100.0,
    );
    let rejected = progress.mark_and_wait().await;
    let Err(SessionError::Error(message)) = rejected else {
        panic!("expected the commit failure, got {rejected:?}");
    };
    assert!(Arc::ptr_eq(&message, &failure));
    let errors = errors.lock().unwrap_or_else(PoisonError::into_inner);
    assert_eq!(errors.len(), 1);
    assert!(matches!(&errors[0], SessionError::Error(message) if Arc::ptr_eq(message, &failure)));
}

#[tokio::test(start_paused = true)]
async fn stops_waits_for_the_commit_in_flight_and_hands_back_waiters_no_commit_covered_yet() {
    let in_flight = Arc::new(tokio::sync::Semaphore::new(0));
    let progress = Progress::new(
        Box::new({
            let in_flight = Arc::clone(&in_flight);
            move || {
                let in_flight = Arc::clone(&in_flight);
                async move {
                    let _permit = in_flight.acquire().await.expect("semaphore open");
                    Ok(0)
                }
                .boxed()
            }
        }),
        Box::new(|_| {}),
        100.0,
    );
    let first = progress.mark_and_wait();
    let second = progress.mark_and_wait();
    let stopped = progress.stop();
    in_flight.add_permits(1);
    let pending = stopped.await;
    first.await.expect("first commit succeeds");
    assert_eq!(pending.len(), 1);
    for waiter in pending {
        waiter.send(Ok(())).expect("second waiter listening");
    }
    second.await.expect("second waiter resolved");
}

// OutputBuffer skipped output

/// Deterministic PRNG (mulberry32) so failures reproduce from the printed seed.
fn random(seed: u32) -> impl FnMut() -> f64 {
    let mut state = seed;
    move || {
        state = state.wrapping_add(0x6d2b_79f5);
        let mut t = state;
        t = (t ^ (t >> 15)).wrapping_mul(t | 1);
        t ^= t.wrapping_add((t ^ (t >> 7)).wrapping_mul(t | 0x3d));
        f64::from(t ^ (t >> 14)) / 4_294_967_296.0
    }
}

/// JS `Math.floor(next() * n)` for an index below `n`.
fn pick(next: &mut (impl FnMut() -> f64 + ?Sized), n: usize) -> usize {
    #[allow(
        clippy::cast_precision_loss,
        clippy::cast_possible_truncation,
        clippy::cast_sign_loss
    )] // reason: JS number arithmetic on small counts
    let index = (next() * n as f64).floor() as usize;
    index
}

// Decoded shell output: ASCII, multi-byte and astral characters, replacement
// characters, CR/LF, tabs, and control characters that sanitizing removes
// after bounding.
const ALPHABET: [&str; 15] = [
    "a", "b", "z", " ", "\n", "\n", "\n", "\r\n", "\t", "é", "€", "😀", "\u{fffd}", "\x01", "\x1b",
];

fn random_chunk(next: &mut (impl FnMut() -> f64 + ?Sized)) -> String {
    let length = pick(next, 12);
    let mut text = String::new();
    for _ in 0..length {
        text.push_str(ALPHABET[pick(next, ALPHABET.len())]);
    }
    text
}

fn measure(text: &str) -> ShellOutputSkip {
    ShellOutputSkip {
        bytes: text.len() as u64,
        newlines: text.chars().filter(|&c| c == '\n').count() as u64,
        ends_with_newline: text.ends_with('\n'),
    }
}

/// Whether `text` proves that everything before it is outside the tail window.
fn exceeds_window(text: &str, limits: &OutputLimits) -> bool {
    let ShellOutputSkip {
        bytes, newlines, ..
    } = measure(text);
    bytes > limits.max_bytes as u64 || newlines > limits.max_lines as u64
}

/// Code-point boundaries of `text`, so a cut never splits a character.
fn boundaries(text: &str) -> Vec<usize> {
    let mut result = vec![0];
    result.extend(text.char_indices().map(|(offset, c)| offset + c.len_utf8()));
    result
}

fn random_tail_limits(next: &mut impl FnMut() -> f64) -> OutputLimits {
    let max_bytes = 1 + pick(next, 40);
    let max_lines = 1 + pick(next, 5);
    OutputLimits {
        max_bytes,
        max_lines,
        retain: OutputRetain::Tail,
    }
}

/// Feed random output to one buffer in full and to another through a
/// reference skipper that follows the contract of `ShellOutputInfo.skipped`:
/// it holds undelivered text, and when it flushes, it may replace a prefix of
/// it by counts if the rest exceeds the window. Snapshots must agree whenever
/// both buffers have seen the same output.
fn check_seed(seed: u32) {
    let mut next = random(seed);
    let limits = random_tail_limits(&mut next);
    let mut full = OutputBuffer::new(limits);
    let mut skipping = OutputBuffer::new(limits);
    let mut pending = String::new();
    let mut skips = 0_usize;
    let mut flush = |next: &mut dyn FnMut() -> f64,
                     pending: &mut String,
                     full: &mut OutputBuffer,
                     skipping: &mut OutputBuffer| {
        if pending.is_empty() {
            return;
        }
        let cuts: Vec<usize> = boundaries(pending)
            .into_iter()
            .filter(|&cut| cut > 0 && exceeds_window(&pending[cut..], &limits))
            .collect();
        if !cuts.is_empty() && next() < 0.7 {
            let cut = cuts[pick(&mut *next, cuts.len())];
            skipping
                .push(
                    ToolOutputChunk::Text(&pending[cut..]),
                    Some(&measure(&pending[..cut])),
                )
                .expect("tail retention accepts skips");
            skips += 1;
        } else {
            push_text(skipping, pending);
        }
        pending.clear();
        // Progress snapshots happen between deliveries and compact stored chunks.
        if next() < 0.5 {
            skipping.snapshot();
        }
        assert_eq!(skipping.snapshot(), full.snapshot(), "seed {seed}");
    };
    let chunks = pick(&mut next, 40);
    for _ in 0..chunks {
        let chunk = random_chunk(&mut next);
        push_text(&mut full, &chunk);
        if next() < 0.3 {
            full.snapshot();
        }
        pending.push_str(&chunk);
        if next() < 0.3 {
            flush(&mut next, &mut pending, &mut full, &mut skipping);
        }
    }
    flush(&mut next, &mut pending, &mut full, &mut skipping);
    full.end();
    skipping.end();
    assert_eq!(skipping.snapshot(), full.snapshot(), "seed {seed}");
}

// Progress commits snapshot at arbitrary moments; snapshots compact what is
// stored and must never change the window. A compaction to exactly the kept
// window lost the character that decides where a later window's first line
// starts.
#[test]
fn keeps_the_same_tail_whenever_progress_snapshots_happen() {
    for seed in 1..=3000 {
        let mut next = random(seed);
        let limits = random_tail_limits(&mut next);
        let mut plain = OutputBuffer::new(limits);
        let mut sampled = OutputBuffer::new(limits);
        let chunks = pick(&mut next, 30);
        for _ in 0..chunks {
            let chunk = random_chunk(&mut next);
            push_text(&mut plain, &chunk);
            push_text(&mut sampled, &chunk);
            if next() < 0.4 {
                sampled.snapshot();
            }
        }
        assert_eq!(sampled.snapshot(), plain.snapshot(), "seed {seed}");
    }
}

#[test]
fn matches_the_full_stream_for_every_legal_skip_pattern() {
    for seed in 1..=3000 {
        check_seed(seed);
    }
}

#[test]
fn counts_skipped_bytes_lines_and_the_final_newline_exactly() {
    let limits = tail(2, 1000);
    let mut full = OutputBuffer::new(limits);
    let mut skipping = OutputBuffer::new(limits);
    // The skipped text ends without a newline, so its last line continues in
    // the delivered text.
    let omitted = "one\ntwo\nthr";
    let kept = "ee\nfour\nfive\nsix";
    push_text(&mut full, &format!("{omitted}{kept}"));
    skipping
        .push(ToolOutputChunk::Text(kept), Some(&measure(omitted)))
        .expect("tail retention accepts skips");
    assert_eq!(skipping.snapshot(), full.snapshot());
    assert_eq!(skipping.snapshot(), bounded("five\nsix", 19, 4));
}

#[test]
fn refuses_skips_for_head_retention() {
    let mut buffer = OutputBuffer::new(head(2, 10));
    let skip = ShellOutputSkip {
        bytes: 3,
        newlines: 1,
        ends_with_newline: true,
    };
    let error = buffer
        .push(ToolOutputChunk::Text("x\ny\nz\n"), Some(&skip))
        .expect_err("head retention refuses skips");
    assert!(error.to_string().contains("tail retention"));
}
