//! Port of `test/env-line-scan.test.ts`.

use eukhe_durable::env::{LineScanner, StreamDecoder};

/// mulberry32, as the TS test seeds it.
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

/// Newlines, ASCII, a byte-order mark, valid multi-byte sequences, and bytes
/// that form invalid or truncated sequences.
const PIECES: &[&[u8]] = &[
    &[0x0a],
    &[0x0a],
    &[0x61],
    &[0x62, 0x63],
    &[0xef, 0xbb, 0xbf],
    &[0xc3, 0xa9],
    &[0xe2, 0x82, 0xac],
    &[0xf0, 0x9f, 0x98, 0x80],
    &[0xe2, 0x82],
    &[0xff],
    &[0x80],
    &[0xf0, 0x9f],
    &[0x0d, 0x0a],
];

/// `Math.floor(next() * n)`.
#[allow(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::cast_precision_loss,
    reason = "next() is in [0, 1) and n is small"
)]
fn below(next: &mut impl FnMut() -> f64, n: usize) -> usize {
    (next() * n as f64).floor() as usize
}

fn random_file(next: &mut impl FnMut() -> f64) -> Vec<u8> {
    let mut bytes = Vec::new();
    let pieces = below(next, 60);
    for _ in 0..pieces {
        bytes.extend_from_slice(PIECES[below(next, PIECES.len())]);
    }
    bytes
}

/// `new TextDecoder().decode(bytes)`: maximal-subpart replacement, leading
/// byte-order mark dropped.
fn decode_whole(bytes: &[u8]) -> String {
    let text = String::from_utf8_lossy(bytes);
    text.strip_prefix('\u{feff}').unwrap_or(&text).to_owned()
}

/// `new TextDecoder("utf-8", { ignoreBOM: from > 0 }).decode(file.subarray(from, to))`.
fn decode_range(file: &[u8], from: u64, to: u64) -> String {
    let from = usize::try_from(from).expect("offset");
    let to = usize::try_from(to).expect("offset");
    let slice = &file[from..to];
    if from > 0 {
        String::from_utf8_lossy(slice).into_owned()
    } else {
        decode_whole(slice)
    }
}

// StreamDecoder

/// Node's streaming `TextDecoder` with BOM handling dropped this U+FEFF, which
/// follows an invalid sequence.
#[test]
fn keeps_a_u_feff_that_does_not_start_the_stream() {
    let bytes = [0xe2, 0x82, 0xef, 0xbb, 0xbf, 0x61];
    let mut decoder = StreamDecoder::new();
    let mut text: String = bytes.iter().map(|byte| decoder.decode(&[*byte])).collect();
    text.push_str(&decoder.finish());
    assert_eq!(text, decode_whole(&bytes));
    assert_eq!(text, "\u{fffd}\u{feff}a");
}

#[test]
fn decodes_any_chunking_like_decoding_the_whole_stream() {
    for seed in 1..=5000 {
        let mut next = random(seed);
        let bytes = random_file(&mut next);
        let mut decoder = StreamDecoder::new();
        let mut text = String::new();
        let mut offset = 0;
        while offset < bytes.len() {
            let size = 1 + below(&mut next, 7);
            let end = (offset + size).min(bytes.len());
            text.push_str(&decoder.decode(&bytes[offset..end]));
            offset += size;
        }
        text.push_str(&decoder.finish());
        assert_eq!(text, decode_whole(&bytes), "seed {seed}");
    }
}

// LineScanner

#[test]
#[allow(clippy::cast_precision_loss, reason = "small test line numbers")]
fn agrees_with_decoding_and_splitting_the_whole_file() {
    for seed in 1..=5000 {
        let mut next = random(seed);
        let file = random_file(&mut next);
        let whole = decode_whole(&file);
        let lines: Vec<&str> = whole.split('\n').collect();
        let start_line = below(&mut next, lines.len() + 2);
        let end_line = if next() < 0.3 {
            None
        } else {
            Some(start_line + 1 + below(&mut next, lines.len() + 1))
        };
        let mut scanner = LineScanner::new(start_line as f64, end_line.map(|end| end as f64))
            .expect("valid range");
        let mut offset = 0;
        while offset < file.len() {
            let size = 1 + below(&mut next, 7);
            let end = (offset + size).min(file.len());
            scanner.push(&file[offset..end]);
            offset += size;
        }
        let scan = scanner.finish();
        let message = format!("seed {seed}");
        assert_eq!(scan.newlines, (lines.len() - 1) as u64, "{message}");
        let selected_end = end_line.unwrap_or(lines.len()).min(lines.len());
        let selected = lines[start_line.min(selected_end)..selected_end].join("\n");
        assert_eq!(
            decode_range(&file, scan.start, scan.end),
            selected,
            "{message}"
        );
        assert_eq!(scan.selected_bytes, selected.len() as u64, "{message}");
        let size = file.len() as u64;
        if start_line < lines.len() {
            assert_eq!(
                decode_range(&file, scan.start, scan.first_line_end),
                lines[start_line],
                "{message}"
            );
            assert_eq!(
                scan.first_line_bytes,
                lines[start_line].len() as u64,
                "{message}"
            );
            let last_line = end_line.unwrap_or(lines.len()).min(lines.len()) - 1;
            let last_end = if last_line + 1 < lines.len() {
                let from = usize::try_from(scan.last_line_start).expect("offset");
                (from
                    + file[from..]
                        .iter()
                        .position(|&byte| byte == b'\n')
                        .expect("newline")) as u64
            } else {
                size
            };
            assert_eq!(
                decode_range(&file, scan.last_line_start, last_end),
                lines[last_line],
                "{message}"
            );
        } else {
            assert_eq!(
                (scan.start, scan.end, scan.selected_bytes),
                (size, size, 0),
                "{message}"
            );
        }
    }
}

#[test]
fn rejects_empty_or_invalid_ranges() {
    assert!(LineScanner::new(2.0, Some(2.0)).is_err());
    assert!(LineScanner::new(-1.0, None).is_err());
    assert!(LineScanner::new(1.5, None).is_err());
}
