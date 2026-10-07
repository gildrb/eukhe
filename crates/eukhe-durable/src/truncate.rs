//! Shared truncation utilities for tool outputs. Port of `truncate.ts`.
//!
//! Truncation is based on two independent limits, whichever is hit first
//! wins: a line limit (default 2000 lines) and a byte limit (default 50KB).
//! Never returns partial lines. Tool output streams are bounded by the
//! harness output buffer instead.

pub(crate) const DEFAULT_MAX_LINES: u64 = 2000;
/// 50KB.
pub(crate) const DEFAULT_MAX_BYTES: u64 = 50 * 1024;

/// Which limit truncated the content: the TS `"lines" | "bytes"`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum TruncatedBy {
    Lines,
    Bytes,
}

impl TruncatedBy {
    /// The TS string: `"lines"` or `"bytes"`.
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::Lines => "lines",
            Self::Bytes => "bytes",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct TruncationResult {
    /// The truncated content.
    pub(crate) content: String,
    /// Whether truncation occurred.
    pub(crate) truncated: bool,
    /// Which limit was hit; `None` (TS `null`) if not truncated.
    pub(crate) truncated_by: Option<TruncatedBy>,
    /// Total number of lines in the original content.
    pub(crate) total_lines: u64,
    /// Total number of bytes in the original content.
    pub(crate) total_bytes: u64,
    /// Number of complete lines in the truncated output.
    pub(crate) output_lines: u64,
    /// Number of bytes in the truncated output.
    pub(crate) output_bytes: u64,
    /// Whether the last line was partially truncated (only for the tail
    /// truncation edge case).
    pub(crate) last_line_partial: bool,
    /// Whether the first line exceeded the byte limit (for head truncation).
    pub(crate) first_line_exceeds_limit: bool,
    /// The max lines limit that was applied.
    pub(crate) max_lines: u64,
    /// The max bytes limit that was applied.
    pub(crate) max_bytes: u64,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct TruncationOptions {
    /// Maximum number of lines (default: 2000).
    pub(crate) max_lines: Option<u64>,
    /// Maximum number of bytes (default: 50KB).
    pub(crate) max_bytes: Option<u64>,
}

/// The totals of a whole text known by a prefix: `lines` counted like
/// [`truncate_head`] (ignoring a trailing newline) and UTF-8 `bytes`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct TruncationTotals {
    pub(crate) lines: u64,
    pub(crate) bytes: u64,
}

/// UTF-8 byte length, like Node's `Buffer.byteLength(content, "utf8")`. A
/// Rust string is valid UTF-8 (it cannot hold the lone surrogates JS encodes
/// as three bytes), so this is its length.
pub(crate) fn utf8_byte_length(content: &str) -> u64 {
    content.len() as u64
}

fn split_lines_for_counting(content: &str) -> Vec<&str> {
    if content.is_empty() {
        return Vec::new();
    }
    let mut lines: Vec<&str> = content.split('\n').collect();
    if content.ends_with('\n') {
        lines.pop();
    }
    lines
}

/// Format bytes as human-readable size.
pub(crate) fn format_size(bytes: u64) -> String {
    if bytes < 1024 {
        format!("{bytes}B")
    } else if bytes < 1024 * 1024 {
        format!("{}KB", to_fixed_1(bytes, 10))
    } else {
        format!("{}MB", to_fixed_1(bytes, 20))
    }
}

/// JS `(bytes / 2 ** shift).toFixed(1)` for a JS number `bytes`: the exact
/// quotient (dividing by a power of two is exact) rounded half up, which is
/// what `toFixed` does (Rust's `{:.1}` rounds exact ties to even).
fn to_fixed_1(bytes: u64, shift: u32) -> String {
    // The JS number holding `bytes` (exact below 2^53).
    #[expect(
        clippy::cast_precision_loss,
        reason = "the size is a JS number; it rounds exactly as in JS"
    )]
    let number = bytes as f64;
    #[expect(
        clippy::cast_possible_truncation,
        clippy::cast_sign_loss,
        reason = "an integral non-negative f64 below 2^64 converts exactly"
    )]
    let integral = number as u128;
    let tenths = (integral * 10 + (1 << (shift - 1))) >> shift;
    format!("{}.{}", tenths / 10, tenths % 10)
}

/// Truncate content from the head (keep first N lines/bytes). Suitable for
/// file reads where you want to see the beginning.
///
/// Never returns partial lines. If the first line exceeds the byte limit,
/// returns empty content with `first_line_exceeds_limit`.
pub(crate) fn truncate_head(content: &str, options: TruncationOptions) -> TruncationResult {
    truncate_head_of(
        content,
        TruncationTotals {
            lines: split_lines_for_counting(content).len() as u64,
            bytes: utf8_byte_length(content),
        },
        options,
    )
}

/// [`truncate_head`] of a text known by a prefix and its totals. The prefix
/// must be the whole text, or longer than `max_bytes + 1` UTF-8 bytes, or
/// hold at least `max_lines` newlines; then the result equals
/// [`truncate_head`] of the whole text.
pub(crate) fn truncate_head_of(
    prefix: &str,
    totals: TruncationTotals,
    options: TruncationOptions,
) -> TruncationResult {
    let max_lines = options.max_lines.unwrap_or(DEFAULT_MAX_LINES);
    let max_bytes = options.max_bytes.unwrap_or(DEFAULT_MAX_BYTES);

    let total_bytes = totals.bytes;
    let lines = split_lines_for_counting(prefix);
    let total_lines = totals.lines;

    // Check if no truncation needed.
    if total_lines <= max_lines && total_bytes <= max_bytes {
        return TruncationResult {
            content: prefix.to_owned(),
            truncated: false,
            truncated_by: None,
            total_lines,
            total_bytes,
            output_lines: total_lines,
            output_bytes: total_bytes,
            last_line_partial: false,
            first_line_exceeds_limit: false,
            max_lines,
            max_bytes,
        };
    }

    // Check if the first line alone exceeds the byte limit. An empty prefix
    // with non-zero totals breaks the precondition; TS would throw a
    // `TypeError` on `Buffer.byteLength(undefined)`, here the missing line
    // counts as empty.
    let first_line_bytes = lines.first().map_or(0, |line| utf8_byte_length(line));
    if first_line_bytes > max_bytes {
        return TruncationResult {
            content: String::new(),
            truncated: true,
            truncated_by: Some(TruncatedBy::Bytes),
            total_lines,
            total_bytes,
            output_lines: 0,
            output_bytes: 0,
            last_line_partial: false,
            first_line_exceeds_limit: true,
            max_lines,
            max_bytes,
        };
    }

    // Collect complete lines that fit.
    let mut output_lines: Vec<&str> = Vec::new();
    let mut output_bytes_count = 0;
    let mut truncated_by = TruncatedBy::Lines;

    for (index, line) in lines.iter().enumerate() {
        if index as u64 >= max_lines {
            break;
        }
        // +1 for the newline.
        let line_bytes = utf8_byte_length(line) + u64::from(index > 0);
        if output_bytes_count + line_bytes > max_bytes {
            truncated_by = TruncatedBy::Bytes;
            break;
        }
        output_lines.push(line);
        output_bytes_count += line_bytes;
    }

    // Without a byte break, only omitted lines prove the line limit was
    // reached; otherwise a trailing newline exceeded bytes.
    if truncated_by != TruncatedBy::Bytes {
        truncated_by = if (output_lines.len() as u64) < total_lines {
            TruncatedBy::Lines
        } else {
            TruncatedBy::Bytes
        };
    }

    let output_content = output_lines.join("\n");
    let final_output_bytes = utf8_byte_length(&output_content);

    TruncationResult {
        content: output_content,
        truncated: true,
        truncated_by: Some(truncated_by),
        total_lines,
        total_bytes,
        output_lines: output_lines.len() as u64,
        output_bytes: final_output_bytes,
        last_line_partial: false,
        first_line_exceeds_limit: false,
        max_lines,
        max_bytes,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn options(max_bytes: u64, max_lines: u64) -> TruncationOptions {
        TruncationOptions {
            max_lines: Some(max_lines),
            max_bytes: Some(max_bytes),
        }
    }

    #[test]
    fn reports_utf8_byte_counts_in_truncation_results() {
        let content = "aé🙂\nb";
        let result = truncate_head(content, options(100, 10));

        assert!(!result.truncated);
        assert_eq!(result.total_bytes, content.len() as u64);
        assert_eq!(result.output_bytes, content.len() as u64);
        assert_eq!(result.total_bytes, 9);
    }

    /// The TS test runs `utf8ByteLength` in a runtime without `Buffer` (a JS
    /// fallback path). Rust has one path; this checks the same valid inputs
    /// (lone surrogates `"\ud83d"`, `"\ude42"` are not representable in a
    /// Rust string) and the same truncation.
    #[test]
    fn counts_utf8_bytes_and_truncates_correctly_in_a_runtime_without_buffer() {
        let inputs = [
            "",
            "ascii",
            "é",
            "中",
            "🙂",
            "a🙂b",
            "\u{07ff}\u{0800}\u{ffff}",
        ];
        let lengths: Vec<u64> = inputs.iter().map(|input| utf8_byte_length(input)).collect();
        assert_eq!(lengths, vec![0, 5, 2, 3, 4, 6, 8]);
        let head = truncate_head("aé🙂\nb", options(7, 10));
        assert_eq!(head.content, "aé🙂");
        assert_eq!(head.output_bytes, 7);
        assert_eq!(head.truncated_by, Some(TruncatedBy::Bytes));
    }

    #[test]
    fn does_not_count_a_trailing_newline_as_an_extra_line() {
        let content = format!("{}\n", ["line"; 3].join("\n"));
        let head = truncate_head(&content, options(100, 3));

        assert!(!head.truncated);
        assert_eq!(head.total_lines, 3);
        assert_eq!(head.output_lines, 3);
    }

    #[test]
    fn truncates_head_by_line_limits() {
        let result = truncate_head("one\ntwo\nthree\nfour", options(100, 2));
        assert_eq!(result.content, "one\ntwo");
        assert!(result.truncated);
        assert_eq!(result.truncated_by, Some(TruncatedBy::Lines));
        assert_eq!(result.total_lines, 4);
        assert_eq!(result.output_lines, 2);
    }

    #[test]
    fn names_truncation_limits_like_ts() {
        assert_eq!(TruncatedBy::Lines.as_str(), "lines");
        assert_eq!(TruncatedBy::Bytes.as_str(), "bytes");
    }

    #[test]
    fn reports_bytes_when_only_a_trailing_newline_exceeds_limits_at_the_line_cap() {
        let result = truncate_head("hello\nworld\n", options(11, 2));
        assert_eq!(result.content, "hello\nworld");
        assert!(result.truncated);
        assert_eq!(result.truncated_by, Some(TruncatedBy::Bytes));
        assert_eq!(result.total_lines, 2);
        assert_eq!(result.output_lines, 2);
    }

    #[test]
    fn truncates_head_on_utf8_byte_limits_without_partial_lines() {
        let result = truncate_head("éé\nabc", options(4, 10));

        assert_eq!(result.content, "éé");
        assert!(result.truncated);
        assert_eq!(result.truncated_by, Some(TruncatedBy::Bytes));
        assert_eq!(result.output_bytes, 4);
        assert!(!result.first_line_exceeds_limit);
    }

    #[test]
    fn reports_head_truncation_when_the_first_line_exceeds_the_byte_limit() {
        let result = truncate_head("éé\nabc", options(3, 10));

        assert_eq!(result.content, "");
        assert!(result.truncated);
        assert_eq!(result.truncated_by, Some(TruncatedBy::Bytes));
        assert!(result.first_line_exceeds_limit);
    }

    #[test]
    fn formats_sizes() {
        assert_eq!(format_size(1023), "1023B");
        assert_eq!(format_size(1536), "1.5KB");
        assert_eq!(format_size(3 * 1024 * 1024), "3.0MB");
    }

    /// `toFixed` rounds exact ties up; values checked against node.
    #[test]
    fn formats_sizes_like_js_to_fixed() {
        assert_eq!(format_size(1280), "1.3KB");
        assert_eq!(format_size(1305), "1.3KB");
        assert_eq!(format_size(80_000), "78.1KB");
        assert_eq!(format_size(51_200), "50.0KB");
        assert_eq!(format_size(1024 * 1024 - 1), "1024.0KB");
        assert_eq!(format_size(1_179_648), "1.1MB");
        assert_eq!(format_size(u64::MAX), "17592186044416.0MB");
    }
}
