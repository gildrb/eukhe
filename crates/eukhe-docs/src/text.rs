//! Line endings and the byte order mark: a file is edited as LF text without a
//! BOM and written back with both restored.

use std::borrow::Cow;

/// Line-ending style of a file.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LineEnding {
    Lf,
    CrLf,
}

/// The first line ending style in `content`; LF when there is none.
#[must_use]
pub fn detect_line_ending(content: &str) -> LineEnding {
    let Some(lf) = content.find('\n') else {
        return LineEnding::Lf;
    };
    match content.find("\r\n") {
        Some(crlf) if crlf < lf => LineEnding::CrLf,
        Some(_) | None => LineEnding::Lf,
    }
}

/// Turn every `\r\n` into `\n`. A lone `\r` is content and stays. Borrows
/// when nothing changes.
#[must_use]
pub fn normalize_to_lf(text: &str) -> Cow<'_, str> {
    if text.contains("\r\n") {
        Cow::Owned(text.replace("\r\n", "\n"))
    } else {
        Cow::Borrowed(text)
    }
}

/// The ending of each line of `content` that has one, in order: one item
/// for each `\n`. A `\n` with a `\r` right before it is CRLF.
#[must_use]
pub fn line_endings(content: &str) -> Vec<LineEnding> {
    let bytes = content.as_bytes();
    bytes
        .iter()
        .enumerate()
        .filter(|(_, byte)| **byte == b'\n')
        .map(
            |(at, _)| match at.checked_sub(1).map(|before| bytes[before]) {
                Some(b'\r') => LineEnding::CrLf,
                Some(_) | None => LineEnding::Lf,
            },
        )
        .collect()
}

/// Re-encode LF text with `ending`.
#[must_use]
pub fn restore_line_endings(text: &str, ending: LineEnding) -> String {
    match ending {
        LineEnding::Lf => text.to_owned(),
        LineEnding::CrLf => text.replace('\n', "\r\n"),
    }
}

/// The UTF-8 byte order mark.
pub const BOM: &str = "\u{FEFF}";

/// Split a leading BOM off `content`: `(bom, rest)`.
#[must_use]
pub fn strip_bom(content: &str) -> (&'static str, &str) {
    content
        .strip_prefix(BOM)
        .map_or(("", content), |rest| (BOM, rest))
}

/// What a file that is not UTF-8 text is: its BOM names UTF-16, else it is
/// some other encoding.
#[must_use]
pub(crate) fn encoding_name(bytes: &[u8]) -> &'static str {
    match bytes {
        [0xFF, 0xFE, ..] => "UTF-16 (little endian)",
        [0xFE, 0xFF, ..] => "UTF-16 (big endian)",
        _ => "not UTF-8",
    }
}

/// A byte count for messages: `512B`, `1.5KB`, `4.0MB`, `1.2GB`.
#[expect(
    clippy::cast_precision_loss,
    reason = "a one-decimal size label tolerates rounding"
)]
#[must_use]
pub(crate) fn format_bytes(bytes: u64) -> String {
    const KIB: u64 = 1024;
    if bytes < KIB {
        format!("{bytes}B")
    } else if bytes < KIB * KIB {
        format!("{:.1}KB", bytes as f64 / KIB as f64)
    } else if bytes < KIB * KIB * KIB {
        format!("{:.1}MB", bytes as f64 / (KIB * KIB) as f64)
    } else {
        format!("{:.1}GB", bytes as f64 / (KIB * KIB * KIB) as f64)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn crlf_round_trip_keeps_bom_and_endings() {
        let raw = "\u{FEFF}a\r\nb\r\n";
        let (bom, body) = strip_bom(raw);
        let ending = detect_line_ending(body);
        let lf = normalize_to_lf(body);
        assert_eq!(
            (bom, ending, lf.as_ref()),
            (BOM, LineEnding::CrLf, "a\nb\n")
        );
        assert_eq!(format!("{bom}{}", restore_line_endings(&lf, ending)), raw);
    }

    #[test]
    fn lone_cr_is_content() {
        assert_eq!(normalize_to_lf("a\rb\r\nc\r\r\n"), "a\rb\nc\r\n");
        assert_eq!(
            line_endings("a\rb\r\nc\r\r\nd\n"),
            vec![LineEnding::CrLf, LineEnding::CrLf, LineEnding::Lf]
        );
    }
}
