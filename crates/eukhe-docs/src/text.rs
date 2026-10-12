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

/// Normalize every `\r\n` and lone `\r` to `\n`. Borrows when nothing changes.
#[must_use]
pub fn normalize_to_lf(text: &str) -> Cow<'_, str> {
    if !text.contains('\r') {
        return Cow::Borrowed(text);
    }
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars().peekable();
    while let Some(ch) = chars.next() {
        if ch == '\r' {
            if chars.peek() == Some(&'\n') {
                chars.next();
            }
            out.push('\n');
        } else {
            out.push(ch);
        }
    }
    Cow::Owned(out)
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
    fn lone_cr_becomes_lf() {
        assert_eq!(normalize_to_lf("a\rb\r\nc"), "a\nb\nc");
    }
}
