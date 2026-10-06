//! Terminal hyperlinks (OSC 8), gated on terminal capabilities.
//!
//! TS parity port of the link rendering split in
//! `packages/tui/src/components/markdown.ts` (`case "link"`): when the
//! terminal is positively known to implement OSC 8 hyperlinks
//! (`getCapabilities().hyperlinks`, `terminal-image.ts detectCapabilities`),
//! the link text is wrapped in an OSC 8 sequence pair so it is clickable and
//! the URL is never printed inline; otherwise the legacy form is used, with
//! the URL shown after the text unless it equals the link text.
//!
//! The renderer embeds the zero-width sequences in span content, exactly
//! like the TS renderer's ANSI strings: `width` skips them, and the inline
//! terminal writes them with the row, so terminals attach the hyperlink to
//! the cells printed between the open and close sequences.

use std::cell::RefCell;

use crate::Line;

/// OSC 8 open: starts a hyperlink region for `url`.
/// Byte-identical to the TS `hyperlink()` helper (`terminal-image.ts`).
#[must_use]
pub fn osc8_open(url: &str) -> String {
    format!("\x1b]8;;{url}\x1b\\")
}

/// OSC 8 close: ends the active hyperlink region.
pub const OSC8_CLOSE: &str = "\x1b]8;;\x1b\\";

/// TS `markdown.ts` `case "link"` href resolution: a WHATWG `new URL()`
/// pass. The deployed interactive renderer always sets `options.baseUrl`
/// (`assistant-message.ts` derives it from the session cwd), so every
/// non-fragment target that parses is emitted through
/// `new URL(target, baseUrl).href`: absolute urls canonicalize (a bare
/// host gains its `/`, the scheme and host lower-case). `WhatWG` parsing
/// with no base only succeeds for absolute urls, so relative targets pass
/// through raw here - the one documented gap: resolving them against the
/// session cwd needs cwd plumbing the markdown pipeline does not carry,
/// and no battery covers a relative link target.
#[must_use]
pub fn resolve_link_href(target: &str) -> String {
    if target.starts_with('#') {
        return sanitize_control_bytes(target.to_string());
    }
    match url::Url::parse(target) {
        Ok(parsed) => parsed.to_string(),
        Err(_) => sanitize_control_bytes(target.to_string()),
    }
}

/// The parse-bypass paths above return the target raw, exactly like the
/// TS renderer (its `!target.startsWith('#')` short-circuit and the
/// `canParse` fallthrough both hand the raw string to `hyperlink()`).
/// A raw C0/DEL byte in that string would ride the OSC 8 `href` field as
/// a second terminal escape (e.g. an OSC 52 clipboard write), so those
/// paths percent-encode the bytes first - the same bytes WHATWG URL
/// parsing percent-encodes on every parseable target in both products.
/// The TS renderer shares the hole (its fragment and unparseable targets
/// reach `hyperlink()` unsanitized); this is deliberate hardening past
/// parity on an input class no battery covers. The markdown URL bracket
/// applies the same hardening to the destination it renders as visible
/// text.
pub(crate) fn sanitize_control_bytes(target: String) -> String {
    if !target
        .as_bytes()
        .iter()
        .any(|&b| matches!(b, 0x00..=0x1f | 0x7f))
    {
        return target;
    }
    let mut out = Vec::with_capacity(target.len());
    for byte in target.bytes() {
        if matches!(byte, 0x00..=0x1f | 0x7f) {
            out.extend_from_slice(format!("%{byte:02X}").as_bytes());
        } else {
            out.push(byte);
        }
    }
    // Only ASCII control bytes were replaced; the remaining bytes are the
    // original valid UTF-8 sequence.
    String::from_utf8(out).expect("utf-8 survives ASCII percent-encoding")
}

/// The env-based hyperlink-capability gate (TS `detectCapabilities`):
/// hyperlinks are enabled only in terminals positively known to implement
/// OSC 8, forced off under tmux/screen (which swallow the sequences by
/// default), and off in unknown terminals (a swallowed OSC 8 hides the URL
/// from the rendered output).
#[must_use]
pub fn hyperlinks_enabled() -> bool {
    if let Some(overridden) = OVERRIDE.with(|c| *c.borrow()) {
        return overridden;
    }
    let term_program = std::env::var("TERM_PROGRAM")
        .unwrap_or_default()
        .to_lowercase();
    let term = std::env::var("TERM").unwrap_or_default().to_lowercase();
    let in_tmux_or_screen = std::env::var_os("TMUX").is_some()
        || term.starts_with("tmux")
        || term.starts_with("screen");
    if in_tmux_or_screen {
        return false;
    }
    if std::env::var_os("KITTY_WINDOW_ID").is_some() || term_program == "kitty" {
        return true;
    }
    if term_program == "ghostty"
        || term.contains("ghostty")
        || std::env::var_os("GHOSTTY_RESOURCES_DIR").is_some()
    {
        return true;
    }
    if std::env::var_os("WEZTERM_PANE").is_some() || term_program == "wezterm" {
        return true;
    }
    if std::env::var_os("ITERM_SESSION_ID").is_some() || term_program == "iterm.app" {
        return true;
    }
    matches!(term_program.as_str(), "vscode" | "alacritty")
}

thread_local! {
    /// Test seam mirroring TS `setCapabilities`: force the capability
    /// decision regardless of the environment. `None` restores detection.
    static OVERRIDE: RefCell<Option<bool>> = const { RefCell::new(None) };
}

/// Set (or clear) the test override for the capability gate.
pub fn set_hyperlinks_override(enabled: Option<bool>) {
    OVERRIDE.with(|c| *c.borrow_mut() = enabled);
}

/// One link region of composed rows: row, visible column range, and
/// destination URL (the renderers' tests read where a link landed).
#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinkRange {
    pub row: usize,
    pub start_col: usize,
    pub end_col: usize,
    pub url: String,
}

/// Scan a composed frame for OSC 8 sequences embedded in span content and
/// convert them into row/column ranges (the paint-time truth). The
/// sequences are zero-width, so visible columns are unaffected. A link left
/// open at a row end (its label wrapped mid-link) extends to the end of the
/// row and resumes at column 0 of the next row, matching the TS renderer's
/// stream where the region stays open across the wrap.
#[cfg(test)]
#[must_use]
pub fn frame_link_ranges(frame: &[Line]) -> Vec<LinkRange> {
    let mut ranges: Vec<LinkRange> = Vec::new();
    let mut carry: Option<(usize, usize, String)> = None;
    for row in 0..frame.len() {
        let mut col = 0usize;
        for span in &frame[row] {
            scan_span(&span.content, row, &mut col, &mut carry, &mut ranges);
        }
        if let Some((start_row, start_col, url)) = carry.take() {
            // A label wrapped mid-link closes its piece at the row end and
            // resumes at column 0 of the next row (the original start row
            // only matters for pieces closed inside `scan_span`).
            let _ = start_row;
            ranges.push(LinkRange {
                row,
                start_col,
                end_col: col,
                url: url.clone(),
            });
            if row + 1 < frame.len() {
                carry = Some((row + 1, 0, url));
            }
        }
    }
    ranges
}

#[cfg(test)]
fn scan_span(
    content: &str,
    row: usize,
    col: &mut usize,
    carry: &mut Option<(usize, usize, String)>,
    ranges: &mut Vec<LinkRange>,
) {
    let mut i = 0usize;
    while i < content.len() {
        if let Some(len) = crate::width::escape_len(&content[i..]) {
            let seq = &content[i..i + len];
            if seq.starts_with("\x1b]8;;") && !is_osc8_close(seq) {
                let url = &seq["\x1b]8;;".len()..];
                let url = url.strip_suffix("\x1b\\").unwrap_or(url);
                if let Some((start_row, start_col, url)) = carry.take() {
                    ranges.push(LinkRange {
                        row: start_row,
                        start_col,
                        end_col: *col,
                        url,
                    });
                }
                *carry = Some((row, *col, url.to_string()));
            } else if is_osc8_close(seq) {
                if let Some((start_row, start_col, url)) = carry.take() {
                    ranges.push(LinkRange {
                        row: start_row,
                        start_col,
                        end_col: *col,
                        url,
                    });
                }
            }
            i += len;
            continue;
        }
        let ch = content[i..].chars().next().expect("char at byte index");
        *col += crate::width::char_width(ch);
        i += ch.len_utf8();
    }
}

fn is_osc8_close(seq: &str) -> bool {
    seq == OSC8_CLOSE || seq == "\x1b]8;;\x07"
}

/// Remove OSC 8 sequences from a rendered line's span contents (the
/// plain-text frame dumps must not see the zero-width bytes).
pub fn strip_osc8(line: &mut Line) {
    for span in line.iter_mut() {
        if span.content.contains("\x1b]8;;") {
            span.content = strip_osc8_content(&span.content);
        }
    }
}

/// Remove OSC 8 open/close sequences from a string, preserving every other
/// escape sequence (OSC 133 zone markers ride in the same contents).
///
/// # Panics
///
/// Cannot panic for any valid `str`: the `expect` guards the scanner
/// invariant that the loop only ever advances by whole escape sequences
/// and chars, so a char always starts at the visited index.
#[must_use]
pub fn strip_osc8_content(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut i = 0usize;
    while i < text.len() {
        if let Some(len) = crate::width::escape_len(&text[i..]) {
            let seq = &text[i..i + len];
            let is_open = seq.starts_with("\x1b]8;;") && !is_osc8_close(seq);
            if !is_open && !is_osc8_close(seq) {
                out.push_str(seq);
            }
            i += len;
            continue;
        }
        let ch = text[i..].chars().next().expect("char at byte index");
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Span;

    #[test]
    fn resolve_link_href_canonicalizes_parseable_targets() {
        // The deployed renderer always sets baseUrl, so every parseable
        // non-fragment href goes through `new URL().href`: hosts gain a
        // trailing `/`, scheme and host lower-case. Unparseable targets
        // and fragments pass raw.
        assert_eq!(
            resolve_link_href("https://x.dev/a?b=1"),
            "https://x.dev/a?b=1"
        );
        assert_eq!(resolve_link_href("https://bare.dev"), "https://bare.dev/");
        assert_eq!(
            resolve_link_href("HTTPS://UPPER.COM/PATH"),
            "https://upper.com/PATH"
        );
        assert_eq!(resolve_link_href("mailto:a@b.dev"), "mailto:a@b.dev");
        assert_eq!(resolve_link_href("see docs"), "see docs");
        assert_eq!(resolve_link_href("#section"), "#section");
    }

    #[test]
    fn parse_bypass_targets_percent_encode_control_bytes() {
        // Fragment and unparseable targets reach the OSC 8 href raw (the
        // TS renderer's own bypass paths); a raw control byte there would
        // ride the terminal stream as a second escape (an OSC 52 clipboard
        // write), so those paths percent-encode C0 and DEL first - the
        // same bytes URL parsing encodes on every parseable target.
        assert_eq!(resolve_link_href("#a]52;cb"), "#a%1B]52;c%07b");
        assert_eq!(resolve_link_href("not a url]8;;x"), "not a url%1B]8;;x");
        assert_eq!(resolve_link_href("#s"), "#s%7F");
        // Printable fragments stay untouched, byte-identical to TS.
        assert_eq!(resolve_link_href("#section"), "#section");
    }

    #[test]
    fn osc8_helpers_match_ts_format() {
        assert_eq!(
            osc8_open("https://x.dev/a"),
            "\x1b]8;;https://x.dev/a\x1b\\"
        );
        assert_eq!(OSC8_CLOSE, "\x1b]8;;\x1b\\");
    }

    #[test]
    fn frame_link_ranges_cover_label_cells() {
        let row0 = vec![
            Span::raw("see "),
            Span::raw(osc8_open("https://x.dev/a")),
            Span::raw("the docs"),
            Span::raw(OSC8_CLOSE),
        ];
        let row1 = vec![Span::raw("tail row")];
        let ranges = frame_link_ranges(&[row0, row1]);
        assert_eq!(
            ranges,
            vec![LinkRange {
                row: 0,
                start_col: 4,
                end_col: 12,
                url: "https://x.dev/a".to_string(),
            }]
        );
    }

    #[test]
    fn open_link_wraps_to_row_end_and_next_row() {
        let frame = vec![
            vec![Span::raw(osc8_open("https://x.dev")), Span::raw("abc")],
            vec![Span::raw("def"), Span::raw(OSC8_CLOSE)],
        ];
        let ranges = frame_link_ranges(&frame);
        assert_eq!(
            ranges,
            vec![
                LinkRange {
                    row: 0,
                    start_col: 0,
                    end_col: 3,
                    url: "https://x.dev".to_string(),
                },
                LinkRange {
                    row: 1,
                    start_col: 0,
                    end_col: 3,
                    url: "https://x.dev".to_string(),
                },
            ]
        );
    }

    #[test]
    fn strip_removes_only_osc8() {
        let mut line = vec![
            Span::raw(crate::osc133::ZONE_START),
            Span::raw("pre "),
            Span::raw(format!("{}txt{}", osc8_open("https://x"), OSC8_CLOSE)),
        ];
        strip_osc8(&mut line);
        let joined: String = line.iter().map(|s| s.content.as_str()).collect();
        assert_eq!(joined, "\x1b]133;A\x07pre txt");
        assert_eq!(
            strip_osc8_content("a\x1b]8;;https://y\x1b\\b\x1b]8;;\x1b\\c"),
            "abc"
        );
    }
}
