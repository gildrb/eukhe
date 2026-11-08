//! Remote-text hygiene for human output. Session names, notes, model
//! answers, and log lines are data, never instructions: a crafted name can
//! rewrite the terminal or impersonate CLI output. Human output strips the
//! controls that can do that; JSON keeps the raw value.

/// Characters that can reorder, hide, or spoof displayed text: bidi
/// controls, zero-width and soft-break format characters, and the BOM.
pub(crate) fn is_invisible_format(c: char) -> bool {
    matches!(c as u32,
        0x00..=0x08 | 0x0B..=0x0C | 0x0E..=0x1F | 0x7F          // C0 except \n \t
        | 0x80..=0x9F                                            // C1
        | 0x200B..=0x200F                                        // zero width + marks
        | 0x202A..=0x202E                                        // bidi embedding
        | 0x2060..=0x2064                                        // invisible operators
        | 0x2066..=0x2069                                        // bidi isolate
        | 0xFEFF | 0x00AD                                        // BOM, soft hyphen
    )
}

/// Strip terminal-escape sequences (CSI, OSC, and two-character escapes)
/// from a string that may contain them split across a filter's output.
fn strip_escape_sequences(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        if c != '\x1b' {
            out.push(c);
            continue;
        }
        match chars.peek() {
            Some('[') => {
                // CSI: parameter and intermediate bytes, then one final byte.
                chars.next();
                while let Some(&next) = chars.peek() {
                    chars.next();
                    if ('\u{40}'..='\u{7e}').contains(&next) {
                        break;
                    }
                }
            }
            Some(']') => {
                // OSC: terminated by BEL or ST (ESC \).
                chars.next();
                let mut terminated = false;
                while let Some(next) = chars.next() {
                    if next == '\x07' {
                        terminated = true;
                        break;
                    }
                    if next == '\x1b' && chars.peek() == Some(&'\\') {
                        chars.next();
                        terminated = true;
                        break;
                    }
                }
                if !terminated {
                    break;
                }
            }
            Some(_) => {
                // A two-character escape: drop the following byte.
                chars.next();
            }
            None => {}
        }
    }
    out
}

/// Human-safe multi-line text: escape sequences, C0/C1 controls, and
/// invisible format characters removed; newlines and tabs kept.
#[must_use]
pub fn text(raw: &str) -> String {
    strip_escape_sequences(raw)
        .chars()
        .filter(|c| !is_invisible_format(*c))
        .collect()
}

/// Human-safe single-line text: like [`text`], with newlines and tabs
/// shown as visible `\n` and `\t` escapes so one row stays one row.
#[must_use]
pub fn line(raw: &str) -> String {
    let clean = text(raw);
    let mut out = String::with_capacity(clean.len());
    for c in clean.chars() {
        match c {
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            other => out.push(other),
        }
    }
    out
}
