//! How a step is shown to the user: exactly what runs, with no character
//! that a terminal hides or moves (control characters, bidi and other
//! invisible format characters).

use std::fmt::Write as _;

/// Whether a terminal hides `c` or moves the text around it: a control
/// character (newline and tab too), or an invisible format character
/// (bidi embeddings, overrides and isolates, zero-width characters, the
/// byte-order mark, the soft hyphen).
fn hidden(c: char) -> bool {
    c.is_control()
        || matches!(
            c,
            '\u{00ad}'
                | '\u{061c}'
                | '\u{180e}'
                | '\u{200b}'..='\u{200f}'
                | '\u{2028}'..='\u{202e}'
                | '\u{2060}'..='\u{2069}'
                | '\u{feff}'
        )
}

/// `text` quoted for bash when it needs quotes. A word with a hidden
/// character is ANSI-C quoted (`$'…'`) with each such character escaped,
/// so the shown word holds none of them and bash reads it back as `text`.
pub(crate) fn quote(text: &str) -> String {
    let plain = !text.is_empty()
        && text
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || "_./=:,+@%^-".contains(c));
    if plain {
        text.to_string()
    } else if text.chars().any(hidden) {
        let mut quoted = String::from("$'");
        for c in text.chars() {
            match c {
                '\\' => quoted.push_str("\\\\"),
                '\'' => quoted.push_str("\\'"),
                '\n' => quoted.push_str("\\n"),
                '\t' => quoted.push_str("\\t"),
                '\r' => quoted.push_str("\\r"),
                c if hidden(c) => {
                    let code = u32::from(c);
                    // Writing to a String cannot fail.
                    let _ = if code < 0x100 {
                        write!(quoted, "\\x{code:02x}")
                    } else {
                        write!(quoted, "\\u{code:04x}")
                    };
                }
                c => quoted.push(c),
            }
        }
        quoted.push('\'');
        quoted
    } else {
        format!("'{}'", text.replace('\'', "'\\''"))
    }
}

/// `text` (a cell of code, many lines) with every hidden character but
/// the newline and the tab written as `\u{…}`: what the user reads is
/// what runs, line for line.
#[must_use]
pub fn visible(text: &str) -> String {
    let mut shown = String::with_capacity(text.len());
    for c in text.chars() {
        if hidden(c) && c != '\n' && c != '\t' {
            // Writing to a String cannot fail.
            let _ = write!(shown, "\\u{{{:x}}}", u32::from(c));
        } else {
            shown.push(c);
        }
    }
    shown
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Regression (audit M3): a word with ESC, CR or a bidi override was
    /// shown raw, so the prompt could hide part of the step.
    #[test]
    fn a_hidden_character_is_escaped_and_bash_reads_the_word_back() {
        let words = [
            "plain-word",
            "two words",
            "it's",
            "evil\u{1b}[2K\rsafe",
            "a\u{202e}txt.exe",
            "tab\there\nline",
            "back\\slash'\u{7f}",
        ];
        let shown: Vec<String> = words.iter().map(|word| quote(word)).collect();
        assert_eq!(
            shown,
            [
                "plain-word",
                "'two words'",
                "'it'\\''s'",
                "$'evil\\x1b[2K\\rsafe'",
                "$'a\\u202etxt.exe'",
                "$'tab\\there\\nline'",
                "$'back\\\\slash\\'\\x7f'",
            ]
        );
        assert!(shown.iter().all(|word| !word.chars().any(hidden)));
        // bash reads each shown word back as the word.
        let script = shown
            .iter()
            .map(|word| format!("printf '%s\\0' {word}"))
            .collect::<Vec<_>>()
            .join("; ");
        let out = std::process::Command::new("bash")
            .args(["-c", &script])
            .env("LC_ALL", "C.UTF-8")
            .output()
            .unwrap();
        let read: Vec<String> = out
            .stdout
            .split(|&byte| byte == 0)
            .filter(|part| !part.is_empty())
            .map(|part| String::from_utf8(part.to_vec()).unwrap())
            .collect();
        assert_eq!(read, words);
    }

    #[test]
    fn visible_keeps_lines_and_escapes_the_rest() {
        assert_eq!(
            visible("print(1)\n\tx = '\u{1b}[31m'\u{2066}"),
            "print(1)\n\tx = '\\u{1b}[31m'\\u{2066}"
        );
    }
}
