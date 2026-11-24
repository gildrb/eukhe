//! Whether a written value reads back as sent (port of `text_readback` in
//! omp `crates/natives/src/desktop/ax.rs`).

use crate::error::{FieldReads, Readback};

/// Whether a field hides its value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FieldKind {
    Plain,
    Secure,
}

/// What stands in for the written text where a read-back repeats it.
const WRITTEN: &str = "<the written text>";
/// Characters of a read-back a refusal quotes.
const SHOWN: usize = 200;

/// Exact equality or a same-length mask is the verdict: a reformatted value
/// was not shown to hold what was sent. `sent` was written so the field
/// should read `expected`; `actual` is what it reads, `None` when unread.
pub(crate) fn text_readback(
    sent: &str,
    expected: &str,
    actual: Option<&str>,
    field: FieldKind,
) -> Result<(), Readback> {
    if actual == Some(expected) || actual.is_some_and(|actual| masks(actual, expected)) {
        return Ok(());
    }
    let reads = match (actual, field) {
        (None, FieldKind::Secure) => FieldReads::SecureUnconfirmed,
        (None, FieldKind::Plain) => FieldReads::Unreadable,
        (Some(""), _) => FieldReads::Empty,
        (Some(actual), _) if masked(actual) => FieldReads::Mask {
            chars: actual.chars().count(),
        },
        (Some(_), FieldKind::Secure) => FieldReads::SecureHidden,
        (Some(actual), FieldKind::Plain) => FieldReads::Text {
            text: cut(&if sent.is_empty() {
                actual.to_owned()
            } else {
                actual.replace(sent, WRITTEN)
            }),
        },
    };
    Err(Readback {
        sent: sent.chars().count(),
        expected: (sent != expected).then(|| expected.chars().count()),
        reads,
    })
}

/// `text` cut to [`SHOWN`] characters, the last an ellipsis when cut.
fn cut(text: &str) -> String {
    if text.chars().nth(SHOWN).is_none() {
        return text.to_owned();
    }
    let mut shown: String = text.chars().take(SHOWN - 1).collect();
    shown.push('…');
    shown
}

/// Whether `actual` is one repeated mask character.
fn masked(actual: &str) -> bool {
    let mut chars = actual.chars();
    chars.next().is_some_and(|first| {
        ['●', '•', '✱', '✺', '*'].contains(&first) && chars.all(|char| char == first)
    })
}

/// Whether `actual` masks `value`: one mask character per character or
/// UTF-16 unit.
fn masks(actual: &str, value: &str) -> bool {
    let shown = actual.chars().count();
    masked(actual) && (shown == value.chars().count() || shown == value.encode_utf16().count())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_reformatted_value_is_unconfirmed_without_quoting_the_text() {
        assert_eq!(
            text_readback("abc", "abc", Some("abc"), FieldKind::Plain),
            Ok(())
        );
        assert_eq!(
            text_readback("pw", "pw", Some("••"), FieldKind::Secure),
            Ok(())
        );
        assert_eq!(
            text_readback("555", "x555", Some("x 555 !"), FieldKind::Plain),
            Err(Readback {
                sent: 3,
                expected: Some(4),
                reads: FieldReads::Text {
                    text: "x <the written text> !".to_owned()
                },
            })
        );
    }
}
