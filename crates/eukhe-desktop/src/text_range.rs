//! Locating text inside an element's value for `select_text` (port of omp
//! `crates/natives/src/desktop/text_range.rs`).
//!
//! Accessibility text ranges count UTF-16 code units, so every offset here is
//! in UTF-16 units, never UTF-8 bytes or Unicode scalars.

use std::fmt;

use serde::{Deserialize, Serialize};

use crate::types::Focus;

/// How many match offsets an ambiguity error lists.
const LISTED_MATCHES: usize = 8;

/// Which part of the matched text becomes the selection.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SelectPart {
    /// The matched text itself.
    #[default]
    Text,
    /// A zero-length caret before the match.
    Start,
    /// A zero-length caret after the match.
    End,
}

/// Selects `text` where it follows `prefix` and precedes `suffix`; empty
/// context matches anywhere.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct TextSelectRequest {
    pub text: String,
    #[serde(default)]
    pub prefix: String,
    #[serde(default)]
    pub suffix: String,
    #[serde(default)]
    pub part: SelectPart,
}

/// The selection read back after `select_text`, in UTF-16 code units.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TextSelection {
    pub start: u32,
    pub length: u32,
    /// The selected text, empty for a caret.
    pub text: String,
    /// Typing and accessibility insertion act on the focused element.
    pub focus: Focus,
}

/// A selection in UTF-16 code units.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Utf16Range {
    pub(crate) start: usize,
    pub(crate) length: usize,
}

/// The context a request gives, as errors name it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Context {
    pub prefix: String,
    pub suffix: String,
}

impl fmt::Display for Context {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match (self.prefix.is_empty(), self.suffix.is_empty()) {
            (false, false) => write!(
                f,
                "after prefix {:?} and before suffix {:?}",
                self.prefix, self.suffix
            ),
            (false, true) => write!(f, "after prefix {:?}", self.prefix),
            (true, false) => write!(f, "before suffix {:?}", self.suffix),
            (true, true) => f.write_str("anywhere"),
        }
    }
}

/// Why a request named no single range.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum TextRangeError {
    #[error(
        "text is empty and no prefix or suffix says where to put the caret; nothing was selected"
    )]
    Unplaced,
    #[error("{text:?} does not occur in the element's value ({units} UTF-16 units); nothing was selected")]
    Missing { text: String, units: usize },
    #[error("no position in the element's value is {context}; nothing was selected")]
    NoPosition { context: Context },
    #[error("{text:?} occurs {occurrences} time(s) in the element's value, but none {context}; nothing was selected")]
    OutsideContext {
        text: String,
        occurrences: usize,
        context: Context,
    },
    #[error("{text:?} occurs {matched} times {context} (UTF-16 offsets {}), so it is ambiguous; give a longer prefix or suffix to choose one; nothing was selected", Offsets::new(.offsets, .matched))]
    Ambiguous {
        text: String,
        matched: usize,
        context: Context,
        /// The first matches' offsets.
        offsets: Vec<usize>,
    },
}

struct Offsets<'a> {
    listed: &'a [usize],
    matched: &'a usize,
}

impl<'a> Offsets<'a> {
    fn new(listed: &'a [usize], matched: &'a usize) -> Self {
        Self { listed, matched }
    }
}

impl fmt::Display for Offsets<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (index, start) in self.listed.iter().enumerate() {
            if index > 0 {
                f.write_str(", ")?;
            }
            write!(f, "{start}")?;
        }
        if *self.matched > self.listed.len() {
            f.write_str(", …")?;
        }
        Ok(())
    }
}

impl TextSelectRequest {
    /// The one range of `value` this request names. Refuses when the text does
    /// not occur, occurs only outside the given context, or occurs more than
    /// once in it.
    pub(crate) fn locate(&self, value: &str) -> Result<Utf16Range, TextRangeError> {
        if self.text.is_empty() && self.prefix.is_empty() && self.suffix.is_empty() {
            return Err(TextRangeError::Unplaced);
        }
        let mut occurrences = 0usize;
        let mut offsets = Vec::with_capacity(LISTED_MATCHES);
        let mut matched = 0usize;
        let mut units = 0usize;
        let boundaries = value
            .char_indices()
            .map(|(byte, character)| (byte, character.len_utf16()))
            .chain(std::iter::once((value.len(), 0)));
        for (byte, width) in boundaries {
            let rest = &value[byte..];
            if let Some(after) = rest.strip_prefix(self.text.as_str()) {
                occurrences += 1;
                if value[..byte].ends_with(&self.prefix) && after.starts_with(&self.suffix) {
                    if offsets.len() < LISTED_MATCHES {
                        offsets.push(units);
                    }
                    matched += 1;
                }
            }
            units += width;
        }
        match (matched, offsets.as_slice()) {
            (1, [start]) => Ok(self.range_at(*start)),
            (0, _) if occurrences == 0 => Err(TextRangeError::Missing {
                text: self.text.clone(),
                units,
            }),
            (0, _) if self.text.is_empty() => Err(TextRangeError::NoPosition {
                context: self.context(),
            }),
            (0, _) => Err(TextRangeError::OutsideContext {
                text: self.text.clone(),
                occurrences,
                context: self.context(),
            }),
            (_, _) => Err(TextRangeError::Ambiguous {
                text: self.text.clone(),
                matched,
                context: self.context(),
                offsets,
            }),
        }
    }

    fn range_at(&self, start: usize) -> Utf16Range {
        let length = self.text.encode_utf16().count();
        match self.part {
            SelectPart::Text => Utf16Range { start, length },
            SelectPart::Start => Utf16Range { start, length: 0 },
            SelectPart::End => Utf16Range {
                start: start + length,
                length: 0,
            },
        }
    }

    fn context(&self) -> Context {
        Context {
            prefix: self.prefix.clone(),
            suffix: self.suffix.clone(),
        }
    }
}

/// The text of `value` in a UTF-16 range, or `None` when the range runs past
/// the end or splits a surrogate pair.
pub(crate) fn utf16_slice(value: &str, range: Utf16Range) -> Option<&str> {
    value.get(utf16_byte_range(value, range)?)
}

/// The UTF-8 byte range of a UTF-16 range in `value`, or `None` when the range
/// runs past the end or splits a surrogate pair.
fn utf16_byte_range(value: &str, range: Utf16Range) -> Option<std::ops::Range<usize>> {
    let start = utf16_byte_offset(value, range.start)?;
    let end = utf16_byte_offset(value, range.start.checked_add(range.length)?)?;
    Some(start..end)
}

fn utf16_byte_offset(value: &str, offset: usize) -> Option<usize> {
    let mut units = 0;
    for (byte, character) in value.char_indices() {
        if units == offset {
            return Some(byte);
        }
        if units > offset {
            return None;
        }
        units += character.len_utf16();
    }
    (units == offset).then_some(value.len())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn request(text: &str, prefix: &str, suffix: &str, part: SelectPart) -> TextSelectRequest {
        TextSelectRequest {
            text: text.to_owned(),
            prefix: prefix.to_owned(),
            suffix: suffix.to_owned(),
            part,
        }
    }

    fn range(start: usize, length: usize) -> Utf16Range {
        Utf16Range { start, length }
    }

    #[test]
    fn offsets_count_utf16_units() {
        let value = "😀 café 😀 tea";
        let tea = request("tea", "", "", SelectPart::Text).locate(value);
        assert_eq!(tea, Ok(range(11, 3)));
        assert_eq!(utf16_slice(value, range(11, 3)), Some("tea"));
        assert_eq!(
            request("😀", "café ", "", SelectPart::End).locate(value),
            Ok(range(10, 0))
        );
        assert_eq!(utf16_slice("a😀b", range(2, 1)), None);
    }

    #[test]
    fn repeated_text_is_ambiguous_until_context_picks_one() {
        let value = "red cat, blue cat, red cat";
        assert_eq!(
            request("cat", "", "", SelectPart::Text).locate(value),
            Err(TextRangeError::Ambiguous {
                text: "cat".to_owned(),
                matched: 3,
                context: Context {
                    prefix: String::new(),
                    suffix: String::new()
                },
                offsets: vec![4, 14, 23],
            })
        );
        assert_eq!(
            request("cat", "blue ", "", SelectPart::Text).locate(value),
            Ok(range(14, 3))
        );
    }
}
