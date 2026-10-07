//! UTF-16 code-unit counting and slicing for JS `.length` / `.slice`
//! semantics on Rust strings.
//!
//! JS strings index UTF-16 code units. Rust strings cannot hold a lone
//! surrogate, so an offset that falls inside a surrogate pair never splits it:
//! a start offset moves past the whole character and an end offset stops
//! before it.

/// JS `text.length`: the number of UTF-16 code units.
#[must_use]
pub fn utf16_len(text: &str) -> usize {
    text.chars().map(char::len_utf16).sum()
}

/// Byte offset of the first character boundary at or after `units` code units
/// (`text.len()` when `units` reaches the end).
#[must_use]
pub fn utf16_ceil_byte_offset(text: &str, units: usize) -> usize {
    let mut counted = 0;
    for (offset, character) in text.char_indices() {
        if counted >= units {
            return offset;
        }
        counted += character.len_utf16();
    }
    text.len()
}

/// Byte offset of the last character boundary at or before `units` code
/// units (`text.len()` when `units` reaches the end).
#[must_use]
pub fn utf16_floor_byte_offset(text: &str, units: usize) -> usize {
    let mut counted = 0;
    for (offset, character) in text.char_indices() {
        let next = counted + character.len_utf16();
        if next > units {
            return offset;
        }
        counted = next;
    }
    text.len()
}

/// JS `text.slice(0, units)` without splitting a character: the longest
/// prefix of at most `units` code units.
#[must_use]
pub fn utf16_prefix(text: &str, units: usize) -> &str {
    &text[..utf16_floor_byte_offset(text, units)]
}

/// JS `text.slice(units)` without splitting a character: the text after the
/// first `units` code units, starting at the next character boundary.
#[must_use]
pub fn utf16_skip(text: &str, units: usize) -> &str {
    &text[utf16_ceil_byte_offset(text, units)..]
}

/// JS `text.slice(text.length - units)` without splitting a character: the
/// longest suffix of at most `units` code units.
#[must_use]
pub fn utf16_suffix(text: &str, units: usize) -> &str {
    let length = utf16_len(text);
    utf16_skip(text, length.saturating_sub(units))
}

/// JS `text.slice(start, end)` for `start <= end` without splitting a
/// character: `start` rounds up and `end` rounds down to character
/// boundaries. Empty when the rounded range is empty.
#[must_use]
pub fn utf16_slice(text: &str, start: usize, end: usize) -> &str {
    let from = utf16_ceil_byte_offset(text, start);
    let to = utf16_floor_byte_offset(text, end);
    if from >= to {
        ""
    } else {
        &text[from..to]
    }
}

/// The UTF-16 code units of `text`, for code-unit-exact comparisons.
pub(crate) fn utf16_units(text: &str) -> Vec<u16> {
    text.encode_utf16().collect()
}

#[cfg(test)]
mod tests {
    use super::{utf16_len, utf16_prefix, utf16_skip, utf16_slice, utf16_suffix};

    #[test]
    fn counts_and_slices_code_units() {
        let text = "a😀b";
        assert_eq!(utf16_len(text), 4);
        assert_eq!(utf16_prefix(text, 1), "a");
        assert_eq!(utf16_prefix(text, 2), "a");
        assert_eq!(utf16_prefix(text, 3), "a😀");
        assert_eq!(utf16_skip(text, 1), "😀b");
        assert_eq!(utf16_skip(text, 2), "b");
        assert_eq!(utf16_skip(text, 9), "");
        assert_eq!(utf16_suffix(text, 1), "b");
        assert_eq!(utf16_suffix(text, 2), "b");
        assert_eq!(utf16_suffix(text, 3), "😀b");
        assert_eq!(utf16_slice(text, 1, 3), "😀");
        assert_eq!(utf16_slice(text, 2, 3), "");
    }
}
