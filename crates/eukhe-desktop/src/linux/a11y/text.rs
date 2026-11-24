//! AT-SPI text offsets count characters; the session counts UTF-16 units
//! (port of the offset conversions in omp `crates/natives/src/desktop/linux/ax.rs`).

use crate::text_range::Utf16Range;

/// The character offsets `[start, end)` of a UTF-16 range in `value`; `None`
/// past the end or inside a surrogate pair.
pub(super) fn char_span(value: &str, range: Utf16Range) -> Option<(i32, i32)> {
    let end = range.start.checked_add(range.length)?;
    let start = char_offset(value, range.start)?;
    let end = char_offset(value, end)?;
    Some((i32::try_from(start).ok()?, i32::try_from(end).ok()?))
}

fn char_offset(value: &str, units: usize) -> Option<usize> {
    let mut seen = 0;
    for (index, character) in value.chars().enumerate() {
        if seen == units {
            return Some(index);
        }
        if seen > units {
            return None;
        }
        seen += character.len_utf16();
    }
    (seen == units).then(|| value.chars().count())
}

/// The UTF-16 range of the character offsets `[start, end)` in `value`, in
/// either order; `None` past the end.
pub(super) fn utf16_span(value: &str, start: i32, end: i32) -> Option<Utf16Range> {
    let (low, high) = (start.min(end), start.max(end));
    let low = usize::try_from(low).ok()?;
    let high = usize::try_from(high).ok()?;
    let units = |chars: usize| -> Option<usize> {
        (chars <= value.chars().count())
            .then(|| value.chars().take(chars).map(char::len_utf16).sum())
    };
    let start = units(low)?;
    Some(Utf16Range {
        start,
        length: units(high)? - start,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn offsets_convert_across_astral_characters() {
        let value = "a😀b";
        let range = Utf16Range {
            start: 1,
            length: 3,
        };
        assert_eq!(char_span(value, range), Some((1, 3)));
        assert_eq!(utf16_span(value, 3, 1), Some(range));
        assert_eq!(
            char_span(
                value,
                Utf16Range {
                    start: 2,
                    length: 0
                }
            ),
            None
        );
        assert_eq!(utf16_span(value, 0, 4), None);
        assert_eq!(
            char_span(
                value,
                Utf16Range {
                    start: 4,
                    length: 0
                }
            ),
            Some((3, 3))
        );
    }
}
