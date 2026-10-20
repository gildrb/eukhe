//! The one token estimate from text (TS pi-ai `CHARS_PER_TOKEN = 3.5`):
//! `ceil(chars / 3.5)`, where `chars` is the text length in UTF-16 code
//! units (the JS `String.length`). Every local estimate of a token count
//! from text uses it: the compaction threshold, the output clamp, the
//! context usage the clients show, the summary-model routing, and the live
//! output count and generation speed of the TUI and the dashboard. The
//! dashboard's `CHARS_PER_TOKEN` (`eukhe-dashboard/ui/src/lib/turn.ts`) is
//! pinned to this ratio by a test.

/// Characters per token as the exact fraction 7/2 (3.5): the numerator.
pub const CHARS_PER_TOKEN_NUMERATOR: u64 = 7;
/// Characters per token as the exact fraction 7/2 (3.5): the denominator.
pub const CHARS_PER_TOKEN_DENOMINATOR: u64 = 2;
/// The characters one image counts as (about 1,371 tokens).
pub const ESTIMATED_IMAGE_CHARS: u64 = 4800;

/// Estimated tokens of `chars` characters: `ceil(chars / 3.5)`.
#[must_use]
pub const fn chars_to_tokens(chars: u64) -> u64 {
    chars
        .saturating_mul(CHARS_PER_TOKEN_DENOMINATOR)
        .div_ceil(CHARS_PER_TOKEN_NUMERATOR)
}

/// The length of `text` in the unit of the estimate: UTF-16 code units
/// (JS `String.length`).
#[must_use]
pub fn text_chars(text: &str) -> u64 {
    text.chars().map(|c| c.len_utf16() as u64).sum()
}

/// Estimated tokens of a text: [`chars_to_tokens`] of [`text_chars`].
#[must_use]
pub fn estimate_text_tokens(text: &str) -> u64 {
    chars_to_tokens(text_chars(text))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `ceil(chars / 3.5)`: 7 characters are 2 tokens, one more starts a
    /// third; an astral character counts two UTF-16 units.
    #[test]
    fn rounds_up_at_three_and_a_half_utf16_units_per_token() {
        assert_eq!(
            [0, 1, 7, 8, 3_500, u64::MAX].map(chars_to_tokens),
            [
                0,
                1,
                2,
                3,
                1_000,
                u64::MAX.div_ceil(CHARS_PER_TOKEN_NUMERATOR)
            ]
        );
        assert_eq!(
            ["", "abcdefg", "abcdefgh", "\u{1F600}"]
                .map(|text| (text_chars(text), estimate_text_tokens(text))),
            [(0, 0), (7, 2), (8, 3), (2, 1)]
        );
    }
}
