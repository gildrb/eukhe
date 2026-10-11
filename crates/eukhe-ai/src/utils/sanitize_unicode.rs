//! Removal of unpaired UTF-16 surrogates.
//!
//! Unpaired surrogates (a high surrogate 0xD800-0xDBFF without a following
//! low surrogate 0xDC00-0xDFFF, or vice versa) cause JSON serialization
//! errors at many providers. A Rust `str` is valid UTF-8 and cannot hold
//! one, so [`sanitize_surrogates`] returns its input unchanged; text decoded
//! from UTF-16 goes through [`sanitize_surrogates_utf16`], which drops them
//! exactly like the TS regex. Properly paired surrogates (emoji and other
//! characters outside the Basic Multilingual Plane) are preserved.

use std::borrow::Cow;

/// TS `sanitizeSurrogates(text)` for a Rust string: valid UTF-8 has no
/// unpaired surrogates, so the text is returned as is.
#[must_use]
pub fn sanitize_surrogates(text: &str) -> Cow<'_, str> {
    Cow::Borrowed(text)
}

/// TS `sanitizeSurrogates(text)` over UTF-16 code units: remove unpaired
/// surrogates and decode the rest.
#[must_use]
pub fn sanitize_surrogates_utf16(units: &[u16]) -> String {
    char::decode_utf16(units.iter().copied())
        .filter_map(Result::ok)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn preserves_paired_and_drops_unpaired_surrogates() {
        let emoji: Vec<u16> = "Hello 🙈 World".encode_utf16().collect();
        assert_eq!(sanitize_surrogates_utf16(&emoji), "Hello 🙈 World");
        let mut unpaired: Vec<u16> = "Text ".encode_utf16().collect();
        unpaired.push(0xD83D);
        unpaired.extend(" here".encode_utf16());
        assert_eq!(sanitize_surrogates_utf16(&unpaired), "Text  here");
        let low_first: Vec<u16> = vec![0xDC00, 0x61, 0xD800];
        assert_eq!(sanitize_surrogates_utf16(&low_first), "a");
        assert_eq!(sanitize_surrogates("Hello 🙈 World"), "Hello 🙈 World");
    }
}
