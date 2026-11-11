//! Unicode character data for the scanners and the Claude normalizer.
//!
//! The upstream tokenizer reads these from `xutf`, which needs a nightly
//! compiler (`portable_simd`); eukhe builds on stable, so this module offers
//! the same names over stable crates and the ported files change only their
//! `use` lines:
//!
//! - General Category: `unicode-general-category` (UCD 16.0.0).
//! - Script: `unicode-script`, pinned to its UCD 16.0.0 release.
//! - NFC, its quick check and the canonical combining class:
//!   `unicode-normalization`.
//!
//! GC and Script stay on UCD 16.0.0, the version upstream pins `xutf` to:
//! the reference regex engines (`regex-syntax` under fancy-regex and
//! tiktoken-rs) resolve `\p{..}` classes against 16.0.0, and the 4803
//! scalars 17.0.0 added would re-split text and change token ids
//! (`scan::tests::class_pin_tracks_ucd_generation` guards it).

pub(crate) use unicode_general_category::GeneralCategory;
use unicode_general_category::get_general_category;
use unicode_normalization::{IsNormalized, UnicodeNormalization, is_nfc_quick};
pub(crate) use unicode_script::Script;
use unicode_script::UnicodeScript;

/// UCD generation of the General Category and Script tables.
#[cfg(test)]
pub(crate) const UCD_VERSION: [(u64, u64, u64); 2] = [
    unicode_general_category::UNICODE_VERSION,
    unicode_script::UNICODE_VERSION,
];

/// The major class of a [`GeneralCategory`] (its first letter).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum GeneralCategoryGroup {
    /// `L`: cased, modifier and other letters.
    Letter,
    /// `M`: nonspacing, spacing and enclosing marks.
    Mark,
    /// `N`: decimal, letter and other numbers.
    Number,
    /// `P`: punctuation.
    Punctuation,
    /// `S`: math, currency, modifier and other symbols.
    Symbol,
    /// `Z`: space, line and paragraph separators.
    Separator,
    /// `C`: controls, format, surrogates, private use and unassigned.
    Other,
}

/// [`GeneralCategory::group`] in `xutf`'s spelling.
pub(crate) trait CategoryGroup {
    /// The category's major class.
    fn group(self) -> GeneralCategoryGroup;
}

impl CategoryGroup for GeneralCategory {
    fn group(self) -> GeneralCategoryGroup {
        match self {
            Self::UppercaseLetter
            | Self::LowercaseLetter
            | Self::TitlecaseLetter
            | Self::ModifierLetter
            | Self::OtherLetter => GeneralCategoryGroup::Letter,
            Self::NonspacingMark | Self::SpacingMark | Self::EnclosingMark => {
                GeneralCategoryGroup::Mark
            }
            Self::DecimalNumber | Self::LetterNumber | Self::OtherNumber => {
                GeneralCategoryGroup::Number
            }
            Self::ConnectorPunctuation
            | Self::DashPunctuation
            | Self::OpenPunctuation
            | Self::ClosePunctuation
            | Self::InitialPunctuation
            | Self::FinalPunctuation
            | Self::OtherPunctuation => GeneralCategoryGroup::Punctuation,
            Self::MathSymbol | Self::CurrencySymbol | Self::ModifierSymbol | Self::OtherSymbol => {
                GeneralCategoryGroup::Symbol
            }
            Self::SpaceSeparator | Self::LineSeparator | Self::ParagraphSeparator => {
                GeneralCategoryGroup::Separator
            }
            // `C`: Control, Format, Surrogate, PrivateUse, Unassigned — and,
            // `GeneralCategory` being `#[non_exhaustive]` upstream, whatever
            // category a later release adds, which is unknown here.
            _ => GeneralCategoryGroup::Other,
        }
    }
}

/// Character properties in `xutf`'s spelling.
pub(crate) trait Ucd {
    /// The character's General Category.
    fn general_category(self) -> GeneralCategory;
    /// The character's General Category major class.
    fn general_category_group(self) -> GeneralCategoryGroup;
    /// The character's Script.
    fn script(self) -> Script;
}

impl Ucd for char {
    #[inline]
    fn general_category(self) -> GeneralCategory {
        get_general_category(self)
    }

    #[inline]
    fn general_category_group(self) -> GeneralCategoryGroup {
        get_general_category(self).group()
    }

    #[inline]
    fn script(self) -> Script {
        UnicodeScript::script(&self)
    }
}

/// Canonical combining class of codepoint `cp` (0 for a non-scalar).
#[inline]
pub(crate) fn canonical_combining_class(cp: u32) -> u8 {
    char::from_u32(cp).map_or(0, unicode_normalization::char::canonical_combining_class)
}

/// Whether `text` is in NFC (quick check, settled by composing on `Maybe`).
pub(crate) fn is_nfc(text: &str) -> bool {
    unicode_normalization::is_nfc(text)
}

/// NFC quick check over a codepoint stream, allocation-free. Conservative:
/// `false` means "may need normalization" (non-scalars read as U+FFFD), so a
/// caller that composes on `false` gets the same text either way.
pub(crate) fn is_nfc_codepoints(cps: impl Iterator<Item = u32>) -> bool {
    is_nfc_quick(cps.map(|cp| char::from_u32(cp).unwrap_or(char::REPLACEMENT_CHARACTER)))
        == IsNormalized::Yes
}

/// NFC of borrowed text.
pub(crate) trait ToUnicodeNormalized {
    /// The NFC form, newly allocated.
    fn to_nfc(&self) -> String;
}

impl ToUnicodeNormalized for str {
    fn to_nfc(&self) -> String {
        self.nfc().collect()
    }
}

/// NFC of owned text.
pub(crate) trait IntoUnicodeNormalized {
    /// The NFC form.
    fn into_nfc(self) -> String;
}

impl IntoUnicodeNormalized for String {
    fn into_nfc(self) -> String {
        self.nfc().collect()
    }
}
