//! Revision triples (`major.minor.patch`) extracted from model ids. Port of
//! omp `packages/catalog/src/compat/revision.ts`: three unsigned 8-bit
//! components, omitted ones zero (`4.6` ≡ `4.6.0`). omp renders extracted
//! revisions as `"4.6.0"` strings and reparses them for every comparison;
//! this port keeps the parsed triple, which compares identically.

use std::cmp::Ordering;

/// A parsed `major.minor.patch` revision; the derived order is omp's
/// lexicographic `compareRevision`.
pub(crate) type Revision = [u8; 3];

/// One decimal component: non-empty ASCII digits, at most 255.
fn parse_component(value: &str) -> Option<u8> {
    if value.is_empty() {
        return None;
    }
    let mut out: u16 = 0;
    for byte in value.bytes() {
        if !byte.is_ascii_digit() {
            return None;
        }
        out = out * 10 + u16::from(byte - b'0');
        if out > 255 {
            return None;
        }
    }
    u8::try_from(out).ok()
}

/// An explicit revision literal: one to three components separated by `.`
/// or `-` (`"4.6"`, `"4-6-1"`); `None` when malformed.
pub(crate) fn parse_revision(value: &str) -> Option<Revision> {
    let mut out = [0; 3];
    // `split` yields at least one part, so a parsed revision always has one.
    for (index, part) in value.split(['.', '-']).enumerate() {
        *out.get_mut(index)? = parse_component(part)?;
    }
    Some(out)
}

/// A leading revision of an id tail that begins with a digit: up to three
/// components separated by `.`, or by `-` followed by a digit
/// (`"4-6-turbo"` → `[4, 6, 0]`). A component whose digits run straight into
/// a letter is a size token (`qwen3-32b`, `llama-3.3-70b`), never a revision
/// component.
pub(crate) fn parse_revision_prefix(value: &str) -> Option<Revision> {
    let bytes = value.as_bytes();
    let mut out = [0; 3];
    let mut count = 0;
    let mut index = 0;
    while count < 3 {
        let start = index;
        while index < bytes.len() && bytes[index].is_ascii_digit() {
            index += 1;
        }
        let trailing = bytes.get(index).copied().unwrap_or(0);
        let component = if trailing.is_ascii_alphabetic() {
            None
        } else {
            parse_component(&value[start..index])
        };
        let Some(component) = component else {
            return (count > 0).then_some(out);
        };
        out[count] = component;
        count += 1;
        let Some(&separator) = bytes.get(index) else {
            break;
        };
        let next_is_digit = bytes.get(index + 1).is_some_and(u8::is_ascii_digit);
        if (separator != b'.' && separator != b'-') || !next_is_digit {
            break;
        }
        index += 1;
    }
    Some(out)
}

/// Whether `revision` is present and at or above the literal `floor`; an
/// absent (or, in omp, unparsable) revision never is.
pub(crate) fn revision_at_least(revision: Option<Revision>, floor: &str) -> bool {
    match (revision, parse_revision(floor)) {
        (Some(revision), Some(floor)) => revision >= floor,
        _ => false,
    }
}

/// One comparison of a cascade rule's `revision ">=2.5 <4"` conjunction.
#[derive(Clone, Copy, Debug)]
pub(crate) enum RevisionTerm {
    AtLeast(Revision),
    Below(Revision),
    AtMost(Revision),
    Equal(Revision),
}

/// Whether `revision` satisfies every term of the conjunction.
pub(crate) fn revision_satisfies(revision: Revision, terms: &[RevisionTerm]) -> bool {
    terms.iter().all(|term| match *term {
        RevisionTerm::AtLeast(floor) => revision.cmp(&floor) != Ordering::Less,
        RevisionTerm::Below(ceiling) => revision.cmp(&ceiling) == Ordering::Less,
        RevisionTerm::AtMost(ceiling) => revision.cmp(&ceiling) != Ordering::Greater,
        RevisionTerm::Equal(exact) => revision == exact,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_explicit_revisions() {
        assert_eq!(parse_revision("4.6"), Some([4, 6, 0]));
        assert_eq!(parse_revision("4-6-1"), Some([4, 6, 1]));
        assert_eq!(parse_revision("255"), Some([255, 0, 0]));
        assert_eq!(parse_revision("256"), None);
        assert_eq!(parse_revision("1.2.3.4"), None);
        assert_eq!(parse_revision("4."), None);
        assert_eq!(parse_revision(""), None);
        assert_eq!(parse_revision("v4"), None);
    }

    #[test]
    fn extracts_leading_revisions_and_skips_size_tokens() {
        assert_eq!(parse_revision_prefix("4-6-turbo"), Some([4, 6, 0]));
        assert_eq!(parse_revision_prefix("4.7"), Some([4, 7, 0]));
        assert_eq!(parse_revision_prefix("45"), Some([45, 0, 0]));
        assert_eq!(parse_revision_prefix("3-32b"), Some([3, 0, 0]));
        assert_eq!(parse_revision_prefix("3.3-70b"), Some([3, 3, 0]));
        assert_eq!(parse_revision_prefix("32b"), None);
        assert_eq!(parse_revision_prefix("5-20250929"), Some([5, 0, 0]));
        assert_eq!(parse_revision_prefix("4-5-20251001-v1:0"), Some([4, 5, 0]));
        assert_eq!(parse_revision_prefix("1.2.3.4"), Some([1, 2, 3]));
        assert_eq!(parse_revision_prefix("4-"), Some([4, 0, 0]));
        assert_eq!(parse_revision_prefix("x"), None);
    }

    #[test]
    fn compares_against_floors() {
        assert!(revision_at_least(Some([5, 0, 0]), "5"));
        assert!(revision_at_least(Some([4, 7, 0]), "4.7"));
        assert!(!revision_at_least(Some([4, 6, 9]), "4.7"));
        assert!(!revision_at_least(None, "0"));
        assert!(!revision_at_least(Some([9, 9, 9]), "x"));
    }

    #[test]
    fn checks_constraint_conjunctions() {
        let range = [
            RevisionTerm::AtLeast([4, 6, 0]),
            RevisionTerm::AtMost([4, 20, 0]),
        ];
        assert!(revision_satisfies([4, 6, 0], &range));
        assert!(revision_satisfies([4, 20, 0], &range));
        assert!(!revision_satisfies([4, 5, 9], &range));
        assert!(!revision_satisfies([4, 21, 0], &range));
        assert!(revision_satisfies(
            [5, 5, 0],
            &[RevisionTerm::Equal([5, 5, 0])]
        ));
        assert!(!revision_satisfies(
            [5, 4, 0],
            &[RevisionTerm::Below([5, 4, 0])]
        ));
    }
}
