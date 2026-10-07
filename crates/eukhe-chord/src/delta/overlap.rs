//! `overlap` of `delta/index.ts`: the longest suffix of one string that is a
//! prefix of another, in UTF-16 code units.

use crate::json::utf16_units;

/// Default head probe length of [`overlap`].
pub const DEFAULT_OVERLAP_PROBE: usize = 64;
/// Default candidate bound of [`overlap`].
pub const DEFAULT_OVERLAP_CANDIDATES: usize = 8;

/// Longest suffix of `a` (within its last `scan` code units) that is a prefix
/// of `b`, in UTF-16 code units, with the default probe (64) and candidate
/// bound (8).
///
/// Always correct: the returned `n` satisfies
/// `a.slice(a.length - n) === b.slice(0, n)`. Gives up (returns 0) on
/// repetitive input with too many candidates.
///
/// ```
/// assert_eq!(eukhe_chord::delta::overlap("abcdefgh", "defghxyz", 65_536), 5);
/// ```
#[must_use]
pub fn overlap(a: &str, b: &str, scan: usize) -> usize {
    overlap_with(
        a,
        b,
        scan,
        DEFAULT_OVERLAP_PROBE,
        DEFAULT_OVERLAP_CANDIDATES,
    )
}

/// [`overlap`] with an explicit head `probe` length and `max_candidates`.
#[must_use]
pub fn overlap_with(a: &str, b: &str, scan: usize, probe: usize, max_candidates: usize) -> usize {
    if a.is_empty() || b.is_empty() || scan == 0 {
        return 0;
    }
    let a_units = utf16_units(a);
    let tail = if a_units.len() > scan {
        &a_units[a_units.len() - scan..]
    } else {
        &a_units[..]
    };
    // An overlap never exceeds the tail and the head never exceeds the probe,
    // so only that much of `b` matters; `b.length` is exact when shorter.
    let needed = tail.len().max(probe);
    let b_units: Vec<u16> = b.encode_utf16().take(needed).collect();
    // A long head first (few candidates, catches large overlaps), then one
    // unit, which finds any overlap at the cost of more candidates.
    for head_length in [probe.min(b_units.len()), 1] {
        let head = &b_units[..head_length];
        let mut tried = 0;
        let mut from = 0;
        while let Some(k) = index_of(tail, head, from) {
            tried += 1;
            if tried > max_candidates {
                break;
            }
            let n = tail.len() - k;
            if n <= b_units.len() && tail[k..] == b_units[..n] {
                return n;
            }
            from = k + 1;
        }
        if head_length == 1 {
            break;
        }
    }
    0
}

/// `haystack.indexOf(needle, from)` over code units.
fn index_of(haystack: &[u16], needle: &[u16], from: usize) -> Option<usize> {
    if needle.is_empty() {
        return (from <= haystack.len()).then_some(from);
    }
    if needle.len() > haystack.len() {
        return None;
    }
    (from..=haystack.len() - needle.len())
        .find(|&start| haystack[start..start + needle.len()] == *needle)
}
