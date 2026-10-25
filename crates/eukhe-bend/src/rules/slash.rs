//! The command a mistyped slash command most likely meant
//! (`bend/slash_suggest.bend`, entry `bend/ffi_slash_suggest.bend`;
//! `laws/slash_suggest.bend`): the first candidate of the fewest
//! Levenshtein edits in chars, when that many edits are within the limit
//! of the typed name's UTF-8 length (1 up to 3 bytes, else a third of it,
//! at least 2). Rust sends the typed name and the candidates and maps the
//! answered index back to its candidate.

use crate::wire::{Reader, WireError, Writer};
use crate::{call, expect_core, Entry, Error};

/// The candidate to suggest for the typed name `typed`, if any.
#[must_use]
pub fn suggestion<'a>(typed: &str, candidates: &[&'a str]) -> Option<&'a str> {
    expect_core(Entry::SlashSuggest, suggestion_call(typed, candidates))
}

fn suggestion_call<'a>(typed: &str, candidates: &[&'a str]) -> Result<Option<&'a str>, Error> {
    let mut request = Writer::new();
    request.str(typed).count(candidates.len());
    for candidate in candidates {
        request.str(candidate);
    }
    let reply = call(Entry::SlashSuggest, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let suggested = if reader.maybe()? {
        let index = reader.count()?;
        Some(*candidates.get(index).ok_or(WireError::Malformed {
            at: 0,
            expected: "the index of a candidate",
        })?)
    } else {
        None
    };
    reader.end()?;
    Ok(suggested)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The suggestion comes from the compiled core: a swapped pair finds
    /// its command, a far name finds none.
    #[test]
    fn the_core_suggests_the_nearest_command() {
        let candidates = ["new", "model", "compact"];
        assert_eq!(
            [
                suggestion("modle", &candidates),
                suggestion("zzzzzz", &candidates)
            ],
            [Some("model"), None]
        );
    }
}
