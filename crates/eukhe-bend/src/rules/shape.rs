//! Line shapes (`bend/shape.bend`, entry `bend/ffi_shape.bend`;
//! `laws/shape/`): the explicit rules eukhe states instead of decision
//! regexes. A shape is data of a table module (`bend/incident_shapes.bend`:
//! ids 0-99) and is named here by its global id; the core answers the
//! first shape of a list that fits a text, or every fit of one shape, with
//! char spans and the text each capture took. [`INCIDENT_RULES`] hands the
//! incident shapes to eukhe-types' classifier.

use crate::wire::{Reader, Writer, STR_MAX};
use crate::{call, expect_core, Entry, Error, WireError};
use eukhe_types::incident::{IncidentRules, IncidentShape, ShapeFit};

/// A fit of a shape: the chars from `start` to `end` (char offsets into
/// the text), and the text each capture took in the order its captures
/// open (`None`: the capture took no part in the fit).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fit {
    pub start: usize,
    pub end: usize,
    pub captures: Vec<Option<String>>,
}

/// The first shape of `ids` (global shape ids) that fits `text`: its index
/// in `ids` and its fit. A text past [`STR_MAX`] chars is read up to there.
///
/// # Panics
///
/// On an unknown shape id or a compiled-core failure (an inconsistent
/// build: [`expect_core`]).
#[must_use]
pub fn first(ids: &[u32], text: &str) -> Option<(usize, Fit)> {
    expect_core(Entry::Shape, first_call(ids, text))
}

/// Every fit of the shape `id` in `text`, left to right: each search
/// starts where the previous fit ended (one char later after an empty
/// fit). A text past [`STR_MAX`] chars is read up to there.
///
/// # Panics
///
/// On an unknown shape id or a compiled-core failure ([`expect_core`]).
#[must_use]
pub fn all(id: u32, text: &str) -> Vec<Fit> {
    expect_core(Entry::Shape, all_call(id, text))
}

/// The incident shapes, asked of the compiled core.
pub const INCIDENT_RULES: IncidentRules = IncidentRules {
    first: incident_first,
};

fn incident_first(text: &str, shapes: &[IncidentShape]) -> Option<ShapeFit> {
    let ids: Vec<u32> = shapes.iter().map(|shape| shape.id()).collect();
    let (index, fit) = first(&ids, text)?;
    Some(ShapeFit {
        index,
        captures: fit.captures,
    })
}

fn first_call(ids: &[u32], text: &str) -> Result<Option<(usize, Fit)>, Error> {
    let mut request = Writer::new();
    request.tag(0).count(ids.len());
    for id in ids {
        request.u32(*id);
    }
    request.str(wire_text(text));
    let reply = call(Entry::Shape, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let found = if reader.maybe()? {
        let index = reader.count()?;
        Some((index, read_fit(&mut reader)?))
    } else {
        None
    };
    reader.end()?;
    Ok(found)
}

fn all_call(id: u32, text: &str) -> Result<Vec<Fit>, Error> {
    let mut request = Writer::new();
    request.tag(1).u32(id).str(wire_text(text));
    let reply = call(Entry::Shape, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let n = reader.count()?;
    let fits = (0..n)
        .map(|_| read_fit(&mut reader))
        .collect::<Result<Vec<_>, _>>()?;
    reader.end()?;
    Ok(fits)
}

fn read_fit(reader: &mut Reader<'_>) -> Result<Fit, WireError> {
    let start = reader.count()?;
    let end = reader.count()?;
    let n = reader.count()?;
    let captures = (0..n)
        .map(|_| {
            Ok(if reader.maybe()? {
                Some(reader.str()?.to_owned())
            } else {
                None
            })
        })
        .collect::<Result<Vec<_>, WireError>>()?;
    Ok(Fit {
        start,
        end,
        captures,
    })
}

/// A text as the wire carries it: its first [`STR_MAX`] chars.
fn wire_text(text: &str) -> &str {
    text.char_indices()
        .nth(STR_MAX)
        .map_or(text, |(end, _)| &text[..end])
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The answers come from the compiled core: the first fitting shape of
    /// a list with its captures, every fit of one shape, an untaken capture.
    #[test]
    fn the_core_reads_the_shapes() {
        let auth = IncidentShape::AuthFailed.id();
        let unknown = IncidentShape::UnknownSession.id();
        let line = "Error: Unknown active session: ab";
        let found = first(&[auth, unknown], line);
        assert_eq!(
            found,
            Some((
                1,
                Fit {
                    start: 7,
                    end: 33,
                    captures: vec![Some("ab".to_string())]
                }
            ))
        );
        let text = "AUTHENTICATION FAILED x authentication failed";
        assert_eq!(
            all(auth, text),
            vec![
                Fit {
                    start: 0,
                    end: 21,
                    captures: vec![]
                },
                Fit {
                    start: 24,
                    end: 45,
                    captures: vec![]
                }
            ]
        );
        let catch_up = IncidentShape::CatchUp.id();
        assert_eq!(
            first(&[catch_up], "Failed to catch up client c1: Error: x")
                .map(|(_, fit)| fit.captures),
            Some(vec![None, Some("Error: x".to_string())])
        );
    }
}

#[cfg(test)]
#[path = "shape_incident_tests.rs"]
mod incident_tests;
