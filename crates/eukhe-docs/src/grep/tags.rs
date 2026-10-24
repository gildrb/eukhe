//! Grep's choice for the tag of each file it shows (`fates` in
//! `bend/doc_tags.bend`), run as the compiled Bend core
//! (`bend/ffi_doc_tags.bend`): a file searched whole whose bytes are UTF-8
//! is tagged with the text grep searched; any other gets no tag, and the
//! choice says why.

use eukhe_bend::wire::{Reader, WireError, Writer};
use eukhe_bend::{call, expect_core, Entry, Error};

/// How grep searched a file it shows (`Scan`).
#[derive(Debug, Clone, Copy)]
pub(super) enum Scan {
    /// In part: the file is over the size limit.
    Part,
    /// Whole; `utf8`: its bytes are UTF-8.
    Whole { utf8: bool },
}

/// What grep does with the tag of a file it shows (`Fate`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Fate {
    /// Record the searched text: the tag names it.
    Tagged,
    /// No tag: searched in part.
    OverLimit,
    /// No tag: the text is not UTF-8.
    NotUtf8,
}

/// The choice for each of `scans`, in order.
pub(super) fn fates(scans: &[Scan]) -> Vec<Fate> {
    expect_core(Entry::DocTags, ask(scans))
}

fn ask(scans: &[Scan]) -> Result<Vec<Fate>, Error> {
    let mut writer = Writer::new();
    writer.count(scans.len());
    for scan in scans {
        match scan {
            Scan::Part => writer.tag(0),
            Scan::Whole { utf8 } => writer.tag(1).bool(*utf8),
        };
    }
    let reply = call(Entry::DocTags, &writer.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    if reader.count()? != scans.len() {
        return Err(Error::Wire(WireError::Malformed {
            at: 0,
            expected: "one choice per shown file",
        }));
    }
    let fates = scans
        .iter()
        .map(|_| {
            Ok(match reader.tag_of(3, "a tag choice")? {
                0 => Fate::Tagged,
                1 => Fate::OverLimit,
                2.. => Fate::NotUtf8,
            })
        })
        .collect::<Result<Vec<Fate>, Error>>()?;
    reader.end()?;
    Ok(fates)
}
