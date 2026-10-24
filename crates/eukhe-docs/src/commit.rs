//! The writer's choices (`bend/doc_commit.bend`, section "The writer's
//! choices"), run as the compiled Bend core (`bend/ffi_doc_commit.bend`):
//! whether an edit goes on after its check, what one publish did, the
//! reply of an edit, whether the write tool may replace a file, the seen
//! versions, the temporary files' prefix and which of them a sweep
//! removes. Rust locks, reads, compares bytes, hashes (the digests are
//! Rust's), publishes and removes; it asks here at each step.

use eukhe_bend::wire::{Reader, WireError, Writer};
use eukhe_bend::{call, expect_core, Entry, Error};

/// What the check of one file of an edit met (`Met`).
#[derive(Debug, Clone, Copy)]
pub(crate) struct Met {
    /// Its bytes changed since the edit staged it.
    pub(crate) changed: bool,
    /// It is a move whose destination exists.
    pub(crate) taken: bool,
}

/// Why an edit writes nothing (`Why`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Why {
    Changed,
    Taken,
}

/// Where a publish put the new bytes (`Placed`).
#[derive(Debug, Clone, Copy)]
pub(crate) enum Placed {
    /// The write or the rename failed.
    No,
    /// The target holds them; `synced`: the directory sync succeeded.
    Yes { synced: bool },
}

/// What one publish met (`Pub`).
#[derive(Debug, Clone, Copy)]
pub(crate) enum Pub {
    Updated(Placed),
    Deleted { removed: bool },
    Moved { placed: Placed, removed: bool },
}

/// The warning a landed publish carries (`Warn`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Warn {
    None,
    Sync,
    Remove,
}

/// What one publish did (`Outcome`): landed (go on) or failed (stop).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Outcome {
    Lands(Warn),
    Fails,
}

/// What became of one staged file (`Fate`).
#[derive(Debug, Clone, Copy)]
pub(crate) enum Fate {
    Noop,
    Wrote(Outcome),
    Untried,
}

/// What the reply says of one file (`Note`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Note {
    Untouched,
    Written,
    Unwritten,
    /// Not tried: the file at this index failed first.
    Skipped(usize),
}

/// The reply of an edit (`Verdict`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Verdict {
    /// Nothing landed: the first failure is the error.
    Failure,
    /// One note a staged file; `partial`: some file was not written.
    Summary { notes: Vec<Note>, partial: bool },
}

/// What a write of the write tool is based on (`Base`).
pub(crate) enum Base<'a> {
    /// The digests of the versions the session saw.
    OnSeen(&'a [String]),
    /// Exactly the bytes the caller holds.
    OnBytes,
}

/// What the target held when the write locked it (`Disk`).
pub(crate) enum Disk<'a> {
    Absent,
    /// Its digest; `expected`: it holds the caller's bytes.
    Present {
        digest: &'a str,
        expected: bool,
    },
}

/// Whether the write tool may replace its target (`Gate`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Gate {
    Proceed,
    Unseen,
    Stale,
}

fn malformed(expected: &'static str) -> WireError {
    WireError::Malformed { at: 0, expected }
}

/// A reply of the compiled core that its laws rule out (Rust met a fact
/// that contradicts it): only an inconsistent build answers it.
pub(crate) fn inconsistent<T>(expected: &'static str) -> T {
    expect_core(
        Entry::DocCommit,
        Err::<T, Error>(Error::Wire(malformed(expected))),
    )
}

/// The compiled core's answer to the request in `writer`, read by `read`.
fn ask<T>(writer: &mut Writer, read: impl FnOnce(&mut Reader<'_>) -> Result<T, WireError>) -> T {
    let answer = || -> Result<T, Error> {
        let reply = call(Entry::DocCommit, &writer.finish()?)?;
        let mut reader = Reader::reply(&reply)?;
        let value = read(&mut reader)?;
        reader.end()?;
        Ok(value)
    };
    expect_core(Entry::DocCommit, answer())
}

fn index(reader: &mut Reader<'_>, below: usize) -> Result<usize, WireError> {
    usize::try_from(reader.nat()?)
        .ok()
        .filter(|&at| at < below)
        .ok_or_else(|| malformed("a file of the edit"))
}

/// The check of an edit's files: `None` publishes every file; else the
/// index of the file that stops it, and why.
pub(crate) fn check(mets: &[Met]) -> Option<(usize, Why)> {
    let mut writer = Writer::new();
    writer.tag(0).count(mets.len());
    for met in mets {
        writer.bool(met.changed).bool(met.taken);
    }
    ask(&mut writer, |reader| {
        if reader.tag_of(2, "a check")? == 0 {
            return Ok(None);
        }
        let at = index(reader, mets.len())?;
        let why = match reader.tag_of(2, "a reason")? {
            0 => Why::Changed,
            1.. => Why::Taken,
        };
        Ok(Some((at, why)))
    })
}

fn spell_placed(writer: &mut Writer, placed: Placed) {
    match placed {
        Placed::No => writer.tag(0),
        Placed::Yes { synced } => writer.tag(1).bool(synced),
    };
}

/// What one publish did.
pub(crate) fn outcome(facts: Pub) -> Outcome {
    let mut writer = Writer::new();
    writer.tag(1);
    match facts {
        Pub::Updated(placed) => {
            writer.tag(0);
            spell_placed(&mut writer, placed);
        }
        Pub::Deleted { removed } => {
            writer.tag(1).bool(removed);
        }
        Pub::Moved { placed, removed } => {
            writer.tag(2);
            spell_placed(&mut writer, placed);
            writer.bool(removed);
        }
    }
    ask(&mut writer, |reader| {
        Ok(match reader.tag_of(2, "an outcome")? {
            0 => Outcome::Lands(match reader.tag_of(3, "a warning")? {
                0 => Warn::None,
                1 => Warn::Sync,
                2.. => Warn::Remove,
            }),
            1.. => Outcome::Fails,
        })
    })
}

/// The reply of an edit whose staged files became `fates`.
pub(crate) fn answer(fates: &[Fate]) -> Verdict {
    let mut writer = Writer::new();
    writer.tag(2).count(fates.len());
    for fate in fates {
        match fate {
            Fate::Noop => writer.tag(0),
            Fate::Wrote(Outcome::Lands(warn)) => writer.tag(1).tag(0).tag(match warn {
                Warn::None => 0,
                Warn::Sync => 1,
                Warn::Remove => 2,
            }),
            Fate::Wrote(Outcome::Fails) => writer.tag(1).tag(1),
            Fate::Untried => writer.tag(2),
        };
    }
    ask(&mut writer, |reader| {
        if reader.tag_of(2, "a verdict")? == 0 {
            return Ok(Verdict::Failure);
        }
        if reader.count()? != fates.len() {
            return Err(malformed("one note a staged file"));
        }
        let notes = fates
            .iter()
            .map(|_| {
                Ok(match reader.tag_of(4, "a note")? {
                    0 => Note::Untouched,
                    1 => Note::Written,
                    2 => Note::Unwritten,
                    3.. => Note::Skipped(index(reader, fates.len())?),
                })
            })
            .collect::<Result<Vec<Note>, WireError>>()?;
        let partial = reader.bool()?;
        Ok(Verdict::Summary { notes, partial })
    })
}

/// Whether the write tool may replace its target.
pub(crate) fn gate(base: &Base<'_>, disk: &Disk<'_>) -> Gate {
    let mut writer = Writer::new();
    writer.tag(3);
    match base {
        Base::OnSeen(seen) => {
            writer.tag(0).count(seen.len());
            for digest in *seen {
                writer.str(digest);
            }
        }
        Base::OnBytes => {
            writer.tag(1);
        }
    }
    match disk {
        Disk::Absent => writer.tag(0),
        Disk::Present { digest, expected } => writer.tag(1).str(digest).bool(*expected),
    };
    ask(&mut writer, |reader| {
        Ok(match reader.tag_of(3, "a write gate")? {
            0 => Gate::Proceed,
            1 => Gate::Unseen,
            2.. => Gate::Stale,
        })
    })
}

fn read_strs(reader: &mut Reader<'_>) -> Result<Vec<String>, WireError> {
    (0..reader.count()?)
        .map(|_| reader.str().map(str::to_owned))
        .collect()
}

/// The seen versions (digests, newest first) after the session sees
/// `digest`.
pub(crate) fn seen(digest: &str, seen: &[String]) -> Vec<String> {
    let mut writer = Writer::new();
    writer.tag(4).str(digest).count(seen.len());
    for earlier in seen {
        writer.str(earlier);
    }
    ask(&mut writer, read_strs)
}

/// The name prefix of the temporary files of a target whose file name has
/// the digest `name_digest`.
pub(crate) fn prefix(name_digest: &str) -> String {
    let mut writer = Writer::new();
    writer.tag(5).str(name_digest);
    ask(&mut writer, |reader| reader.str().map(str::to_owned))
}

/// The entries (by index) a sweep of the target whose file name has the
/// digest `name_digest` removes; each entry is its name (lossy UTF-8) and
/// whether a live writer holds it.
pub(crate) fn gone(name_digest: &str, entries: &[(String, bool)]) -> Vec<usize> {
    let mut writer = Writer::new();
    writer.tag(6).str(name_digest).count(entries.len());
    for (name, held) in entries {
        writer.str(name).bool(*held);
    }
    ask(&mut writer, |reader| {
        (0..reader.count()?)
            .map(|_| index(reader, entries.len()))
            .collect()
    })
}
