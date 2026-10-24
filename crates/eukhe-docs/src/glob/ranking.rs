//! The ranking and the pages of one `glob`, decided by the compiled Bend
//! core (`bend/ffi_doc_glob.bend`, model `bend/doc_glob.bend`, laws
//! `laws/doc_glob.bend`): the core gets each matched path's time, asks for
//! the path itself only while it can still be on the page, keeps the best
//! `skip + page + 1` paths, and answers the page. Rust reads times, spells
//! paths and moves them; it keeps no path.

use std::num::NonZeroUsize;

use eukhe_bend::wire::{Reader, WireError, Writer, NAT_MAX};
use eukhe_bend::{expect_core, Entry, Error, Stepper};

use super::{GlobError, GlobMatch};

/// A glob's ranking in the core.
pub(super) struct Ranking {
    core: Stepper,
}

/// What the core answers for a page.
pub(super) struct Page {
    /// The page's paths, newest first, then by path.
    pub(super) matches: Vec<GlobMatch>,
    /// The `skip` of the next page, when paths follow this one.
    pub(super) next_skip: Option<u64>,
    /// The number of ranked paths, when the skip is at or past their end.
    pub(super) past_end: Option<u64>,
}

impl Ranking {
    /// A ranking for the page of `skip` and `limit` (none: the default
    /// page); numbers past the wire's range are cut to it.
    pub(super) fn open(skip: u64, limit: Option<NonZeroUsize>) -> Ranking {
        let opened = (|| -> Result<Stepper, Error> {
            let mut request = Writer::new();
            request.nat(skip.min(NAT_MAX));
            match limit {
                None => request.none(),
                Some(limit) => request
                    .some()
                    .nat(u64::try_from(limit.get()).map_or(NAT_MAX, |limit| limit.min(NAT_MAX))),
            };
            let (core, reply) = Stepper::open(Entry::DocGlob, &request.finish()?)?;
            Reader::reply(&reply)?.end()?;
            Ok(core)
        })();
        Ranking {
            core: expect_core(Entry::DocGlob, opened),
        }
    }

    /// Feeds the next matched path, changed at `modified_ms`; `spell`
    /// makes its display path only when the core can still keep it.
    ///
    /// # Errors
    ///
    /// The error of `spell`.
    pub(super) fn meet(
        &mut self,
        modified_ms: u64,
        spell: impl FnOnce() -> Result<String, GlobError>,
    ) -> Result<(), GlobError> {
        let modified_ms = modified_ms.min(NAT_MAX);
        let wanted = (|| -> Result<bool, Error> {
            let reply = self
                .core
                .step(&Writer::new().tag(0).nat(modified_ms).finish()?)?;
            let mut reader = Reader::reply(&reply)?;
            let wanted = reader.bool()?;
            reader.end()?;
            Ok(wanted)
        })();
        if !expect_core(Entry::DocGlob, wanted) {
            return Ok(());
        }
        let path = spell()?;
        let added = (|| -> Result<(), Error> {
            let reply = self
                .core
                .step(&Writer::new().tag(1).nat(modified_ms).str(&path).finish()?)?;
            Reader::reply(&reply)?.end()?;
            Ok(())
        })();
        expect_core(Entry::DocGlob, added);
        Ok(())
    }

    /// The page of the paths met so far. A directory's path ends in `/`.
    pub(super) fn page(mut self) -> Page {
        let page = (|| -> Result<Page, Error> {
            let reply = self.core.step(&Writer::new().tag(2).finish()?)?;
            let mut reader = Reader::reply(&reply)?;
            let next_skip = maybe_nat(&mut reader)?;
            let past_end = maybe_nat(&mut reader)?;
            let count = reader.count()?;
            let matches = (0..count)
                .map(|_| {
                    let modified_ms = reader.nat()?;
                    let path = reader.str()?;
                    Ok(GlobMatch {
                        path: path.to_owned(),
                        modified_ms,
                        is_dir: path.ends_with('/'),
                    })
                })
                .collect::<Result<Vec<_>, WireError>>()?;
            reader.end()?;
            Ok(Page {
                matches,
                next_skip,
                past_end,
            })
        })();
        expect_core(Entry::DocGlob, page)
    }
}

fn maybe_nat(reader: &mut Reader<'_>) -> Result<Option<u64>, WireError> {
    if reader.maybe()? {
        Ok(Some(reader.nat()?))
    } else {
        Ok(None)
    }
}
