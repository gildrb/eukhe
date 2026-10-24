//! Grep's decisions, made by the compiled Bend core (`bend/ffi_doc_search.bend`
//! over the rules of `bend/doc_search.bend`, laws `laws/doc_search.bend`): the
//! scope of a search, what becomes of each file of the walk (searched or not,
//! the matches it fetches and keeps, cut, shown or paged out, searched in
//! part), the page of matching files and the match limit. Rust walks, reads
//! and counts matches; every rule runs in the core. Every request and reply is
//! one list of Nats; a number past the wire's largest is sent as that largest
//! (no count of files, matches or lines reaches it).

use eukhe_bend::wire::{Reader, WireError, Writer, NAT_MAX};
use eukhe_bend::{expect_core, Entry, Stepper};

use crate::read::selector::LineRange;

fn nat(n: u64) -> u64 {
    n.min(NAT_MAX)
}

fn nat_of(n: usize) -> u64 {
    u64::try_from(n).map_or(NAT_MAX, nat)
}

/// A count the core answers, as a `usize`.
fn size(n: u64) -> usize {
    usize::try_from(n).unwrap_or(usize::MAX)
}

fn spell(nats: &[u64]) -> Result<String, WireError> {
    let mut request = Writer::new();
    request.count(nats.len());
    for &n in nats {
        request.nat(n);
    }
    request.finish()
}

fn read_nats(reply: &str) -> Result<Vec<u64>, WireError> {
    let mut reader = Reader::reply(reply)?;
    let nats = (0..reader.count()?)
        .map(|_| reader.nat())
        .collect::<Result<Vec<_>, _>>()?;
    reader.end()?;
    Ok(nats)
}

fn malformed(expected: &'static str) -> WireError {
    WireError::Malformed { at: 0, expected }
}

/// A Bool of a reply: 0 or 1.
fn bit(n: u64) -> Result<bool, WireError> {
    match n {
        0 => Ok(false),
        1 => Ok(true),
        2.. => Err(malformed("a Bool (0 or 1)")),
    }
}

/// One call of the entry.
fn call(nats: &[u64]) -> Vec<u64> {
    let reply = (|| -> Result<Vec<u64>, eukhe_bend::Error> {
        Ok(read_nats(&eukhe_bend::call(
            Entry::DocSearch,
            &spell(nats)?,
        )?)?)
    })();
    expect_core(Entry::DocSearch, reply)
}

/// The scope of a search (model `scope`).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Scope {
    /// The scope can hold several files: it pages them.
    pub(super) multi: bool,
    /// Matches kept of one file.
    pub(super) per_file: u64,
    /// Matching files skipped before the page.
    pub(super) skip: u64,
    /// Matching files on the page.
    pub(super) window: u64,
}

/// The scope of a path of `roots` roots, `dirs` of them directories, with
/// the skip and the match limit the request asks.
pub(super) fn scope(roots: usize, dirs: usize, skip: u64, limit: Option<usize>) -> Scope {
    let limit = limit.map_or(0, |limit| nat_of(limit).saturating_add(1).min(NAT_MAX));
    let reply = call(&[2, nat_of(roots), nat_of(dirs), nat(skip), limit]);
    let read = (|| -> Result<Scope, WireError> {
        let [multi, per_file, skip, window] = reply[..] else {
            return Err(malformed("a scope: multi, p, s, k"));
        };
        Ok(Scope {
            multi: bit(multi)?,
            per_file,
            skip,
            window,
        })
    })();
    expect_core(Entry::DocSearch, read)
}

/// The page of `total` matching files (model `grep.next`, `grep.past`,
/// `page`).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Page {
    /// The skip of the next page, when a matching file follows this one.
    pub(super) next: Option<u64>,
    /// The skip is past the end of the matching files.
    pub(super) past: bool,
    /// The place of each file of the page among the matching files.
    pub(super) files: Vec<usize>,
}

pub(super) fn page(scope: Scope, total: usize) -> Page {
    let reply = call(&[
        0,
        nat_of(total),
        scope.skip,
        scope.window,
        u64::from(scope.multi),
    ]);
    let read = (|| -> Result<Page, WireError> {
        let [next, past, ref files @ ..] = reply[..] else {
            return Err(malformed("a page: next, past, files"));
        };
        Ok(Page {
            next: next.checked_sub(1),
            past: bit(past)?,
            files: files.iter().map(|&at| size(at)).collect(),
        })
    })();
    expect_core(Entry::DocSearch, read)
}

/// The match limit over the page's files of `matches` matches each (model
/// `rr`, `rr.cut`): whether it cut matches, and what each file keeps.
pub(super) fn limit(limit: usize, matches: &[usize]) -> (bool, Vec<usize>) {
    let mut request = vec![1, nat_of(limit)];
    request.extend(matches.iter().map(|&n| nat_of(n)));
    let reply = call(&request);
    let read = (|| -> Result<(bool, Vec<usize>), WireError> {
        let [cut, ref kept @ ..] = reply[..] else {
            return Err(malformed("a limit: cut, kept"));
        };
        if kept.len() != matches.len() {
            return Err(malformed("one kept count per file"));
        }
        Ok((bit(cut)?, kept.iter().map(|&n| size(n)).collect()))
    })();
    expect_core(Entry::DocSearch, read)
}

/// The next file of a walk: not searched (with the files left, none of them
/// searched) or searched for at most `fetch` matches.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Ask {
    Stop { left: u64 },
    Fetch(u64),
}

/// A file the walk asked for and did not search.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Skip {
    /// A NUL byte is in it.
    Binary,
    /// It does not open.
    Unreadable,
}

/// A file left out of the matches (model `Class`: not searched, or skipped
/// with its reason).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Left {
    NotSearched,
    Binary,
    Unreadable,
}

/// The class of a file met (model `Class`).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Class {
    NoMatch,
    /// A matching file on the page.
    Shown,
    /// A matching file off the page.
    PagedOut,
    Left(Left),
}

/// The decision on a file searched.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Said {
    pub(super) class: Class,
    /// It held more matches than it keeps.
    pub(super) cut: bool,
    /// Only a part of it was searched.
    pub(super) partial: bool,
    /// The matches it keeps.
    pub(super) kept: usize,
}

/// A reply to what a file held: its class, cut, partial, kept.
fn read_said(reply: &[u64]) -> Result<Said, WireError> {
    let [class, cut, partial, kept] = reply[..] else {
        return Err(malformed("a file's class, cut, partial, kept"));
    };
    Ok(Said {
        class: match class {
            0 => Class::NoMatch,
            1 => Class::Shown,
            2 => Class::PagedOut,
            3 => Class::Left(Left::NotSearched),
            4 => Class::Left(Left::Binary),
            5 => Class::Left(Left::Unreadable),
            6.. => return Err(malformed("the class of a file the walk opened")),
        },
        cut: bit(cut)?,
        partial: bit(partial)?,
        kept: size(kept),
    })
}

/// The walk of a search: the core's stepper, one file at a time.
pub(super) struct Walk {
    core: Stepper,
}

impl Walk {
    /// A walk of `files` files under `scope`, keeping `total` matches in all
    /// and searching `max_bytes` bytes of a file.
    pub(super) fn open(scope: Scope, total: u64, files: usize, max_bytes: u64) -> Walk {
        let opened = (|| -> Result<Stepper, eukhe_bend::Error> {
            let request = spell(&[
                scope.per_file,
                scope.skip,
                scope.window,
                nat(total),
                nat_of(files),
                nat(max_bytes),
            ])?;
            let (core, reply) = Stepper::open(Entry::DocSearch, &request)?;
            Reader::reply(&reply)?.end()?;
            Ok(core)
        })();
        Walk {
            core: expect_core(Entry::DocSearch, opened),
        }
    }

    fn step(&mut self, event: &[u64]) -> Vec<u64> {
        let reply = (|| -> Result<Vec<u64>, eukhe_bend::Error> {
            Ok(read_nats(&self.core.step(&spell(event)?)?)?)
        })();
        expect_core(Entry::DocSearch, reply)
    }

    /// The next file, whose roots select `ranges` (none: every line).
    pub(super) fn ask(&mut self, ranges: &[LineRange]) -> Ask {
        let mut event = vec![0];
        for range in ranges {
            event.push(nat(range.start_line));
            event.push(
                range
                    .end_line
                    .map_or(0, |end| nat(end).min(NAT_MAX - 1) + 1),
            );
        }
        let reply = self.step(&event);
        let read = match reply[..] {
            [0, left] => Ok(Ask::Stop { left }),
            [1, fetch] => Ok(Ask::Fetch(fetch)),
            _ => Err(malformed(
                "an ask: 0 and the files left, or 1 and the fetch",
            )),
        };
        expect_core(Entry::DocSearch, read)
    }

    /// The file asked for was searched: `hits` matches in the part searched;
    /// `big`: it is over the size limit, searched in part.
    pub(super) fn opened(&mut self, hits: usize, big: bool) -> Said {
        let reply = self.step(&[1, nat_of(hits), u64::from(big)]);
        expect_core(Entry::DocSearch, read_said(&reply))
    }

    /// The file asked for was not searched.
    pub(super) fn skipped(&mut self, why: Skip) -> Left {
        let reply = self.step(&match why {
            Skip::Binary => [2, 0],
            Skip::Unreadable => [2, 1],
        });
        let read = read_said(&reply).and_then(|said| match said.class {
            Class::Left(left) => Ok(left),
            Class::NoMatch | Class::Shown | Class::PagedOut => {
                Err(malformed("the class of a file not searched"))
            }
        });
        expect_core(Entry::DocSearch, read)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The scope and the walk come from the compiled core.
    #[test]
    fn the_scope_and_the_walk_come_from_the_core() {
        assert_eq!(
            scope(1, 1, 7, None),
            Scope {
                multi: true,
                per_file: 20,
                skip: 7,
                window: 20
            }
        );
        let mut walk = Walk::open(scope(1, 0, 7, Some(2)), 30, 2, 100);
        assert_eq!(walk.ask(&[]), Ask::Fetch(31));
        assert_eq!(
            walk.opened(25, false),
            Said {
                class: Class::Shown,
                cut: false,
                partial: false,
                kept: 25
            }
        );
        assert_eq!(walk.ask(&[]), Ask::Fetch(6));
    }
}
