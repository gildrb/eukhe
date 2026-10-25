//! What a session commit writes and publishes for one staged document
//! (`bend/doc_plan.bend`, entry `bend/ffi_doc_plan.bend`;
//! `laws/doc_plan.bend`). [`content`] and [`publishes`] encode their
//! question, call [`Entry::DocPlan`] and decode the answer.

use crate::wire::{Reader, Writer};
use crate::{call, Entry, Error};

/// A loaded incarnation at commit (`FDp.QContent`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Loaded {
    /// The definition version storage holds.
    pub stored: u64,
    /// The definition's version.
    pub version: u64,
    /// Whether the commit stages operations on it.
    pub staged: bool,
}

/// What a loaded incarnation writes (`Dp.Content`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Content {
    /// Nothing.
    Kept,
    /// A base of the whole value at the definition's version.
    Base,
    /// A delta of the staged operations.
    Delta,
}

/// The change a plan carries (`Dp.Change`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Change {
    /// None: a fork copy, a retirement.
    None,
    /// A created document's.
    Created,
    /// A loaded incarnation's.
    Loaded,
}

/// A plan as adoption sees it (`FDp.QPublishes`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Plan {
    /// Whether the plan retires its document.
    pub retire: bool,
    pub change: Change,
    /// Whether the plan writes content.
    pub writes: bool,
}

/// What `loaded` writes (`Dp.content`): a base when storage holds an older
/// version than the definition's, even without operations; else a delta
/// when operations are staged, else nothing.
///
/// # Errors
///
/// [`Error::Wire`] when a version is past [`crate::wire::NAT_MAX`]; else
/// only from an inconsistent build (see [`crate::expect_core`]).
pub fn content(loaded: Loaded) -> Result<Content, Error> {
    let mut request = Writer::new();
    request
        .tag(0)
        .nat(loaded.stored)
        .nat(loaded.version)
        .bool(loaded.staged);
    let reply = call(Entry::DocPlan, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let content = match reply.tag_of(3, "a content")? {
        0 => Content::Kept,
        1 => Content::Base,
        _ => Content::Delta,
    };
    reply.end()?;
    Ok(content)
}

/// Whether adoption publishes `plan` (`Dp.publishes`): one that retires its
/// document or has no loaded incarnation's change, and a loaded
/// incarnation's only when it writes content.
///
/// # Errors
///
/// Only from an inconsistent build (see [`crate::expect_core`]).
pub fn publishes(plan: Plan) -> Result<bool, Error> {
    let change = match plan.change {
        Change::None => 0,
        Change::Created => 1,
        Change::Loaded => 2,
    };
    let mut request = Writer::new();
    request
        .tag(1)
        .bool(plan.retire)
        .tag(change)
        .bool(plan.writes);
    let reply = call(Entry::DocPlan, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let publishes = reply.bool()?;
    reply.end()?;
    Ok(publishes)
}

#[cfg(test)]
mod tests {
    use super::{content, publishes, Change, Content, Loaded, Plan};

    #[test]
    fn the_codec_carries_each_question_through_the_core() {
        let migrated = Loaded {
            stored: 1,
            version: 2,
            staged: false,
        };
        assert_eq!(content(migrated).unwrap(), Content::Base);
        let quiet = Plan {
            retire: false,
            change: Change::Loaded,
            writes: false,
        };
        assert!(!publishes(quiet).unwrap());
    }
}
