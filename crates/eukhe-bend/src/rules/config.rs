//! The config rules (`bend/config.bend`, entry `bend/ffi_config.bend`;
//! `laws/config.bend`): what a writer of a config document writes, which
//! leaves of a settings document apply and which are named, the in-flight
//! limit of each provider, which keys of a project document apply under
//! its trust, and the merged `mcpServers` entries. The caller turns its
//! documents into these facts, calls these functions and acts on the
//! answer; keys and values cross the wire as their places.

use crate::wire::{Reader, WireError, Writer};
use crate::{call, expect_core, Entry, Error};

/// One entry of a document as the core sees it: the place of its key and
/// of its value.
pub type DocEntry = (u64, u64);

/// How the read of a document under its lock ended.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Read<K, V> {
    /// No file.
    Missing,
    /// The document's entries, in order.
    Parsed(Vec<(K, V)>),
    /// A file that cannot be read or parsed, or of a version this build
    /// does not know.
    Broken,
}

/// One edit of one key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Edit<K, V> {
    Set(K, V),
    Delete(K),
}

fn entries(request: &mut Writer, entries: &[DocEntry]) {
    request.count(entries.len());
    for &(key, value) in entries {
        request.nat(key).nat(value);
    }
}

fn read_entries(reply: &mut Reader<'_>) -> Result<Vec<DocEntry>, WireError> {
    let count = reply.count()?;
    let mut entries = Vec::with_capacity(count);
    for _ in 0..count {
        entries.push((reply.nat()?, reply.nat()?));
    }
    Ok(entries)
}

/// The item at `place` of `items`, taken (each place is taken at most
/// once): a place the request did not send, or one taken twice, is a
/// reply of an inconsistent build.
fn take<T>(items: &mut [Option<T>], place: u64) -> Result<T, WireError> {
    usize::try_from(place)
        .ok()
        .and_then(|place| items.get_mut(place))
        .and_then(Option::take)
        .ok_or(WireError::Malformed {
            at: 0,
            expected: "a place the request sent, once",
        })
}

/// What a read/modify/write of `edit` over the document `read` writes
/// (`Cf.rmw`): the entries to write, in order, or `None` when the core
/// refuses (the read is broken). The document's entries cross the wire as
/// their places; the edit's key is the place of the entry with that key
/// (the place after the last when there is none), its value the place
/// after the last.
#[must_use]
pub fn rmw<K: PartialEq, V>(read: Read<K, V>, edit: Edit<K, V>) -> Option<Vec<(K, V)>> {
    expect_core(Entry::Config, rmw_call(read, edit))
}

fn rmw_call<K: PartialEq, V>(
    read: Read<K, V>,
    edit: Edit<K, V>,
) -> Result<Option<Vec<(K, V)>>, Error> {
    let mut request = Writer::new();
    request.tag(0);
    let document = match read {
        Read::Missing => {
            request.tag(0);
            Vec::new()
        }
        Read::Parsed(document) => {
            request.tag(1).count(document.len());
            for place in 0..document.len() as u64 {
                request.nat(place).nat(place);
            }
            document
        }
        Read::Broken => {
            request.tag(2);
            Vec::new()
        }
    };
    let last = document.len() as u64;
    let place_of = |key: &K| {
        document
            .iter()
            .position(|(known, _)| known == key)
            .map_or(last, |place| place as u64)
    };
    let (key, value) = match edit {
        Edit::Set(key, value) => {
            request.tag(0).nat(place_of(&key)).nat(last);
            (key, Some(value))
        }
        Edit::Delete(key) => {
            request.tag(1).nat(place_of(&key));
            (key, None)
        }
    };
    let reply = call(Entry::Config, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    if reply.tag_of(2, "a write")? == 0 {
        reply.end()?;
        return Ok(None);
    }
    let written = read_entries(&mut reply)?;
    reply.end()?;
    let (keys, values): (Vec<_>, Vec<_>) = document
        .into_iter()
        .map(|(key, value)| (Some(key), Some(value)))
        .unzip();
    let mut keys = keys;
    let mut values = values;
    keys.push(Some(key));
    values.push(value);
    let mut out = Vec::with_capacity(written.len());
    for (key, value) in written {
        out.push((take(&mut keys, key)?, take(&mut values, value)?));
    }
    Ok(Some(out))
}

/// What the load of one leaf of a settings document found.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Outcome {
    /// The value is one its setting holds.
    Good,
    /// A value its setting (or its cvar) does not admit.
    BadType,
    /// A key no setting declares.
    Undeclared,
}

/// The leaves that apply and the leaves a diagnostic names, each by its
/// path's place, in order (`Cf.applied`, `Cf.reported`).
#[must_use]
pub fn leaves(leaves: &[(u64, Outcome)]) -> (Vec<u64>, Vec<u64>) {
    expect_core(Entry::Config, leaves_call(leaves))
}

fn leaves_call(leaves: &[(u64, Outcome)]) -> Result<(Vec<u64>, Vec<u64>), Error> {
    let mut request = Writer::new();
    request.tag(1).count(leaves.len());
    for &(path, outcome) in leaves {
        request.nat(path).tag(match outcome {
            Outcome::Good => 0,
            Outcome::BadType => 1,
            Outcome::Undeclared => 2,
        });
    }
    let reply = call(Entry::Config, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let mut paths = || -> Result<Vec<u64>, crate::WireError> {
        let count = reply.count()?;
        (0..count).map(|_| reply.nat()).collect()
    };
    let applied = paths()?;
    let reported = paths()?;
    reply.end()?;
    Ok((applied, reported))
}

/// One provider's `providerMaxInFlight` entry as written.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Val {
    /// A whole number (a count past `u32::MAX` is `u32::MAX`).
    Num(u32),
    /// Anything else.
    Malformed,
}

/// `providerMaxInFlight` as written.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InFlight<'a> {
    Unset,
    /// A map: each provider's place and its entry.
    Map(&'a [(u64, Val)]),
    /// A value that is not a map.
    NotMap,
}

/// A provider's in-flight limit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Lim {
    Unlimited,
    Cap(u32),
}

/// The in-flight limit of each provider of `providers` (places), in order
/// (`Cf.limits`).
#[must_use]
pub fn limits(in_flight: InFlight<'_>, providers: &[u64]) -> Vec<Lim> {
    expect_core(Entry::Config, limits_call(in_flight, providers))
}

fn limits_call(in_flight: InFlight<'_>, providers: &[u64]) -> Result<Vec<Lim>, Error> {
    let mut request = Writer::new();
    request.tag(2);
    match in_flight {
        InFlight::Unset => {
            request.tag(0);
        }
        InFlight::Map(slots) => {
            request.tag(1).count(slots.len());
            for &(provider, value) in slots {
                request.nat(provider);
                match value {
                    Val::Num(n) => request.tag(0).u32(n),
                    Val::Malformed => request.tag(1),
                };
            }
        }
        InFlight::NotMap => {
            request.tag(2);
        }
    }
    request.count(providers.len());
    for &provider in providers {
        request.nat(provider);
    }
    let reply = call(Entry::Config, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let count = reply.count()?;
    let mut limits = Vec::with_capacity(count);
    for _ in 0..count {
        limits.push(match reply.tag_of(2, "a limit")? {
            0 => Lim::Unlimited,
            _ => Lim::Cap(reply.u32()?),
        });
    }
    reply.end()?;
    Ok(limits)
}

/// Whether the project directory is trusted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Trust {
    Trusted,
    Untrusted,
}

/// What applies of the leaves `keys` of a project document (or a project
/// prompt file) under `trust`, each a path (the key names from the top,
/// or the file name) and a value: the leaves that apply, in order, and
/// the names of the withheld ones, each once (`Cf.project` over no global
/// entries, `Cf.withheld`).
///
/// # Errors
///
/// [`Error::Wire`] when a key name is past the wire's bounds
/// ([`crate::wire::STR_MAX`] chars); else only from an inconsistent build.
#[allow(clippy::type_complexity)] // the leaves that apply and the withheld names
pub fn project<V>(
    trust: Trust,
    keys: Vec<(Vec<String>, V)>,
) -> Result<(Vec<(Vec<String>, V)>, Vec<String>), Error> {
    let mut request = Writer::new();
    request
        .tag(3)
        .tag(match trust {
            Trust::Trusted => 0,
            Trust::Untrusted => 1,
        })
        .count(keys.len());
    for (place, (path, _)) in keys.iter().enumerate() {
        request.nat(place as u64).count(path.len());
        for name in path {
            request.str(name);
        }
        request.nat(place as u64);
    }
    let reply = call(Entry::Config, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let applied = read_entries(&mut reply)?;
    let count = reply.count()?;
    let mut withheld = Vec::with_capacity(count);
    for _ in 0..count {
        withheld.push(reply.str()?.to_string());
    }
    reply.end()?;
    let (paths, values): (Vec<_>, Vec<_>) = keys
        .into_iter()
        .map(|(path, value)| (Some(path), Some(value)))
        .unzip();
    let (mut paths, mut values) = (paths, values);
    let mut kept = Vec::with_capacity(applied.len());
    for (key, value) in applied {
        kept.push((take(&mut paths, key)?, take(&mut values, value)?));
    }
    Ok((kept, withheld))
}

/// The entries that apply when the `project` entries go over the `global`
/// ones (`Cf.finds` of `Cf.merge` over every name, the global names first):
/// a project entry replaces the global entry of its name whole. Each entry
/// is one field, its whole value; names and values cross the wire as their
/// places.
#[must_use]
pub fn merge<N: PartialEq, V>(global: Vec<(N, V)>, project: Vec<(N, V)>) -> Vec<(N, V)> {
    expect_core(Entry::Config, merge_call(global, project))
}

fn merge_call<N: PartialEq, V>(
    global: Vec<(N, V)>,
    project: Vec<(N, V)>,
) -> Result<Vec<(N, V)>, Error> {
    let mut names: Vec<Option<N>> = Vec::new();
    let mut values: Vec<Option<V>> = Vec::new();
    let mut request = Writer::new();
    request.tag(4);
    for side in [global, project] {
        request.count(side.len());
        for (name, value) in side {
            let place =
                if let Some(place) = names.iter().position(|known| known.as_ref() == Some(&name)) {
                    place
                } else {
                    names.push(Some(name));
                    names.len() - 1
                };
            let value_place = values.len() as u64;
            values.push(Some(value));
            request.nat(place as u64);
            entries(&mut request, &[(value_place, value_place)]);
        }
    }
    request.count(names.len());
    for place in 0..names.len() as u64 {
        request.nat(place);
    }
    let reply = call(Entry::Config, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let count = reply.count()?;
    let mut found = Vec::with_capacity(count);
    for place in 0..count as u64 {
        if reply.maybe()? {
            let fields = read_entries(&mut reply)?;
            let name = take(&mut names, place)?;
            match fields.as_slice() {
                [(key, value)] if key == value => found.push((name, take(&mut values, *value)?)),
                _ => {
                    return Err(WireError::Malformed {
                        at: 0,
                        expected: "an entry of one field",
                    }
                    .into())
                }
            }
        }
    }
    reply.end()?;
    Ok(found)
}

#[cfg(test)]
mod tests {
    use super::{
        leaves, limits, merge, project, rmw, Edit, InFlight, Lim, Outcome, Read, Trust, Val,
    };

    #[test]
    fn the_codec_carries_each_question_through_the_core() {
        let path = |names: &[&str]| names.iter().map(ToString::to_string).collect::<Vec<_>>();
        assert_eq!(
            (
                rmw(Read::Parsed(vec![("a", 1), ("b", 2)]), Edit::Set("a", 3)),
                rmw(Read::Parsed(vec![("a", 1), ("b", 2)]), Edit::Set("c", 3)),
                rmw(Read::<&str, u8>::Broken, Edit::Delete("a")),
                leaves(&[(0, Outcome::Good), (1, Outcome::Undeclared)]),
                limits(
                    InFlight::Map(&[(0, Val::Num(3)), (1, Val::Malformed)]),
                    &[0, 1, 2]
                ),
                project(
                    Trust::Untrusted,
                    vec![(path(&["theme"]), 'a'), (path(&["mcpServers", "x"]), 'b')],
                )
                .unwrap(),
                merge(vec![("g", 1), ("n", 2)], vec![("g", 3), ("p", 4)]),
            ),
            (
                Some(vec![("a", 3), ("b", 2)]),
                Some(vec![("a", 1), ("b", 2), ("c", 3)]),
                None,
                (vec![0], vec![1]),
                vec![Lim::Cap(3), Lim::Cap(1), Lim::Unlimited],
                (
                    vec![(path(&["theme"]), 'a')],
                    vec!["mcpServers".to_string()]
                ),
                vec![("g", 3), ("n", 2), ("p", 4)],
            )
        );
    }
}
