//! The judgment of a path under the session's [`PathPolicy`] (docs/tools.md
//! S7, `LAWS.bend` section `path_policy`): `judge` in `bend/path_policy.bend`,
//! run as the compiled Bend core, one call per path the shell or a
//! document tool touches. The caller resolves the path ([`resolve`], IO)
//! and judges the [`RealPath`] it acts on; a second resolution would lose
//! a loop. Every path component crosses as an id (equal names, equal ids).
//!
//! - The class: Secret under a secret entry; else Protected when a rule
//!   covers it (a Tree rule's path or anything under it, a Dir rule's
//!   directory or an entry directly in it, a Named rule's name as a
//!   component below the path's deepest workspace root) or it is an
//!   ancestor of a rule's entry or of a secret; else Inside under a
//!   workspace root unless its links looped; else Outside.
//! - It holds a secret: it is under a secret entry, or an ancestor of one.

use std::collections::HashMap;
use std::ffi::OsStr;
use std::path::Path;

use eukhe_bend::wire::{Reader, Writer};
use eukhe_bend::{call, expect_core, Entry, Error};
use eukhe_types::path_policy::{resolve, PathClass, PathPolicy, PathRule, RealPath};

/// The judgment of one resolved path.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Judged {
    pub class: PathClass,
    /// It is a secret or a directory that holds one: a recursive read of
    /// it reads a secret.
    pub holds_secret: bool,
}

/// The judgment of `resolved` under `policy`, on its real path as it is
/// (`judge` in `bend/path_policy.bend`, through `bend/ffi_path_policy.bend`).
#[must_use]
pub fn judge(policy: &PathPolicy, resolved: &RealPath) -> Judged {
    expect_core(Entry::PathPolicy, decide(policy, resolved))
}

/// Interns path components: each distinct name is one id, so equal names
/// are equal ids (the model compares names by id).
#[derive(Default)]
struct Names<'a> {
    ids: HashMap<&'a OsStr, u64>,
}

impl<'a> Names<'a> {
    fn id(&mut self, name: &'a OsStr) -> u64 {
        let next = u64::try_from(self.ids.len()).unwrap_or(u64::MAX);
        *self.ids.entry(name).or_insert(next)
    }

    /// The ids of `path`'s components, deepest first, as the model's path
    /// list (`/` is the empty list).
    fn path(&mut self, path: &'a Path) -> Vec<u64> {
        let mut ids: Vec<u64> = path
            .components()
            .filter(|component| !matches!(component, std::path::Component::RootDir))
            .map(|component| self.id(component.as_os_str()))
            .collect();
        ids.reverse();
        ids
    }
}

/// Writes `lists` as one wire list of Nats, each item 1 + its value and
/// each list ended by 0 (`bend/wire_flat.bend`).
fn flat(writer: &mut Writer, lists: &[Vec<u64>]) {
    let len: usize = lists.iter().map(|list| list.len() + 1).sum();
    writer.count(len);
    for list in lists {
        for item in list {
            writer.nat(item + 1);
        }
        writer.nat(0);
    }
}

fn decide(policy: &PathPolicy, resolved: &RealPath) -> Result<Judged, Error> {
    let mut names = Names::default();
    let roots: Vec<Vec<u64>> = policy.roots().iter().map(|root| names.path(root)).collect();
    let rules: Vec<Vec<u64>> = policy
        .protected()
        .iter()
        .map(|rule| match rule {
            PathRule::Tree(path) => [vec![0], names.path(path)].concat(),
            PathRule::Dir(path) => [vec![1], names.path(path)].concat(),
            PathRule::Named(name) => vec![2, names.id(name.as_os_str())],
        })
        .collect();
    let secret: Vec<Vec<u64>> = policy
        .secret()
        .iter()
        .map(|entry| names.path(entry))
        .collect();
    let at = names.path(resolved.path());
    let mut writer = Writer::new();
    flat(&mut writer, &roots);
    flat(&mut writer, &rules);
    flat(&mut writer, &secret);
    writer.count(at.len());
    for id in &at {
        writer.nat(*id);
    }
    writer.bool(resolved.looped());
    let reply = call(Entry::PathPolicy, &writer.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let class = match reader.tag_of(4, "a path class")? {
        0 => PathClass::Inside,
        1 => PathClass::Outside,
        2 => PathClass::Protected,
        3.. => PathClass::Secret,
    };
    let holds_secret = reader.bool()?;
    reader.end()?;
    Ok(Judged {
        class,
        holds_secret,
    })
}

/// The judgment of `absolute`, on its real path ([`resolve`]).
#[must_use]
pub fn judge_path(policy: &PathPolicy, absolute: &Path) -> Judged {
    judge(policy, &resolve(absolute))
}

#[cfg(test)]
mod tests;
