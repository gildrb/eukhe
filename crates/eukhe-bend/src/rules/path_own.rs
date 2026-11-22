//! The own paths (`bend/path_own.bend`, entry `bend/ffi_path_own.bend`;
//! `laws/path_own.bend`): the agent can't write eukhe's own config and
//! credentials, the session record or a protected file of a check under
//! acceptance (spec/README.md I3). The caller names those places as own
//! rules over real paths, resolves the path an access touches and asks its
//! class here, given the path policy's class of it: a write an own rule
//! names is [`Class::Own`] (refused); anything else keeps that class. Every
//! path component crosses as an id (equal names, equal ids).

use std::collections::HashMap;
use std::ffi::OsStr;
use std::path::{Component, Path};

use eukhe_types::path_policy::{PathClass, RealPath};

use crate::wire::{Reader, WireError, Writer};
use crate::{call, expect_core, Entry, Error};

/// One own rule, over a real path.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rule<'a> {
    /// The path and everything under it.
    Tree(&'a Path),
    /// The directory itself and every entry directly in it (not deeper).
    Dir(&'a Path),
}

/// What an access does to the path.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Access {
    /// Reads it (a file, a listing, a search).
    Read,
    /// Writes, creates, moves or deletes it.
    Write,
}

/// The class of an access.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Class {
    /// No own rule names it (or it reads): the path policy's class.
    Judged(PathClass),
    /// A write the own rule at this index names (the first that does):
    /// refused.
    Own(usize),
}

/// The class of `access` to `resolved` under the own rules `own`, the path
/// policy having judged it `judged` (`Po.class`): a write the first own
/// rule naming the real path names is [`Class::Own`] with that rule's
/// index; a read, or a write no rule names, is `judged`.
#[must_use]
pub fn class(own: &[Rule<'_>], resolved: &RealPath, judged: PathClass, access: Access) -> Class {
    expect_core(Entry::PathOwn, decide(own, resolved, judged, access))
}

/// Interns path components: each distinct name is one id.
#[derive(Default)]
struct Names<'a> {
    ids: HashMap<&'a OsStr, u64>,
}

impl<'a> Names<'a> {
    fn id(&mut self, name: &'a OsStr) -> u64 {
        let next = u64::try_from(self.ids.len()).unwrap_or(u64::MAX);
        *self.ids.entry(name).or_insert(next)
    }

    /// The ids of `path`'s components, deepest first (`/` is the empty
    /// list).
    fn path(&mut self, path: &'a Path) -> Vec<u64> {
        let mut ids: Vec<u64> = path
            .components()
            .filter(|component| !matches!(component, Component::RootDir))
            .map(|component| self.id(component.as_os_str()))
            .collect();
        ids.reverse();
        ids
    }
}

fn code(class: PathClass) -> u64 {
    match class {
        PathClass::Inside => 0,
        PathClass::Outside => 1,
        PathClass::Protected => 2,
        PathClass::Secret => 3,
    }
}

fn decide(
    own: &[Rule<'_>],
    resolved: &RealPath,
    judged: PathClass,
    access: Access,
) -> Result<Class, Error> {
    let mut names = Names::default();
    let rules: Vec<Vec<u64>> = own
        .iter()
        .map(|rule| match rule {
            Rule::Tree(path) => [vec![0], names.path(path)].concat(),
            Rule::Dir(path) => [vec![1], names.path(path)].concat(),
        })
        .collect();
    let at = names.path(resolved.path());
    let mut request = Writer::new();
    // The rules as one list: each item 1 + its value, each rule ended by 0
    // (`bend/wire_flat.bend`).
    request.count(rules.iter().map(|rule| rule.len() + 1).sum());
    for rule in &rules {
        for item in rule {
            request.nat(item + 1);
        }
        request.nat(0);
    }
    request.count(at.len());
    for id in &at {
        request.nat(*id);
    }
    request.nat(code(judged)).bool(access == Access::Write);
    let reply = call(Entry::PathOwn, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let class = match reader.tag_of(2, "a write class")? {
        0 => Class::Judged(match reader.tag_of(4, "a path class")? {
            0 => PathClass::Inside,
            1 => PathClass::Outside,
            2 => PathClass::Protected,
            // `tag_of` answers a tag below 4: this is 3.
            _ => PathClass::Secret,
        }),
        // `tag_of` answers a tag below 2: this is 1.
        _ => Class::Own(
            usize::try_from(reader.nat()?).map_err(|_| WireError::Malformed {
                at: 0,
                expected: "an own rule's index",
            })?,
        ),
    };
    reader.end()?;
    Ok(class)
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use eukhe_types::path_policy::{resolve, PathClass};

    use super::{class, Access, Class, Rule};

    #[test]
    fn a_write_an_own_rule_names_is_own_at_the_first_such_rule() {
        let own = [
            Rule::Tree(Path::new("/h/.eukhe/agent/sessions")),
            Rule::Tree(Path::new("/h/w/settings.json")),
            Rule::Dir(Path::new("/h/.eukhe/agent")),
        ];
        let write =
            |path: &str, judged| class(&own, &resolve(Path::new(path)), judged, Access::Write);
        assert_eq!(
            (
                write(
                    "/h/.eukhe/agent/sessions/s1/log.jsonl",
                    PathClass::Protected
                ),
                write("/h/.eukhe/agent/sessions", PathClass::Protected),
                write("/h/w/settings.json", PathClass::Inside),
                write("/h/.eukhe/agent/auth.json", PathClass::Secret),
                write("/h/.eukhe/agent", PathClass::Protected),
            ),
            (
                Class::Own(0),
                Class::Own(0),
                Class::Own(1),
                Class::Own(2),
                Class::Own(2)
            )
        );
    }

    #[test]
    fn a_read_or_a_write_no_rule_names_keeps_the_judged_class() {
        let own = [Rule::Dir(Path::new("/h/.eukhe/agent"))];
        assert_eq!(
            (
                class(
                    &own,
                    &resolve(Path::new("/h/.eukhe/agent/auth.json")),
                    PathClass::Secret,
                    Access::Read
                ),
                class(
                    &own,
                    &resolve(Path::new("/h/.eukhe/agent/cache/x")),
                    PathClass::Protected,
                    Access::Write
                ),
                class(
                    &own,
                    &resolve(Path::new("/h/.eukhe")),
                    PathClass::Protected,
                    Access::Write
                ),
                class(
                    &own,
                    &resolve(Path::new("/h/w/src/main.rs")),
                    PathClass::Inside,
                    Access::Write
                ),
            ),
            (
                Class::Judged(PathClass::Secret),
                Class::Judged(PathClass::Protected),
                Class::Judged(PathClass::Protected),
                Class::Judged(PathClass::Inside)
            )
        );
    }
}
