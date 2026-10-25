//! The code mode tool's description and its `codemode` system prompt
//! section (`bend/codemode_describe.bend`, entry
//! `bend/ffi_codemode_describe.bend`; `laws/codemode_describe.bend`). The
//! caller renders each tool's section (heading, description, declaration)
//! and gives its name and the section's UTF-16 length ([`Tool`]), and each
//! namespace's name, lowercase name, prefix and trimmed description
//! ([`Namespace`]). The core decides each tool's namespace, the groups and
//! their order, which sections fit the budget, every heading and marker,
//! the joints, and the whole description text.

use crate::wire::{Reader, WireError, Writer, NAT_MAX};
use crate::{call, Entry, Error};

/// A tool of the section (`Dsc.Tool`).
#[derive(Clone, Copy, Debug)]
pub struct Tool<'a> {
    /// Its name.
    pub name: &'a str,
    /// The UTF-16 length of its rendered section.
    pub size: u64,
}

/// A namespace (`Dsc.Space`).
#[derive(Clone, Copy, Debug)]
pub struct Namespace<'a> {
    /// Its name, its `##` heading.
    pub name: &'a str,
    /// Its name in lowercase (Rust `to_lowercase`): the first key of the
    /// namespace order.
    pub key: &'a str,
    /// Tools whose names start with it belong to it.
    pub prefix: &'a str,
    /// Its description, trimmed (Rust `trim`); `""` when it has none.
    pub about: &'a str,
}

/// A piece of the section's text (`Dsc.Part`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Part {
    /// A text.
    Text(String),
    /// The rendered section of the tool at this index.
    Section(usize),
}

/// What scripts get beside the tools (the description's `models` part).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Globals {
    /// Scripts get the `models.*` globals.
    pub models: bool,
    /// `models.classify(null, ..)` uses the session's default classifier.
    pub default_classifier: bool,
}

fn index_below(n: u64, len: usize, expected: &'static str) -> Result<usize, WireError> {
    usize::try_from(n)
        .ok()
        .filter(|&index| index < len)
        .ok_or(WireError::Malformed { at: 0, expected })
}

/// The namespace of each tool named in `names`: the index in `prefixes` of
/// the longest prefix the name starts with, the first of equally long ones
/// (`Dsc.space_of`).
///
/// # Errors
///
/// [`Error::Wire`] when a name or prefix is past [`crate::wire::STR_MAX`]
/// chars; else only from an inconsistent build (see [`crate::expect_core`]).
pub fn namespaces(names: &[&str], prefixes: &[&str]) -> Result<Vec<Option<usize>>, Error> {
    let mut request = Writer::new();
    request.tag(0).count(names.len());
    for name in names {
        request.str(name);
    }
    request.count(prefixes.len());
    for prefix in prefixes {
        request.str(prefix);
    }
    let reply = call(Entry::CodemodeDescribe, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let count = reply.count()?;
    if count != names.len() {
        return Err(WireError::Malformed {
            at: 0,
            expected: "a namespace per name",
        }
        .into());
    }
    let mut found = Vec::with_capacity(count);
    for _ in 0..count {
        found.push(if reply.maybe()? {
            Some(index_below(
                reply.nat()?,
                prefixes.len(),
                "a prefix's index",
            )?)
        } else {
            None
        });
    }
    reply.end()?;
    Ok(found)
}

/// The `codemode` section for `tools`, `namespaces` and the budget in
/// tokens, as the texts and tool sections to join in order; `None` without
/// tools (`Dsc.section`).
///
/// # Errors
///
/// [`Error::Wire`] when a name, prefix or description is past
/// [`crate::wire::STR_MAX`] chars; else only from an inconsistent build (see
/// [`crate::expect_core`]).
pub fn section(
    tools: &[Tool<'_>],
    namespaces: &[Namespace<'_>],
    budget: u64,
) -> Result<Option<Vec<Part>>, Error> {
    let mut request = Writer::new();
    request.tag(1).count(tools.len());
    for tool in tools {
        request.str(tool.name).nat(tool.size.min(NAT_MAX));
    }
    request.count(namespaces.len());
    for namespace in namespaces {
        request
            .str(namespace.name)
            .str(namespace.key)
            .str(namespace.prefix)
            .str(namespace.about);
    }
    request.nat(budget.min(NAT_MAX));
    let reply = call(Entry::CodemodeDescribe, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    if !reply.maybe()? {
        reply.end()?;
        return Ok(None);
    }
    let count = reply.count()?;
    let mut parts = Vec::with_capacity(count);
    for _ in 0..count {
        parts.push(match reply.tag_of(2, "a part")? {
            0 => Part::Text(reply.str()?.to_owned()),
            _ => Part::Section(index_below(reply.nat()?, tools.len(), "a tool's index")?),
        });
    }
    reply.end()?;
    Ok(Some(parts))
}

/// The code mode tool's description for the script's `globals`
/// (`Dsc.description`).
///
/// # Errors
///
/// Only from an inconsistent build (see [`crate::expect_core`]).
pub fn description(globals: Globals) -> Result<String, Error> {
    let mut request = Writer::new();
    request
        .tag(2)
        .bool(globals.models)
        .bool(globals.default_classifier);
    let reply = call(Entry::CodemodeDescribe, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let text = reply.str()?.to_owned();
    reply.end()?;
    Ok(text)
}

#[cfg(test)]
mod tests {
    use super::{namespaces, section, Namespace, Part, Tool};

    #[test]
    fn the_codec_carries_the_facts_through_the_core() {
        assert_eq!(
            namespaces(&["mcp__docs__x", "read"], &["mcp__", "mcp__docs__"]).unwrap(),
            [Some(1), None]
        );
        let tools = [
            Tool {
                name: "gh-a",
                size: 160,
            },
            Tool {
                name: "gh-b",
                size: 300,
            },
        ];
        let spaces = [Namespace {
            name: "GitHub",
            key: "github",
            prefix: "gh-",
            about: "",
        }];
        assert_eq!(
            section(&tools, &spaces, 40).unwrap(),
            Some(vec![
                Part::Text("Tools scripts can call (`await tools.<name>(args)`):".to_owned()),
                Part::Text("\n\n".to_owned()),
                Part::Text("## GitHub (some tools not listed)".to_owned()),
                Part::Text("\n\n".to_owned()),
                Part::Section(0),
            ])
        );
    }
}
