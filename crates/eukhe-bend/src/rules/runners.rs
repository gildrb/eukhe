//! The runners of code (`bend/runners.bend`, entry `bend/ffi_runners.bend`;
//! `laws/runners.bend`): the tools a session installs with their caps and
//! gates, and main's roster. Each function encodes its facts, calls
//! [`Entry::Runners`] and decodes the decision.

use eukhe_types::shell::{ShellEffect, ShellEffects};

use crate::wire::{Reader, Writer};
use crate::{call, expect_core, Entry, Error};

/// How the gate covers a tool's code (`Ru.Gate`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Covered {
    /// The tool runs no code of its own.
    Ungated,
    /// Each step passes the shell step's verdict (`bash`).
    EachStep,
    /// Each call is judged as an effect with its caps (`python`).
    EachCall,
}

/// One tool a session installs (`Ru.Tool`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tool {
    pub name: String,
    /// The effects the code it runs may have.
    pub caps: ShellEffects,
    pub gate: Covered,
}

/// Every tool a session installs, in install order (`Ru.registry`): a
/// `single` session's, every child's.
#[must_use]
pub fn registry() -> Vec<Tool> {
    expect_core(Entry::Runners, roster_call(Roster::Registry))
}

/// Whether main has chat memory (the chat memory's tools join its roster).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChatMemory {
    On,
    Off,
}

/// Main's roster in the `main-worker` shape, in install order
/// (`Ru.main_roster`): read-only tools and the worker tools.
#[must_use]
pub fn main_roster(chat: ChatMemory) -> Vec<Tool> {
    expect_core(Entry::Runners, roster_call(Roster::Main(chat)))
}

/// The roster a request asks for: tag 2 the registry, tag 3 main's.
#[derive(Clone, Copy)]
enum Roster {
    Registry,
    Main(ChatMemory),
}

fn roster_call(roster: Roster) -> Result<Vec<Tool>, Error> {
    let mut request = Writer::new();
    match roster {
        Roster::Registry => request.tag(2),
        Roster::Main(chat) => request.tag(3).bool(chat == ChatMemory::On),
    };
    let reply = call(Entry::Runners, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let count = reader.count()?;
    let mut tools = Vec::with_capacity(count);
    for _ in 0..count {
        let name = reader.str()?.to_owned();
        let mut caps = ShellEffects::NONE;
        for _ in 0..reader.count()? {
            caps.insert(ShellEffect::ALL[reader.tag_of(7, "an effect code")? as usize]);
        }
        let gate = match reader.tag_of(3, "a gate")? {
            0 => Covered::Ungated,
            1 => Covered::EachStep,
            // `tag_of` answers a tag below 3: this is 2.
            _ => Covered::EachCall,
        };
        tools.push(Tool { name, caps, gate });
    }
    reader.end()?;
    Ok(tools)
}
