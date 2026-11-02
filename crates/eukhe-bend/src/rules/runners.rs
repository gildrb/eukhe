//! The runners of code (`bend/runners.bend`, entry `bend/ffi_runners.bend`;
//! `laws/runners.bend`): whether a call of a tool that runs code runs
//! unasked, how a gated call ends once the user answered (or no one
//! could), and the tools a session installs with their caps and gates.
//! Each function encodes its facts, calls [`Entry::Runners`] and decodes
//! the decision.

use eukhe_types::shell::{AutoSet, ShellEffect, ShellEffects};

use super::shell::{Gate, Said};
use crate::wire::{Reader, Writer};
use crate::{call, expect_core, Entry, Error};

/// Who answered the question about a gated call (`Ru.Asker`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Asker {
    /// No approver is attached: no one was asked.
    NoClient,
    /// An approver was asked and gave no answer.
    Silent,
    /// The user answered.
    Says(Said),
}

/// How a gated call ended (`Ru.End`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ended {
    /// Its code runs: within the auto set.
    RanUnasked,
    /// Its code runs: the user approved it.
    RanApproved,
    /// It does not run: the user denied it.
    Denied,
    /// It does not run: no one answered.
    Unanswered,
}

/// How the approval gate covers a tool's code (`Ru.Gate`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Covered {
    /// The tool runs no code of its own.
    Ungated,
    /// Each step asks unless within the auto set (`bash`).
    EachStep,
    /// Each call asks unless within the auto set (`ipython`).
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

/// Whether the session has chat memory (its tools join the registry).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChatMemory {
    On,
    Off,
}

/// Whether a call of a tool with `caps` runs unasked under `auto`
/// (`Ru.within`).
#[must_use]
pub fn within(auto: AutoSet, caps: ShellEffects) -> Gate {
    expect_core(Entry::Runners, within_call(auto, caps))
}

fn within_call(auto: AutoSet, caps: ShellEffects) -> Result<Gate, Error> {
    let mut request = Writer::new();
    request.tag(0);
    codes(&mut request, caps);
    codes(&mut request, auto.effects());
    let reply = call(Entry::Runners, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let gate = if reader.bool()? {
        Gate::Unasked
    } else {
        Gate::Asks
    };
    reader.end()?;
    Ok(gate)
}

/// How a call of a tool with `caps` under `auto` ends when `asker`
/// answered (`Ru.cell`).
#[must_use]
pub fn cell(auto: AutoSet, caps: ShellEffects, asker: Asker) -> Ended {
    expect_core(Entry::Runners, cell_call(auto, caps, asker))
}

fn cell_call(auto: AutoSet, caps: ShellEffects, asker: Asker) -> Result<Ended, Error> {
    let mut request = Writer::new();
    request.tag(1);
    codes(&mut request, caps);
    codes(&mut request, auto.effects());
    match asker {
        Asker::NoClient => request.tag(0),
        Asker::Silent => request.tag(1),
        Asker::Says(said) => request.tag(2).bool(said == Said::Yes),
    };
    let reply = call(Entry::Runners, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    // Whether it asked: the caller knows it asked an approver.
    reader.bool()?;
    let ran = reader.tag_of(2, "how a call ended")? == 0;
    let second = reader.tag_of(2, "how a call ran or why it was refused")? == 0;
    reader.end()?;
    Ok(match (ran, second) {
        (true, true) => Ended::RanUnasked,
        (true, false) => Ended::RanApproved,
        (false, true) => Ended::Denied,
        (false, false) => Ended::Unanswered,
    })
}

/// Every tool a session installs, in install order (`Ru.registry`): a
/// `single` session's, every child's.
#[must_use]
pub fn registry(chat: ChatMemory) -> Vec<Tool> {
    expect_core(Entry::Runners, roster_call(REGISTRY, chat))
}

/// Main's roster in the `main-worker` shape, in install order
/// (`Ru.main_roster`): read-only tools and the worker tools.
#[must_use]
pub fn main_roster(chat: ChatMemory) -> Vec<Tool> {
    expect_core(Entry::Runners, roster_call(MAIN_ROSTER, chat))
}

/// The request tags of the two rosters.
const REGISTRY: u32 = 2;
const MAIN_ROSTER: u32 = 3;

fn roster_call(tag: u32, chat: ChatMemory) -> Result<Vec<Tool>, Error> {
    let mut request = Writer::new();
    request.tag(tag).bool(chat == ChatMemory::On);
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

/// A set of effects as the list of their codes.
fn codes(request: &mut Writer, effects: ShellEffects) {
    request.count(effects.iter().count());
    for effect in effects.iter() {
        request.nat(u64::from(effect.code()));
    }
}

#[cfg(test)]
mod tests {
    use eukhe_types::shell::{AutoSet, ShellEffect, ShellEffects};

    use super::{cell, within, Asker, Ended};
    use crate::rules::shell::{Gate, Said};

    #[test]
    fn the_codec_carries_each_question_through_the_core() {
        let exec = ShellEffects::of(&[ShellEffect::Exec]);
        let read = AutoSet::new([ShellEffect::Read]);
        assert_eq!(
            (
                within(read, exec),
                within(AutoSet::new([ShellEffect::Exec]), exec),
                cell(read, exec, Asker::NoClient),
                cell(read, exec, Asker::Silent),
                cell(read, exec, Asker::Says(Said::No)),
                cell(read, exec, Asker::Says(Said::Yes)),
            ),
            (
                Gate::Asks,
                Gate::Unasked,
                Ended::Unanswered,
                Ended::Unanswered,
                Ended::Denied,
                Ended::RanApproved,
            )
        );
    }
}
