//! The shell step (`bend/tools.bend` part 4, entry `bend/ffi_shell.bend`;
//! `laws/shell.bend`): the effects of a step made of parts and whether it
//! runs ([`verdict`]: every step runs but one that writes an own path).
//! The approval gate ([`step`], [`allows`], [`answered`]) stays for the
//! callers that still ask it. Each function encodes the facts Rust
//! gathered, calls [`Entry::Shell`] and decodes the decision.

use eukhe_types::shell::{AutoSet, ShellEffect, ShellEffects};

use crate::wire::{Reader, Writer};
use crate::{call, expect_core, Entry, Error};

/// One part of a step: its command, a redirection, a path it names, the
/// working directory it reads (`bend/tools.bend` `Part`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Part {
    /// The part's own effects (the command table's, a target class's).
    pub own: ShellEffects,
    /// Whether the part names a path that is or holds a secret.
    pub names_secret: bool,
}

/// Whether a step runs without a question.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Gate {
    /// Its effects are within the auto set: it runs unasked.
    Unasked,
    /// It runs only when the user approves it.
    Asks,
}

/// The user's answer to a gated step, as the gate reads it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Said {
    /// The user approved the step.
    Yes,
    /// A denial, no answer, or the gateway rule's refusal.
    No,
}

/// What an answer does to the script.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Answered {
    /// The step runs.
    Runs,
    /// The script stops at this step: it and every later step do not run.
    Stops {
        /// The step the script stops at.
        step: u64,
    },
}

/// One part of a step as its verdict reads it (`bend/tools.bend` `Piece`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StepPart {
    /// The part's own effects (the command table's, a target class's).
    pub own: ShellEffects,
    /// Whether the part names a path that is or holds a secret.
    pub names_secret: bool,
    /// Whether the part writes an own path: eukhe's own config and
    /// credentials, the session record, a protected file of a check.
    pub writes_own: bool,
}

/// Whether a step runs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    /// It runs, unasked.
    Runs,
    /// A part writes an own path: the step and every later step of the
    /// script do not run.
    Refused,
}

/// The effects of a step made of `parts` (every effect of every part; the
/// secret effect only from a part that names a secret path) and whether it
/// runs: refused exactly when a part writes an own path (`Tl.pieces.effs`,
/// `Tl.verdict`).
#[must_use]
pub fn verdict(parts: &[StepPart]) -> (ShellEffects, Verdict) {
    expect_core(Entry::Shell, verdict_call(parts))
}

fn verdict_call(parts: &[StepPart]) -> Result<(ShellEffects, Verdict), Error> {
    let mut request = Writer::new();
    request.tag(3);
    // bend/wire_flat.bend: each part is its two flags and its codes, each
    // item written as 1 + item, the part ending with 0.
    let items: usize = parts.iter().map(|part| 3 + part.own.iter().count()).sum();
    request.count(items);
    for part in parts {
        request.nat(1 + u64::from(part.names_secret));
        request.nat(1 + u64::from(part.writes_own));
        for effect in part.own.iter() {
            request.nat(1 + u64::from(effect.code()));
        }
        request.nat(0);
    }
    let reply = call(Entry::Shell, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let mut effects = ShellEffects::NONE;
    for _ in 0..reader.count()? {
        effects.insert(effect(&mut reader)?);
    }
    let verdict = match reader.tag_of(2, "a step's verdict")? {
        0 => Verdict::Runs,
        // `tag_of` answers a tag below 2: this is 1.
        _ => Verdict::Refused,
    };
    reader.end()?;
    Ok((effects, verdict))
}

/// The effects of a step made of `parts` (every effect of every part; the
/// secret effect only from a part that names a secret path) and whether it
/// runs unasked under `auto` (`Tl.join`, `Tl.within`).
#[must_use]
pub fn step(auto: AutoSet, parts: &[Part]) -> (ShellEffects, Gate) {
    expect_core(Entry::Shell, step_call(auto, parts))
}

fn step_call(auto: AutoSet, parts: &[Part]) -> Result<(ShellEffects, Gate), Error> {
    let mut request = Writer::new();
    request.tag(0);
    codes(&mut request, auto.effects());
    // bend/wire_flat.bend: each part is its flag and its codes, each item
    // written as 1 + item, the part ending with 0.
    let items: usize = parts.iter().map(|part| 2 + part.own.iter().count()).sum();
    request.count(items);
    for part in parts {
        request.nat(1 + u64::from(part.names_secret));
        for effect in part.own.iter() {
            request.nat(1 + u64::from(effect.code()));
        }
        request.nat(0);
    }
    let reply = call(Entry::Shell, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let mut effects = ShellEffects::NONE;
    for _ in 0..reader.count()? {
        effects.insert(effect(&mut reader)?);
    }
    let gate = gate(reader.bool()?);
    reader.end()?;
    Ok((effects, gate))
}

/// Whether an access with `effects` runs unasked under `auto`
/// (`Tl.within`).
#[must_use]
pub fn allows(auto: AutoSet, effects: ShellEffects) -> Gate {
    expect_core(Entry::Shell, allows_call(auto, effects))
}

fn allows_call(auto: AutoSet, effects: ShellEffects) -> Result<Gate, Error> {
    let mut request = Writer::new();
    request.tag(1);
    codes(&mut request, auto.effects());
    codes(&mut request, effects);
    let reply = call(Entry::Shell, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let gate = gate(reader.bool()?);
    reader.end()?;
    Ok(gate)
}

/// What the answer `said` to the gated step `step` does (`Tl.gate`).
#[must_use]
pub fn answered(step: u64, said: Said) -> Answered {
    expect_core(Entry::Shell, answered_call(step, said))
}

fn answered_call(step: u64, said: Said) -> Result<Answered, Error> {
    let mut request = Writer::new();
    request.tag(2).nat(step).bool(said == Said::Yes);
    let reply = call(Entry::Shell, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let answered = match reader.tag_of(2, "what an answer does")? {
        0 => Answered::Runs,
        // `tag_of` answers a tag below 2: this is 1.
        _ => Answered::Stops {
            step: reader.nat()?,
        },
    };
    reader.end()?;
    Ok(answered)
}

/// A set of effects as the list of their codes.
fn codes(request: &mut Writer, effects: ShellEffects) {
    request.count(effects.iter().count());
    for effect in effects.iter() {
        request.nat(u64::from(effect.code()));
    }
}

/// The effect of a code of the reply.
fn effect(reader: &mut Reader<'_>) -> Result<ShellEffect, Error> {
    let code = reader.tag_of(7, "an effect code")?;
    Ok(ShellEffect::ALL[code as usize])
}

fn gate(unasked: bool) -> Gate {
    if unasked {
        Gate::Unasked
    } else {
        Gate::Asks
    }
}

#[cfg(test)]
mod tests {
    use eukhe_types::shell::{AutoSet, ShellEffect, ShellEffects};

    use super::{allows, answered, step, verdict, Answered, Gate, Part, Said, StepPart, Verdict};

    #[test]
    fn a_step_runs_unless_a_part_writes_an_own_path() {
        let read = StepPart {
            own: ShellEffects::of(&[ShellEffect::Read]),
            names_secret: false,
            writes_own: false,
        };
        let secret_write = StepPart {
            own: ShellEffects::of(&[ShellEffect::Write, ShellEffect::Outside]),
            names_secret: true,
            writes_own: false,
        };
        let own_write = StepPart {
            own: ShellEffects::of(&[ShellEffect::Write, ShellEffect::Protected]),
            names_secret: false,
            writes_own: true,
        };
        assert_eq!(
            (
                verdict(&[]),
                verdict(&[read, secret_write]),
                verdict(&[read, own_write]),
            ),
            (
                (ShellEffects::NONE, Verdict::Runs),
                (
                    ShellEffects::of(&[
                        ShellEffect::Read,
                        ShellEffect::Write,
                        ShellEffect::Outside,
                        ShellEffect::Secret,
                    ]),
                    Verdict::Runs,
                ),
                (
                    ShellEffects::of(&[
                        ShellEffect::Read,
                        ShellEffect::Write,
                        ShellEffect::Protected,
                    ]),
                    Verdict::Refused,
                ),
            )
        );
    }

    #[test]
    fn the_codec_carries_each_question_through_the_core() {
        let parts = [
            Part {
                own: ShellEffects::of(&[ShellEffect::Read]),
                names_secret: false,
            },
            Part {
                own: ShellEffects::of(&[ShellEffect::Write, ShellEffect::Outside]),
                names_secret: true,
            },
        ];
        let auto = AutoSet::new([ShellEffect::Read, ShellEffect::Write]);
        assert_eq!(
            (
                step(auto, &parts),
                allows(auto, ShellEffects::of(&[ShellEffect::Read])),
                answered(4, Said::No),
                answered(4, Said::Yes),
            ),
            (
                (
                    ShellEffects::of(&[
                        ShellEffect::Read,
                        ShellEffect::Write,
                        ShellEffect::Outside,
                        ShellEffect::Secret,
                    ]),
                    Gate::Asks,
                ),
                Gate::Unasked,
                Answered::Stops { step: 4 },
                Answered::Runs,
            )
        );
    }
}
