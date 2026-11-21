//! The shell step (`bend/tools.bend` part 4, entry `bend/ffi_shell.bend`;
//! `laws/shell.bend`): the effects of a step made of parts and whether it
//! runs ([`verdict`]: every step runs but one that writes an own path).
//! It encodes the facts Rust gathered, calls [`Entry::Shell`] and decodes
//! the decision.

use eukhe_types::shell::{ShellEffect, ShellEffects};

use crate::wire::{Reader, Writer};
use crate::{call, expect_core, Entry, Error};

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

/// The effect of a code of the reply.
fn effect(reader: &mut Reader<'_>) -> Result<ShellEffect, Error> {
    let code = reader.tag_of(7, "an effect code")?;
    Ok(ShellEffect::ALL[code as usize])
}

#[cfg(test)]
mod tests {
    use eukhe_types::shell::{ShellEffect, ShellEffects};

    use super::{verdict, StepPart, Verdict};

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
}
