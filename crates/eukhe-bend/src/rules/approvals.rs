//! Where a question of the approval gate goes, one session at a time
//! (`bend/approvals.bend` `next`, `answered`, `default_auto`; entry
//! `bend/ffi_approvals.bend`; `laws/approvals.bend`): what a session does
//! with a question, what its clients' answer makes of the step, and the
//! default auto set. Each function encodes its facts, calls
//! [`Entry::Approvals`] and decodes the decision. The interleaving of the
//! sessions (the relay to a parent, clients that leave, the first answer)
//! is the caller's.

use eukhe_types::shell::{AutoSet, ShellAnswer, ShellEffect, ShellEffects};

use super::shell::Said;
use crate::wire::{Reader, Writer};
use crate::{call, expect_core, Entry, Error};

/// Who answers a question of the session now (`Am.Here`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Here {
    /// No client is attached.
    Nobody,
    /// Clients are attached, and all are the phone gateway.
    GatewayOnly,
    /// An interactive client is attached.
    Clients,
}

/// Whether the session has a parent session.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Parent {
    /// A session above it can take the question.
    Above,
    /// It is a root.
    Root,
}

/// What the session does with the question (`Am.Next`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Next {
    /// Show it to its clients: their answer, or their leaving, decides.
    Show,
    /// Hand it to the parent session.
    Relay,
    /// It ends here with this answer.
    Ends(ShellAnswer),
}

/// What a session that is `here` (with a parent or not) does with the
/// question of a step with `effects` (`Am.next`).
#[must_use]
pub fn next(here: Here, effects: ShellEffects, parent: Parent) -> Next {
    expect_core(Entry::Approvals, next_call(here, effects, parent))
}

fn next_call(here: Here, effects: ShellEffects, parent: Parent) -> Result<Next, Error> {
    let mut request = Writer::new();
    request.tag(0).tag(match here {
        Here::Nobody => 0,
        Here::GatewayOnly => 1,
        Here::Clients => 2,
    });
    codes(&mut request, effects);
    request.bool(parent == Parent::Above);
    let reply = call(Entry::Approvals, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let next = match reader.tag_of(3, "what a session does with a question")? {
        0 => Next::Show,
        1 => Next::Relay,
        // `tag_of` answers a tag below 3: this is 2.
        _ => Next::Ends(fate(&mut reader)?),
    };
    reader.end()?;
    Ok(next)
}

/// What the answer `said` of a session's clients makes of a step with
/// `effects` (`Am.answered`).
#[must_use]
pub fn answered(effects: ShellEffects, said: Said) -> ShellAnswer {
    expect_core(Entry::Approvals, answered_call(effects, said))
}

fn answered_call(effects: ShellEffects, said: Said) -> Result<ShellAnswer, Error> {
    let mut request = Writer::new();
    request.tag(1);
    codes(&mut request, effects);
    request.bool(said == Said::Yes);
    let reply = call(Entry::Approvals, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let answer = fate(&mut reader)?;
    reader.end()?;
    Ok(answer)
}

/// The auto set of a session whose user sets none (`Am.default_auto`).
#[must_use]
pub fn default_auto() -> AutoSet {
    expect_core(Entry::Approvals, default_auto_call())
}

fn default_auto_call() -> Result<AutoSet, Error> {
    let mut request = Writer::new();
    request.tag(2);
    let reply = call(Entry::Approvals, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let mut effects = Vec::new();
    for _ in 0..reader.count()? {
        effects.push(ShellEffect::ALL[reader.tag_of(7, "an effect code")? as usize]);
    }
    reader.end()?;
    Ok(AutoSet::new(effects))
}

/// A step's fate (`Am.Fate`) as the answer the gate reads.
fn fate(reader: &mut Reader<'_>) -> Result<ShellAnswer, Error> {
    Ok(match reader.tag_of(4, "a step's fate")? {
        0 => ShellAnswer::Approve,
        1 => ShellAnswer::Deny,
        2 => ShellAnswer::Unanswered,
        // `tag_of` answers a tag below 4: this is 3.
        _ => ShellAnswer::GatewayRefused,
    })
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
    use eukhe_types::shell::{AutoSet, ShellAnswer, ShellEffect, ShellEffects};

    use super::{answered, default_auto, next, Here, Next, Parent};
    use crate::rules::shell::Said;

    #[test]
    fn the_codec_carries_each_question_through_the_core() {
        let write = ShellEffects::of(&[ShellEffect::Write]);
        let secret = ShellEffects::of(&[ShellEffect::Read, ShellEffect::Secret]);
        assert_eq!(
            (
                next(Here::Clients, write, Parent::Root),
                next(Here::Nobody, write, Parent::Above),
                next(Here::Nobody, write, Parent::Root),
                next(Here::GatewayOnly, write, Parent::Above),
                next(Here::GatewayOnly, secret, Parent::Root),
                answered(write, Said::No),
                answered(write, Said::Yes),
                default_auto(),
            ),
            (
                Next::Show,
                Next::Relay,
                Next::Ends(ShellAnswer::Unanswered),
                Next::Ends(ShellAnswer::Approve),
                Next::Ends(ShellAnswer::GatewayRefused),
                ShellAnswer::Deny,
                ShellAnswer::Approve,
                AutoSet::new(ShellEffect::ALL.into_iter().take(6)),
            )
        );
    }
}
