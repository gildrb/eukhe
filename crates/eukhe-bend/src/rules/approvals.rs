//! The approval gate (docs/tools.md G5): the model `bend/approvals.bend`,
//! entry `bend/ffi_approvals.bend`, laws `laws/approvals/`.
//!
//! The call answers the default auto set. The stepper is one session's
//! desk: the session's open questions, kept in the compiled core. Its host
//! (`crates/eukhe-daemon/src/shell_approval.rs`) sends each event as it
//! arrives (a question reaches the session, a client answers, a client
//! detaches, a step stops waiting, the parent answers a relay) and does the
//! acts the desk answers. The desk decides what each event means: which
//! question an answer belongs to (the first answer wins), where a question
//! goes when its clients leave, and the step's fate; it wakes each key at
//! most once over every order of events (`approvals_desk_wakes_once`).

use eukhe_types::shell::{AutoSet, ShellAnswer, ShellEffect, ShellEffects};

use super::shell::Said;
use crate::wire::{Reader, WireError, Writer};
use crate::{call, expect_core, Entry, Error, Stepper};

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

/// The key the desk gave a question: the host's waiter for it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Key(u64);

/// What the host does (`Am.Act`), in order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Act {
    /// Send the question's frame to the session's clients.
    Show(Key),
    /// Tell the clients the question is settled.
    Settle(Key),
    /// Hand the question to the parent session; its answer comes back as
    /// [`Desk::back`].
    Relay(Key),
    /// The waiting step fares this answer.
    Wake(Key, ShellAnswer),
    /// The client's answer was taken.
    Took,
    /// No open question takes the client's answer: refuse it.
    Gone,
}

/// One session's desk, kept in the compiled core.
#[derive(Debug)]
pub struct Desk {
    stepper: Stepper,
}

impl Default for Desk {
    fn default() -> Self {
        Self::open()
    }
}

impl Desk {
    /// An empty desk.
    #[must_use]
    pub fn open() -> Self {
        let (stepper, reply) = expect_core(Entry::Approvals, Stepper::open(Entry::Approvals, ""));
        expect_core(
            Entry::Approvals,
            Reader::reply(&reply).and_then(Reader::end),
        );
        Desk { stepper }
    }

    /// A question about a step with `effects` reaches the session, whose
    /// frame names `request_id`; `here` and `parent` say who answers the
    /// session now. Its key, and the acts.
    ///
    /// # Errors
    ///
    /// `request_id` is longer than the wire carries (the desk is kept).
    pub fn ask(
        &mut self,
        request_id: &str,
        effects: ShellEffects,
        here: Here,
        parent: Parent,
    ) -> Result<(Key, Vec<Act>), Error> {
        let mut event = Writer::new();
        event.tag(0).str(request_id);
        event.count(effects.iter().count());
        for effect in effects.iter() {
            event.nat(u64::from(effect.code()));
        }
        event.tag(here_code(here)).bool(parent == Parent::Above);
        let reply = self.stepper.step(&event.finish()?)?;
        let mut reader = Reader::reply(&reply)?;
        let key = Key(reader.nat()?);
        let acts = read_acts(reader)?;
        Ok((key, acts))
    }

    /// A client answers the question its frame named `request_id`.
    ///
    /// # Errors
    ///
    /// `request_id` is longer than the wire carries (the desk is kept).
    pub fn answer(&mut self, request_id: &str, said: Said) -> Result<Vec<Act>, Error> {
        let mut event = Writer::new();
        event.tag(1).str(request_id).bool(said == Said::Yes);
        self.event(&mut event)
    }

    /// A client detached; `here` and `parent` say who answers the session
    /// now.
    pub fn detach(&mut self, here: Here, parent: Parent) -> Vec<Act> {
        let mut event = Writer::new();
        event
            .tag(2)
            .tag(here_code(here))
            .bool(parent == Parent::Above);
        expect_core(Entry::Approvals, self.event(&mut event))
    }

    /// The step of `key` stopped waiting.
    pub fn cancel(&mut self, key: Key) -> Vec<Act> {
        let mut event = Writer::new();
        event.tag(3).nat(key.0);
        expect_core(Entry::Approvals, self.event(&mut event))
    }

    /// The parent session's answer to the relay of `key`
    /// ([`ShellAnswer::Unanswered`] when the relay failed).
    pub fn back(&mut self, key: Key, answer: ShellAnswer) -> Vec<Act> {
        let mut event = Writer::new();
        event.tag(4).nat(key.0).tag(match answer {
            ShellAnswer::Approve => 0,
            ShellAnswer::Deny => 1,
            ShellAnswer::Unanswered => 2,
            ShellAnswer::GatewayRefused => 3,
        });
        expect_core(Entry::Approvals, self.event(&mut event))
    }

    fn event(&mut self, event: &mut Writer) -> Result<Vec<Act>, Error> {
        let reply = self.stepper.step(&event.finish()?)?;
        Ok(read_acts(Reader::reply(&reply)?)?)
    }
}

fn here_code(here: Here) -> u32 {
    match here {
        Here::Nobody => 0,
        Here::GatewayOnly => 1,
        Here::Clients => 2,
    }
}

/// The acts of a reply: their count, then each.
fn read_acts(mut reader: Reader<'_>) -> Result<Vec<Act>, WireError> {
    let count = reader.count()?;
    let mut acts = Vec::with_capacity(count.min(16));
    for _ in 0..count {
        acts.push(match reader.tag_of(6, "a desk act")? {
            0 => Act::Show(Key(reader.nat()?)),
            1 => Act::Settle(Key(reader.nat()?)),
            2 => Act::Relay(Key(reader.nat()?)),
            3 => {
                let key = Key(reader.nat()?);
                Act::Wake(key, fate(&mut reader)?)
            }
            4 => Act::Took,
            // `tag_of` answers a tag below 6: this is 5.
            _ => Act::Gone,
        });
    }
    reader.end()?;
    Ok(acts)
}

/// The auto set of a session whose user sets none (`Am.default_auto`).
#[must_use]
pub fn default_auto() -> AutoSet {
    expect_core(Entry::Approvals, default_auto_call())
}

fn default_auto_call() -> Result<AutoSet, Error> {
    let reply = call(Entry::Approvals, "")?;
    let mut reader = Reader::reply(&reply)?;
    let mut effects = Vec::new();
    for _ in 0..reader.count()? {
        effects.push(ShellEffect::ALL[reader.tag_of(7, "an effect code")? as usize]);
    }
    reader.end()?;
    Ok(AutoSet::new(effects))
}

/// A step's fate (`Am.Fate`) as the answer the gate reads.
fn fate(reader: &mut Reader<'_>) -> Result<ShellAnswer, WireError> {
    Ok(match reader.tag_of(4, "a step's fate")? {
        0 => ShellAnswer::Approve,
        1 => ShellAnswer::Deny,
        2 => ShellAnswer::Unanswered,
        // `tag_of` answers a tag below 4: this is 3.
        _ => ShellAnswer::GatewayRefused,
    })
}

#[cfg(test)]
mod tests {
    use eukhe_types::shell::{AutoSet, ShellAnswer, ShellEffect, ShellEffects};

    use super::{default_auto, Act, Desk, Here, Key, Parent};
    use crate::rules::shell::Said;

    /// The codec carries every event and act through the core (the desk's
    /// rule itself is pinned by `laws/approvals/`).
    #[test]
    fn the_desk_runs_in_the_core() {
        let write = ShellEffects::of(&[ShellEffect::Write]);
        let secret = ShellEffects::of(&[ShellEffect::Read, ShellEffect::Secret]);
        let mut desk = Desk::open();
        let shown = desk
            .ask("call-1:0", write, Here::Clients, Parent::Above)
            .unwrap();
        let ruled = desk
            .ask("call-2:0", secret, Here::GatewayOnly, Parent::Root)
            .unwrap();
        let relayed = desk
            .ask("call-3:0", write, Here::Nobody, Parent::Above)
            .unwrap();
        let denied = desk.answer("call-1:0", Said::No).unwrap();
        let again = desk.answer("call-1:0", Said::Yes).unwrap();
        let back = desk.back(Key(2), ShellAnswer::Approve);
        let left = desk
            .ask("call-4:0", write, Here::Clients, Parent::Root)
            .unwrap();
        let detached = desk.detach(Here::Nobody, Parent::Root);
        let cancelled = desk.cancel(Key(3));
        assert_eq!(
            (shown, ruled, relayed, denied, again, back, left, detached, cancelled),
            (
                (Key(0), vec![Act::Show(Key(0))]),
                (Key(1), vec![Act::Wake(Key(1), ShellAnswer::GatewayRefused)]),
                (Key(2), vec![Act::Relay(Key(2))]),
                vec![
                    Act::Settle(Key(0)),
                    Act::Wake(Key(0), ShellAnswer::Deny),
                    Act::Took
                ],
                vec![Act::Gone],
                vec![Act::Wake(Key(2), ShellAnswer::Approve)],
                (Key(3), vec![Act::Show(Key(3))]),
                vec![
                    Act::Settle(Key(3)),
                    Act::Wake(Key(3), ShellAnswer::Unanswered)
                ],
                vec![],
            )
        );
        assert_eq!(
            default_auto(),
            AutoSet::new(ShellEffect::ALL.into_iter().take(6))
        );
    }
}
