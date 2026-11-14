//! Exactly-once effects: the life of one effect across restarts and what
//! a restart does with it. The model `bend/once.bend`, entry
//! `bend/ffi_once.bend` (a stepper and a call), laws `laws/once.bend`,
//! spec `spec/once/life.bend` (O1-O8).
//!
//! An effect is anything the harness does to the world for a run: a tool
//! call, a subagent spawn, a background job, a cron fire, a heartbeat, the
//! delivery of a queued or steering message, a provider request, a file
//! write. Its owner journals it durably ([`Record`]): intended before
//! anything of it happens, started before each launch, then one end. At
//! every restart of its run the owner reads the journal back into an
//! [`Effect`], looks at the world when it can ([`Seen`]), asks
//! [`Effect::restart`], and does what the [`Verdict`] says. An effect
//! whose repeat nothing drops is never launched twice
//! (`once_never_launches_twice`); a finished one is never launched again
//! (`once_ended_never_launches`); one reported done ran (`once_done_ran`);
//! a cut one is reported interrupted (`once_unknown_is_said`). The answers
//! are the spec's after every prefix of a journal (`once_step_is_spec`).
//!
//! [`key`] is the idempotency key every send of one effect carries: two
//! effects never share one (`once_key_distinct`).

use crate::wire::{Reader, WireError, Writer};
use crate::{call, expect_core, Entry, Stepper};

/// How the run of an effect comes back after a restart.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    /// The run goes on.
    Resume,
    /// The run was ended: nothing of it starts any more.
    Stop,
}

/// What the target of a keyed effect declares of a repeat of its
/// idempotency key: a declaration the principal or the target's operator
/// made, never one a model or a generic tool wrote.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Dedup {
    /// No such declaration, or one that drops a repeat only within a
    /// window (only the harness's own clock could tell that a relaunch
    /// falls inside it): a repeat may take hold again.
    Undeclared,
    /// Every repeat of the key is dropped, whenever it comes.
    Lasting,
}

/// What a second launch of an effect would do.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Policy {
    /// It may change state and nothing drops a repeat: it is never
    /// launched twice.
    Never,
    /// It changes nothing: it may run again.
    Safe,
    /// Every launch carries its idempotency key ([`key`]); it is sent again
    /// under it only when its target's declaration `dedup` is
    /// [`Dedup::Lasting`], at most `cap` more times
    /// (`once_undeduped_sends_once`, `once_keyed_sends_capped`).
    Keyed { dedup: Dedup, cap: u32 },
}

/// What the world shows of a started effect at a restart.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Seen {
    /// Nothing can be asked, or the answer is unclear.
    Dark,
    /// Its effect is there.
    Landed,
    /// Its effect is certainly not there, and its launcher is dead: it can
    /// never land.
    Clean,
}

/// A record of an effect's journal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Record {
    /// Written before anything of the effect happens.
    Intended,
    /// Written before each launch.
    Started,
    /// Written after the effect ended, with its result.
    Finished,
    /// A restart could not tell whether it ran: reported interrupted.
    Unknown,
    /// A restart knows it never ran: reported not started.
    Unstarted,
}

/// An effect as its journal tells it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Life {
    /// No record.
    Absent,
    /// Intended, never launched.
    Pending,
    /// Launched `1 + again` times, no end on record.
    Running { again: u64 },
    /// Finished.
    Ran,
    /// Settled unknown.
    Lost,
    /// Settled unstarted.
    Void,
}

/// What a restart does with an effect.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    /// No record of it: nothing to do.
    Skip,
    /// Journal [`Record::Started`], then run it (a first launch, or one
    /// more).
    Launch,
    /// Journal [`Record::Finished`]: it ran; its effect in the world is its
    /// result.
    Adopt,
    /// Journal [`Record::Unknown`]: report it interrupted; never run it.
    Interrupt,
    /// Journal [`Record::Unstarted`]: report it not started; never run it.
    Abandon,
    /// It ended before: report what the journal says; never run it.
    Settled,
}

/// One effect, its life kept in the compiled core.
#[derive(Debug)]
pub struct Effect {
    stepper: Stepper,
    life: Life,
}

impl Effect {
    /// An effect with no record yet.
    #[must_use]
    pub fn open() -> Effect {
        let (stepper, reply) = expect_core(Entry::Once, Stepper::open(Entry::Once, ""));
        let life = expect_core(Entry::Once, read_life(&reply));
        Effect { stepper, life }
    }

    /// The effect whose journal holds `records`, in order.
    #[must_use]
    pub fn of(records: impl IntoIterator<Item = Record>) -> Effect {
        let mut effect = Effect::open();
        for record in records {
            effect.record(record);
        }
        effect
    }

    /// The next record of the journal: the life after it.
    pub fn record(&mut self, record: Record) -> Life {
        let tag = match record {
            Record::Intended => 0,
            Record::Started => 1,
            Record::Finished => 2,
            Record::Unknown => 3,
            Record::Unstarted => 4,
        };
        let request = expect_core(Entry::Once, Writer::new().tag(0).tag(tag).finish());
        let reply = expect_core(Entry::Once, self.stepper.step(&request));
        self.life = expect_core(Entry::Once, read_life(&reply));
        self.life
    }

    /// The life the records read so far tell.
    #[must_use]
    pub fn life(&self) -> Life {
        self.life
    }

    /// What a restart of the effect's run (`mode`) does with it, the effect
    /// of `policy`, the world showing `seen`. The caller journals the
    /// record the verdict names (through [`Effect::record`], and durably)
    /// before it acts on it.
    pub fn restart(&mut self, mode: Mode, policy: Policy, seen: Seen) -> Verdict {
        let mut request = Writer::new();
        request.tag(1).tag(match mode {
            Mode::Resume => 0,
            Mode::Stop => 1,
        });
        match policy {
            Policy::Never => request.tag(0),
            Policy::Safe => request.tag(1),
            Policy::Keyed { dedup, cap } => request.tag(2).nat(u64::from(cap)).tag(match dedup {
                Dedup::Undeclared => 0,
                Dedup::Lasting => 1,
            }),
        };
        request.tag(match seen {
            Seen::Dark => 0,
            Seen::Landed => 1,
            Seen::Clean => 2,
        });
        let request = expect_core(Entry::Once, request.finish());
        let reply = expect_core(Entry::Once, self.stepper.step(&request));
        expect_core(Entry::Once, read_verdict(&reply))
    }
}

/// What a restart of a run (`mode`) does with the effect whose journal
/// holds `records`, in order: its life and the verdict.
#[must_use]
pub fn restart(
    records: impl IntoIterator<Item = Record>,
    mode: Mode,
    policy: Policy,
    seen: Seen,
) -> (Life, Verdict) {
    let mut effect = Effect::of(records);
    let life = effect.life();
    (life, effect.restart(mode, policy, seen))
}

/// The idempotency key every send of the effect `id` of `scope` (its
/// session) carries: the scope, then the id, each spelled with its length
/// in chars, so two effects never share a key.
#[must_use]
pub fn key(scope: &str, id: &str) -> String {
    expect_core(Entry::Once, key_call(scope, id))
}

fn key_call(scope: &str, id: &str) -> Result<String, crate::Error> {
    let request = Writer::new().str(scope).str(id).finish()?;
    let reply = call(Entry::Once, &request)?;
    // The reply is the key as text (not a wire value), or the error form.
    Reader::reply(&reply)?;
    Ok(reply)
}

fn read_life(reply: &str) -> Result<Life, WireError> {
    let mut r = Reader::reply(reply)?;
    let life = match r.tag_of(6, "a life")? {
        0 => Life::Absent,
        1 => Life::Pending,
        2 => Life::Running { again: r.nat()? },
        3 => Life::Ran,
        4 => Life::Lost,
        // `tag_of` answers a tag below 6: this is 5.
        _ => Life::Void,
    };
    r.end()?;
    Ok(life)
}

fn read_verdict(reply: &str) -> Result<Verdict, WireError> {
    let mut r = Reader::reply(reply)?;
    let verdict = match r.tag_of(6, "a verdict")? {
        0 => Verdict::Skip,
        1 => Verdict::Launch,
        2 => Verdict::Adopt,
        3 => Verdict::Interrupt,
        4 => Verdict::Abandon,
        // `tag_of` answers a tag below 6: this is 5.
        _ => Verdict::Settled,
    };
    r.end()?;
    Ok(verdict)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A tool call cut mid-run: a `never` call is interrupted, a safe one
    /// runs again, a stopped run's is interrupted whatever its policy; the
    /// world showing it landed adopts it, showing it clean launches it.
    #[test]
    fn a_cut_effect_is_decided_by_policy_and_world() {
        let cut = || [Record::Intended, Record::Started];
        let table: Vec<(Mode, Policy, Seen, Verdict)> = [
            (Mode::Resume, Policy::Never, Seen::Dark),
            (Mode::Resume, Policy::Safe, Seen::Dark),
            (Mode::Stop, Policy::Safe, Seen::Dark),
            (Mode::Resume, Policy::Never, Seen::Landed),
            (Mode::Stop, Policy::Never, Seen::Landed),
            (Mode::Resume, Policy::Never, Seen::Clean),
            (Mode::Stop, Policy::Never, Seen::Clean),
        ]
        .into_iter()
        .map(|(mode, policy, seen)| (mode, policy, seen, restart(cut(), mode, policy, seen).1))
        .collect();
        assert_eq!(
            table,
            vec![
                (Mode::Resume, Policy::Never, Seen::Dark, Verdict::Interrupt),
                (Mode::Resume, Policy::Safe, Seen::Dark, Verdict::Launch),
                (Mode::Stop, Policy::Safe, Seen::Dark, Verdict::Interrupt),
                (Mode::Resume, Policy::Never, Seen::Landed, Verdict::Adopt),
                (Mode::Stop, Policy::Never, Seen::Landed, Verdict::Adopt),
                (Mode::Resume, Policy::Never, Seen::Clean, Verdict::Launch),
                (Mode::Stop, Policy::Never, Seen::Clean, Verdict::Abandon),
            ]
        );
    }

    /// The life after each prefix of a journal, and the verdict of a
    /// resume there: nothing before the intent, a launch before the start,
    /// an interrupt after it, settled after the end, whatever follows.
    #[test]
    fn every_prefix_of_a_journal_has_its_verdict() {
        let journal = [
            Record::Intended,
            Record::Started,
            Record::Finished,
            Record::Started,
            Record::Unknown,
        ];
        let seen: Vec<(Life, Verdict)> = (0..=journal.len())
            .map(|n| {
                restart(
                    journal[..n].iter().copied(),
                    Mode::Resume,
                    Policy::Never,
                    Seen::Dark,
                )
            })
            .collect();
        assert_eq!(
            seen,
            vec![
                (Life::Absent, Verdict::Skip),
                (Life::Pending, Verdict::Launch),
                (Life::Running { again: 0 }, Verdict::Interrupt),
                (Life::Ran, Verdict::Settled),
                (Life::Ran, Verdict::Settled),
                (Life::Ran, Verdict::Settled),
            ]
        );
    }

    /// A keyed effect whose target drops every repeat of its key is sent
    /// again while fewer than its cap, counted across restarts by the
    /// starts on record.
    #[test]
    fn a_keyed_effect_is_sent_again_up_to_its_cap() {
        let mut effect = Effect::of([Record::Intended, Record::Started]);
        let policy = Policy::Keyed {
            dedup: Dedup::Lasting,
            cap: 2,
        };
        let mut verdicts = Vec::new();
        for _ in 0..3 {
            let verdict = effect.restart(Mode::Resume, policy, Seen::Dark);
            verdicts.push((effect.life(), verdict));
            if verdict == Verdict::Launch {
                effect.record(Record::Started);
            }
        }
        assert_eq!(
            verdicts,
            vec![
                (Life::Running { again: 0 }, Verdict::Launch),
                (Life::Running { again: 1 }, Verdict::Launch),
                (Life::Running { again: 2 }, Verdict::Interrupt),
            ]
        );
    }

    /// A keyed effect whose target has no declaration is never sent
    /// again: a cut one is interrupted, whatever its cap.
    #[test]
    fn a_keyed_effect_without_a_lasting_declaration_is_sent_once() {
        let mut effect = Effect::of([Record::Intended, Record::Started]);
        let policy = Policy::Keyed {
            dedup: Dedup::Undeclared,
            cap: 5,
        };
        assert_eq!(
            effect.restart(Mode::Resume, policy, Seen::Dark),
            Verdict::Interrupt
        );
    }

    /// Keys spell the scope and the id with their lengths: gluing them
    /// differently gives another key.
    #[test]
    fn keys_of_different_effects_differ() {
        assert_eq!(key("s1", "t:9"), "2,s13,t:9");
        assert_ne!(key("ab", "c"), key("a", "bc"));
        assert_eq!(key("séance", ""), "6,séance0,");
        assert_eq!(
            key("request", "request:0123456789abcdef:12"),
            "7,request27,request:0123456789abcdef:12"
        );
    }
}
