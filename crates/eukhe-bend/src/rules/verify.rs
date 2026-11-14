//! Verified completion (`bend/verify.bend`, entry `bend/ffi_verify.bend`;
//! `laws/verify.bend`, spec `spec/verified/verify.bend`): "done" is a claim
//! the harness reports as success only when every acceptance check was
//! confirmed on the final state. Rust keeps the acceptance of a task,
//! gathers the evidence of each check and asks the compiled core for every
//! decision: the verdict of a piece of evidence ([`grade_command`],
//! [`grade_until`], [`grade_judge`]), who may change what ([`act`]), what
//! whether a final answer is a claim ([`claims`]), what the verifier does
//! next ([`advance`]), the label of the result ([`label`]) and the exit
//! code of a headless run ([`exit`]).

use crate::wire::{Reader, WireError, Writer, NAT_MAX};
use crate::{call, Entry, Error};

/// The verdict of one check on one state (`V.Verdict`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    /// The check passed.
    Confirmed,
    /// The check failed.
    Refuted,
    /// The check itself failed to judge: never read as passed or failed.
    Broken,
    /// Nothing was learned (a cancelled check).
    Unjudged,
}

impl Verdict {
    fn tag(self) -> u32 {
        match self {
            Verdict::Confirmed => 0,
            Verdict::Refuted => 1,
            Verdict::Broken => 2,
            Verdict::Unjudged => 3,
        }
    }

    fn read(reader: &mut Reader<'_>) -> Result<Self, WireError> {
        Ok(match reader.tag_of(4, "a verdict")? {
            0 => Verdict::Confirmed,
            1 => Verdict::Refuted,
            2 => Verdict::Broken,
            // `tag_of` answers a tag below 4: this is 3.
            _ => Verdict::Unjudged,
        })
    }
}

/// What the harness saw of a check's command (`V.Evidence`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Evidence {
    /// The command exited with this code.
    Exited(u64),
    /// The command ended with no exit status (a signal).
    NoStatus,
    /// The command ran past its time limit.
    TimedOut,
    /// The command could not start.
    SpawnFailed,
    /// The command was cancelled.
    Cancelled,
}

impl Evidence {
    fn write(self, request: &mut Writer) {
        match self {
            Evidence::Exited(code) => request.tag(0).nat(code.min(NAT_MAX)),
            Evidence::NoStatus => request.tag(1),
            Evidence::TimedOut => request.tag(2),
            Evidence::SpawnFailed => request.tag(3),
            Evidence::Cancelled => request.tag(4),
        };
    }
}

/// What the judge answered (`V.Answer`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Answer {
    /// An explicit yes.
    Yes,
    /// An explicit no.
    No,
    /// A reply with neither.
    Unreadable,
    /// No reply: the request failed or was refused.
    Unavailable,
    /// The request was cancelled.
    Stopped,
}

/// The slot of one check (`V.Slot`): never judged, or its last verdict and
/// the state it judged.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Slot {
    Open,
    Judged { verdict: Verdict, at: u64 },
}

impl Slot {
    fn write(self, request: &mut Writer) {
        match self {
            Slot::Open => request.tag(0),
            Slot::Judged { verdict, at } => request.tag(1).tag(verdict.tag()).nat(at.min(NAT_MAX)),
        };
    }

    fn read(reader: &mut Reader<'_>) -> Result<Self, WireError> {
        Ok(match reader.tag_of(2, "a slot")? {
            0 => Slot::Open,
            // `tag_of` answers a tag below 2: this is 1.
            _ => Slot::Judged {
                verdict: Verdict::read(reader)?,
                at: reader.nat()?,
            },
        })
    }
}

fn write_slots(request: &mut Writer, slots: &[Slot]) {
    request.count(slots.len());
    for slot in slots {
        slot.write(request);
    }
}

/// Who acts (`V.Actor`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Actor {
    /// The task's owner: the user, an SDK client, the CLI, the parent that
    /// assigned the task.
    Owner,
    /// The worker that does the task.
    Worker,
    /// The harness's verifier.
    Verifier,
}

/// An act on an acceptance (`V.Op`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Op {
    /// Set the task's checks: `checks` of them.
    Assign { checks: u64 },
    /// Claim the task done.
    Claim,
    /// Record the verdict of check `index` of revision `revision` on the
    /// state `at`.
    Record {
        revision: u64,
        index: u64,
        verdict: Verdict,
        at: u64,
    },
}

/// The acceptance of one task (`V.Acc`).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Acceptance {
    /// The revision of the checks: it grows with every Assign.
    pub revision: u64,
    /// One slot per check.
    pub slots: Vec<Slot>,
    /// A claim waits for its verdict.
    pub claimed: bool,
    /// How many times in a row a refuted claim went back to the worker.
    pub tries: u64,
}

impl Acceptance {
    fn write(&self, request: &mut Writer) {
        request.nat(self.revision.min(NAT_MAX));
        write_slots(request, &self.slots);
        request.bool(self.claimed).nat(self.tries.min(NAT_MAX));
    }

    fn read(reader: &mut Reader<'_>) -> Result<Self, WireError> {
        let revision = reader.nat()?;
        let count = reader.count()?;
        let mut slots = Vec::with_capacity(count);
        for _ in 0..count {
            slots.push(Slot::read(reader)?);
        }
        Ok(Acceptance {
            revision,
            slots,
            claimed: reader.bool()?,
            tries: reader.nat()?,
        })
    }
}

/// The label of a result (`V.Label`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Label {
    /// There is a check, every check is confirmed on the final state and
    /// programs run confined. The entry answers it for no request: no
    /// confinement exists (`V.confined`).
    Verified,
    /// A check is refuted on the final state.
    Failed,
    /// Neither: no checks, or a check that did not judge the final state,
    /// is broken or unjudged.
    Unverified,
    /// There is a check and every check is confirmed on the final state;
    /// programs run unconfined: checks passed, unconfined.
    Passed,
}

impl Label {
    fn read(reader: &mut Reader<'_>) -> Result<Self, WireError> {
        Ok(match reader.tag_of(4, "a label")? {
            0 => Label::Verified,
            1 => Label::Failed,
            2 => Label::Unverified,
            // `tag_of` answers a tag below 4: this is 3.
            _ => Label::Passed,
        })
    }
}

/// What the verifier does next (`V.Action`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Action {
    /// No claim waits.
    Rest,
    /// Run the check at `index` and record its verdict.
    Run { index: u64 },
    /// Give the evidence back to the worker.
    Return,
    /// End the claim with this label.
    End(Label),
}

/// One request of the entry: its reply, read whole by `read`.
fn ask<T>(
    request: &mut Writer,
    read: impl FnOnce(&mut Reader<'_>) -> Result<T, WireError>,
) -> Result<T, Error> {
    let reply = call(Entry::Verify, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let value = read(&mut reader)?;
    reader.end()?;
    Ok(value)
}

/// The verdict of a command check: `expect` is the exit code its owner
/// expects, `intact` whether every file the check protects is as the
/// owner left it.
///
/// # Errors
///
/// A compiled-core failure or a malformed reply (an inconsistent build).
pub fn grade_command(expect: u64, intact: bool, evidence: Evidence) -> Result<Verdict, Error> {
    let mut request = Writer::new();
    request.tag(4).nat(expect.min(NAT_MAX)).bool(intact);
    evidence.write(&mut request);
    ask(&mut request, Verdict::read)
}

/// The verdict of a loop's until-condition.
///
/// # Errors
///
/// A compiled-core failure or a malformed reply (an inconsistent build).
pub fn grade_until(evidence: Evidence) -> Result<Verdict, Error> {
    let mut request = Writer::new();
    request.tag(5);
    evidence.write(&mut request);
    ask(&mut request, Verdict::read)
}

/// The verdict of a judge's answer.
///
/// # Errors
///
/// A compiled-core failure or a malformed reply (an inconsistent build).
pub fn grade_judge(answer: Answer) -> Result<Verdict, Error> {
    let tag = match answer {
        Answer::Yes => 0,
        Answer::No => 1,
        Answer::Unreadable => 2,
        Answer::Unavailable => 3,
        Answer::Stopped => 4,
    };
    let mut request = Writer::new();
    request.tag(6).tag(tag);
    ask(&mut request, Verdict::read)
}

/// One act of `who` on `acceptance`: whether it is admitted, and the
/// acceptance after it (`acceptance` itself when refused).
///
/// # Errors
///
/// A compiled-core failure or a malformed reply (an inconsistent build).
pub fn act(who: Actor, op: Op, acceptance: &Acceptance) -> Result<(bool, Acceptance), Error> {
    let who = match who {
        Actor::Owner => 0,
        Actor::Worker => 1,
        Actor::Verifier => 2,
    };
    let mut request = Writer::new();
    request.tag(0).tag(who);
    match op {
        Op::Assign { checks } => request.tag(0).nat(checks.min(NAT_MAX)),
        Op::Claim => request.tag(1),
        Op::Record {
            revision,
            index,
            verdict,
            at,
        } => request
            .tag(2)
            .nat(revision.min(NAT_MAX))
            .nat(index.min(NAT_MAX))
            .tag(verdict.tag())
            .nat(at.min(NAT_MAX)),
    };
    acceptance.write(&mut request);
    ask(&mut request, |reader| {
        Ok((reader.bool()?, Acceptance::read(reader)?))
    })
}

/// One step of the verifier on the state `now`, with at most `cap`
/// returns to the worker in a row: what it does, and the acceptance after
/// the step.
///
/// # Errors
///
/// A compiled-core failure or a malformed reply (an inconsistent build).
pub fn advance(now: u64, cap: u64, acceptance: &Acceptance) -> Result<(Action, Acceptance), Error> {
    let mut request = Writer::new();
    request.tag(1).nat(now.min(NAT_MAX)).nat(cap.min(NAT_MAX));
    acceptance.write(&mut request);
    ask(&mut request, |reader| {
        let action = match reader.tag_of(4, "a verifier action")? {
            0 => Action::Rest,
            1 => Action::Run {
                index: reader.nat()?,
            },
            2 => Action::Return,
            // `tag_of` answers a tag below 4: this is 3.
            _ => Action::End(Label::read(reader)?),
        };
        Ok((action, Acceptance::read(reader)?))
    })
}

/// The facts of one final answer, for [`claims`].
// Each flag is an independent fact the rule reads.
#[allow(clippy::struct_excessive_bools)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AnswerFacts {
    /// Queued input or running work owns the next boundary.
    pub held: bool,
    /// The task has a check.
    pub checked: bool,
    /// An active goal drives the run: it claims with `goal.complete()`.
    pub goal: bool,
    /// A claim already waits for its verdict.
    pub claimed: bool,
    /// The last claim ended on the state now.
    pub ended: bool,
}

/// Whether the verifier judges a claim at a final answer.
///
/// # Errors
///
/// A compiled-core failure or a malformed reply (an inconsistent build).
pub fn claims(facts: AnswerFacts) -> Result<bool, Error> {
    let mut request = Writer::new();
    request
        .tag(7)
        .bool(facts.held)
        .bool(facts.checked)
        .bool(facts.goal)
        .bool(facts.claimed)
        .bool(facts.ended);
    // `Reader::bool` is fixed to one reader lifetime; `ask` needs a reader
    // of any lifetime, which only a closure gives.
    #[allow(clippy::redundant_closure_for_method_calls)]
    ask(&mut request, |reader| reader.bool())
}

/// The label of the result on the state `now`.
///
/// # Errors
///
/// A compiled-core failure or a malformed reply (an inconsistent build).
pub fn label(now: u64, slots: &[Slot]) -> Result<Label, Error> {
    let mut request = Writer::new();
    request.tag(2).nat(now.min(NAT_MAX));
    write_slots(&mut request, slots);
    ask(&mut request, Label::read)
}

/// The exit code of a headless run whose own code is `base`: `base` when
/// every check is confirmed on the state `now` (also with no checks), else
/// nonzero.
///
/// # Errors
///
/// A compiled-core failure or a malformed reply (an inconsistent build).
pub fn exit(base: u64, now: u64, slots: &[Slot]) -> Result<u64, Error> {
    let mut request = Writer::new();
    request.tag(3).nat(base.min(NAT_MAX)).nat(now.min(NAT_MAX));
    write_slots(&mut request, slots);
    // `Reader::nat` is fixed to one reader lifetime (see `claims`).
    #[allow(clippy::redundant_closure_for_method_calls)]
    ask(&mut request, |reader| reader.nat())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn confirmed(at: u64) -> Slot {
        Slot::Judged {
            verdict: Verdict::Confirmed,
            at,
        }
    }

    /// A claim runs through the compiled core: the owner's checks, the
    /// worker's refused acts, the verifier's records, the end.
    #[test]
    fn a_claim_is_verified_only_by_the_verifiers_records_on_the_final_state() {
        let empty = Acceptance::default();
        let (admitted, set) = act(Actor::Owner, Op::Assign { checks: 2 }, &empty).expect("assign");
        assert!(admitted);
        assert_eq!(
            set,
            Acceptance {
                revision: 1,
                slots: vec![Slot::Open, Slot::Open],
                claimed: false,
                tries: 0,
            }
        );
        // The worker cannot drop its checks nor record a verdict.
        assert_eq!(
            act(Actor::Worker, Op::Assign { checks: 0 }, &set).expect("assign"),
            (false, set.clone())
        );
        let record = |index, verdict, at| Op::Record {
            revision: 1,
            index,
            verdict,
            at,
        };
        assert_eq!(
            act(Actor::Worker, record(0, Verdict::Confirmed, 7), &set).expect("record"),
            (false, set.clone())
        );
        let (_, claimed) = act(Actor::Worker, Op::Claim, &set).expect("claim");
        assert_eq!(
            advance(7, 3, &claimed).expect("advance").0,
            Action::Run { index: 0 }
        );
        let (_, first) =
            act(Actor::Verifier, record(0, Verdict::Confirmed, 7), &claimed).expect("record");
        assert_eq!(
            advance(7, 3, &first).expect("advance").0,
            Action::Run { index: 1 }
        );
        let (_, both) =
            act(Actor::Verifier, record(1, Verdict::Confirmed, 7), &first).expect("record");
        let (action, ended) = advance(7, 3, &both).expect("advance");
        // Programs run unconfined: every check confirmed is "checks
        // passed, unconfined", never verified.
        assert_eq!(action, Action::End(Label::Passed));
        assert_eq!(
            ended,
            Acceptance {
                revision: 1,
                slots: vec![confirmed(7), confirmed(7)],
                claimed: false,
                tries: 0,
            }
        );
        // The worker's next effect makes the verdicts stale.
        assert_eq!(label(7, &ended.slots).expect("label"), Label::Passed);
        assert_eq!(label(8, &ended.slots).expect("label"), Label::Unverified);
        assert_eq!(exit(0, 7, &ended.slots).expect("exit"), 0);
        assert_eq!(exit(0, 8, &ended.slots).expect("exit"), 1);
        assert_eq!(exit(0, 8, &[]).expect("exit"), 0);
    }

    /// A refuted claim goes back to the worker up to the cap, then ends
    /// failed.
    #[test]
    fn a_refuted_claim_returns_then_ends_failed() {
        let refuted = Acceptance {
            revision: 1,
            slots: vec![Slot::Judged {
                verdict: Verdict::Refuted,
                at: 4,
            }],
            claimed: true,
            tries: 0,
        };
        let (action, back) = advance(4, 1, &refuted).expect("advance");
        assert_eq!(action, Action::Return);
        assert_eq!(
            back,
            Acceptance {
                claimed: false,
                tries: 1,
                ..refuted.clone()
            }
        );
        let (_, again) = act(Actor::Worker, Op::Claim, &back).expect("claim");
        let (action, ended) = advance(4, 1, &again).expect("advance");
        assert_eq!(action, Action::End(Label::Failed));
        assert_eq!(
            ended,
            Acceptance {
                claimed: false,
                tries: 0,
                ..refuted
            }
        );
    }

    /// Whether a final answer is a claim comes from the compiled core.
    #[test]
    fn the_core_says_when_an_answer_is_a_claim() {
        let plain = AnswerFacts {
            held: false,
            checked: true,
            goal: false,
            claimed: false,
            ended: false,
        };
        assert_eq!(
            [
                claims(plain),
                claims(AnswerFacts {
                    held: true,
                    ..plain
                }),
                claims(AnswerFacts {
                    checked: false,
                    ..plain
                }),
                claims(AnswerFacts {
                    goal: true,
                    ..plain
                }),
                claims(AnswerFacts {
                    ended: true,
                    ..plain
                }),
                claims(AnswerFacts {
                    goal: true,
                    claimed: true,
                    ended: true,
                    ..plain
                }),
                claims(AnswerFacts {
                    held: true,
                    claimed: true,
                    ..plain
                }),
            ]
            .map(|claim| claim.expect("a decision")),
            [true, false, false, false, false, true, false]
        );
    }

    /// The verdicts of evidence come from the compiled core.
    #[test]
    fn the_core_grades_the_evidence() {
        assert_eq!(
            [
                grade_command(0, true, Evidence::Exited(0)),
                grade_command(0, true, Evidence::Exited(101)),
                grade_command(3, true, Evidence::Exited(3)),
                grade_command(0, false, Evidence::Exited(0)),
                grade_command(0, true, Evidence::TimedOut),
                grade_command(0, true, Evidence::SpawnFailed),
                grade_command(0, true, Evidence::NoStatus),
                grade_command(0, true, Evidence::Cancelled),
                grade_until(Evidence::Exited(0)),
                grade_until(Evidence::Exited(1)),
                grade_until(Evidence::Exited(2)),
                grade_judge(Answer::Yes),
                grade_judge(Answer::No),
                grade_judge(Answer::Unreadable),
                grade_judge(Answer::Unavailable),
                grade_judge(Answer::Stopped),
            ]
            .map(|verdict| verdict.expect("a verdict")),
            [
                Verdict::Confirmed,
                Verdict::Refuted,
                Verdict::Confirmed,
                Verdict::Refuted,
                Verdict::Broken,
                Verdict::Broken,
                Verdict::Broken,
                Verdict::Unjudged,
                Verdict::Confirmed,
                Verdict::Refuted,
                Verdict::Broken,
                Verdict::Confirmed,
                Verdict::Refuted,
                Verdict::Broken,
                Verdict::Broken,
                Verdict::Unjudged,
            ]
        );
    }
}
