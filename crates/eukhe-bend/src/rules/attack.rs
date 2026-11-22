//! Blind attackers on the acceptance checks (`bend/attack.bend`, entry
//! `bend/ffi_attack.bend`; `laws/attack.bend`, spec
//! `spec/verified/attack.bend`): fresh attackers write wrong code for the
//! task with a witness; a survivor counts like a break that got through.
//! Rust asks the attackers and runs their attacks in scratch copies, and
//! asks the compiled core for every decision: the outcome of one attack
//! ([`outcome`]), the label ([`label`]) and the exit code of a headless run
//! ([`exit`]), which replace `strength`'s and equal them with no attack.

use super::strength::{Gauge, Label};
use super::verify::{write_slots, Label as VerifyLabel, Slot};
use crate::wire::{Reader, WireError, Writer, NAT_MAX};
use crate::{call, Entry, Error};

/// How one attack ended (`At.Outcome`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    /// The checks let the wrong code through.
    Survived,
    /// The checks, the witness or the judge stopped it.
    Clean,
    /// It did not run.
    Unrun,
}

impl Outcome {
    fn tag(self) -> u32 {
        match self {
            Outcome::Survived => 0,
            Outcome::Clean => 1,
            Outcome::Unrun => 2,
        }
    }
}

/// What running one attack showed (`At.Run`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Run {
    /// It ran at all.
    pub ran: bool,
    /// Its wrong code passed every gauged check.
    pub passes: bool,
    /// The witness's output on it differs from the required output.
    pub differs: bool,
    /// The judge's verdict on the required output; `None`: no verdict.
    pub agrees: Option<bool>,
}

fn write_gauges(request: &mut Writer, gauges: &[Gauge]) {
    request.count(gauges.len());
    for gauge in gauges {
        gauge.write(request);
    }
}

fn write_outcomes(request: &mut Writer, outcomes: &[Outcome]) {
    request.count(outcomes.len());
    for outcome in outcomes {
        request.tag(outcome.tag());
    }
}

fn verify_label_tag(label: VerifyLabel) -> u32 {
    match label {
        VerifyLabel::Verified => 0,
        VerifyLabel::Failed => 1,
        VerifyLabel::Unverified => 2,
        VerifyLabel::Passed => 3,
    }
}

/// One request of the entry: its reply, read whole by `read`.
fn ask<T>(
    request: &mut Writer,
    read: impl FnOnce(&mut Reader<'_>) -> Result<T, WireError>,
) -> Result<T, Error> {
    let reply = call(Entry::Attack, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let value = read(&mut reader)?;
    reader.end()?;
    Ok(value)
}

/// How an attack that showed `run` ended.
///
/// # Errors
///
/// A compiled-core failure or a malformed reply (an inconsistent build).
pub fn outcome(run: Run) -> Result<Outcome, Error> {
    let mut request = Writer::new();
    request
        .tag(0)
        .bool(run.ran)
        .bool(run.passes)
        .bool(run.differs);
    match run.agrees {
        None => request.tag(0),
        Some(yes) => request.tag(1).bool(yes),
    };
    ask(&mut request, |reader| {
        Ok(match reader.tag_of(3, "an attack outcome")? {
            0 => Outcome::Survived,
            1 => Outcome::Clean,
            // `tag_of` answers a tag below 3: this is 2.
            _ => Outcome::Unrun,
        })
    })
}

/// The label of a result whose verify label is `label` on the state `now`,
/// with the outcomes of the attacks made on `now`.
///
/// # Errors
///
/// A compiled-core failure or a malformed reply (an inconsistent build).
pub fn label(
    label: VerifyLabel,
    now: u64,
    gauges: &[Gauge],
    outcomes: &[Outcome],
) -> Result<Label, Error> {
    let mut request = Writer::new();
    request
        .tag(1)
        .tag(verify_label_tag(label))
        .nat(now.min(NAT_MAX));
    write_gauges(&mut request, gauges);
    write_outcomes(&mut request, outcomes);
    ask(&mut request, Label::read)
}

/// The exit code of a headless run whose own code is `base`, with the
/// outcomes of the attacks made on `now`.
///
/// # Errors
///
/// A compiled-core failure or a malformed reply (an inconsistent build).
pub fn exit(
    base: u64,
    now: u64,
    slots: &[Slot],
    gauges: &[Gauge],
    outcomes: &[Outcome],
) -> Result<u64, Error> {
    let mut request = Writer::new();
    request.tag(2).nat(base.min(NAT_MAX)).nat(now.min(NAT_MAX));
    write_slots(&mut request, slots);
    write_gauges(&mut request, gauges);
    write_outcomes(&mut request, outcomes);
    // `Reader::nat` is fixed to one reader lifetime (see `verify::claims`).
    #[allow(clippy::redundant_closure_for_method_calls)]
    ask(&mut request, |reader| reader.nat())
}

#[cfg(test)]
mod tests {
    use super::super::strength::{Bar, Mark};
    use super::super::verify::Verdict;
    use super::*;

    fn strong(now: u64) -> Gauge {
        Gauge {
            bar: Bar::Needs { pct: 80 },
            mark: Mark::Measured {
                caught: 4,
                ran: 4,
                planned: 4,
                at: now,
            },
        }
    }

    const JUDGE: Gauge = Gauge {
        bar: Bar::Exempt,
        mark: Mark::Unmeasured,
    };

    #[test]
    fn an_attack_survives_only_when_it_passed_showed_wrong_and_the_judge_agreed() {
        let run = |ran, passes, differs, agrees| {
            outcome(Run {
                ran,
                passes,
                differs,
                agrees,
            })
            .expect("the core answers")
        };
        assert_eq!(run(true, true, true, Some(true)), Outcome::Survived);
        assert_eq!(run(true, false, true, Some(true)), Outcome::Clean);
        assert_eq!(run(true, true, false, Some(true)), Outcome::Clean);
        assert_eq!(run(true, true, true, Some(false)), Outcome::Clean);
        assert_eq!(run(true, true, true, None), Outcome::Unrun);
        assert_eq!(run(false, true, true, Some(true)), Outcome::Unrun);
    }

    #[test]
    fn a_survivor_takes_done_away_and_two_clean_attacks_certify_judges() {
        let now = 7;
        let passed = VerifyLabel::Passed;
        assert_eq!(
            label(passed, now, &[strong(now)], &[]).unwrap(),
            Label::Passed
        );
        assert_eq!(
            label(
                passed,
                now,
                &[strong(now)],
                &[Outcome::Clean, Outcome::Survived]
            )
            .unwrap(),
            Label::Uncertified
        );
        assert_eq!(
            label(passed, now, &[JUDGE], &[Outcome::Clean]).unwrap(),
            Label::Uncertified
        );
        assert_eq!(
            label(
                passed,
                now,
                &[JUDGE],
                &[Outcome::Clean, Outcome::Unrun, Outcome::Clean]
            )
            .unwrap(),
            Label::Passed
        );
        let slots = [Slot::Judged {
            verdict: Verdict::Confirmed,
            at: now,
        }];
        assert_eq!(exit(0, now, &slots, &[strong(now)], &[]).unwrap(), 0);
        assert_eq!(
            exit(0, now, &slots, &[strong(now)], &[Outcome::Survived]).unwrap(),
            3
        );
        assert_eq!(
            exit(1, now, &slots, &[strong(now)], &[Outcome::Survived]).unwrap(),
            1
        );
    }
}
