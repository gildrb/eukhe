//! The strength of the acceptance checks (`bend/strength.bend`, entry
//! `bend/ffi_strength.bend`; `laws/strength.bend`, spec
//! `spec/verified/strength.bend`): a check certifies done only when it was
//! shown to catch broken code. Rust breaks the code the task changed in a
//! scratch copy (mutants), runs each gauged check on the broken copies and
//! asks the compiled core for every decision: the strength of a check
//! ([`strength`]), the verifier's step after verify ended a claim
//! ([`settle`]), the label ([`label`]), who records a mark ([`record`]) and
//! the exit code of a headless run ([`exit`]).

use super::verify::{write_slots, Actor, Label as VerifyLabel, Slot};
use crate::wire::{Reader, WireError, Writer, NAT_MAX};
use crate::{call, Entry, Error};

/// What the owner asks of a check (`St.Bar`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Bar {
    /// A judge or the intent check: no code to break for it.
    Exempt,
    /// The owner waived the check's strength (`--strength 0`).
    Waived,
    /// The check must catch at least `pct` percent of the breaks.
    Needs { pct: u64 },
}

/// What the verifier measured for a check (`St.Mark`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mark {
    Unmeasured,
    /// The breaks caught, run and planned on the state `at`.
    Measured {
        caught: u64,
        ran: u64,
        planned: u64,
        at: u64,
    },
}

/// One check: the owner's bar and the verifier's mark (`St.Gauge`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Gauge {
    pub bar: Bar,
    pub mark: Mark,
}

impl Mark {
    fn write(self, request: &mut Writer) {
        match self {
            Mark::Unmeasured => request.tag(0),
            Mark::Measured {
                caught,
                ran,
                planned,
                at,
            } => request
                .tag(1)
                .nat(caught.min(NAT_MAX))
                .nat(ran.min(NAT_MAX))
                .nat(planned.min(NAT_MAX))
                .nat(at.min(NAT_MAX)),
        };
    }
}

impl Gauge {
    fn write(self, request: &mut Writer) {
        match self.bar {
            Bar::Exempt => request.tag(0),
            Bar::Waived => request.tag(1),
            Bar::Needs { pct } => request.tag(2).nat(pct.min(NAT_MAX)),
        };
        self.mark.write(request);
    }

    fn read(reader: &mut Reader<'_>) -> Result<Self, WireError> {
        let bar = match reader.tag_of(3, "a bar")? {
            0 => Bar::Exempt,
            1 => Bar::Waived,
            // `tag_of` answers a tag below 3: this is 2.
            _ => Bar::Needs { pct: reader.nat()? },
        };
        let mark = match reader.tag_of(2, "a mark")? {
            0 => Mark::Unmeasured,
            // `tag_of` answers a tag below 2: this is 1.
            _ => Mark::Measured {
                caught: reader.nat()?,
                ran: reader.nat()?,
                planned: reader.nat()?,
                at: reader.nat()?,
            },
        };
        Ok(Gauge { bar, mark })
    }
}

fn write_gauges(request: &mut Writer, gauges: &[Gauge]) {
    request.count(gauges.len());
    for gauge in gauges {
        gauge.write(request);
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

/// The strength of a check on a state (`St.Strength`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Strength {
    /// Shown to catch at least the owner's share of the breaks.
    Strong,
    /// It caught less, or there was nothing to break.
    Weak,
    /// Not measured on this state, or the measurement was cut short.
    Unshown,
    /// Exempt or waived.
    Free,
}

/// The label of a result (`St.Label`): verify's four, and not certified.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Label {
    Verified,
    Failed,
    Unverified,
    /// Checks passed, unconfined; done certified.
    Passed,
    /// Every check confirmed, but not shown to catch broken code.
    Uncertified,
}

impl Label {
    fn read(reader: &mut Reader<'_>) -> Result<Self, WireError> {
        Ok(match reader.tag_of(5, "a label")? {
            0 => Label::Verified,
            1 => Label::Failed,
            2 => Label::Unverified,
            3 => Label::Passed,
            // `tag_of` answers a tag below 5: this is 4.
            _ => Label::Uncertified,
        })
    }
}

/// The verifier's step after verify ended a claim (`St.Step`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Step {
    /// Break the code and run the check at `index` on the broken copies.
    Measure { index: u64 },
    /// End the claim with this label.
    End(Label),
}

/// One request of the entry: its reply, read whole by `read`.
fn ask<T>(
    request: &mut Writer,
    read: impl FnOnce(&mut Reader<'_>) -> Result<T, WireError>,
) -> Result<T, Error> {
    let reply = call(Entry::Strength, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let value = read(&mut reader)?;
    reader.end()?;
    Ok(value)
}

/// The verifier's step after verify ended a claim with `ended` on the
/// state `now`: measure the next gauged check with no mark on `now`, or
/// end the claim with the label.
///
/// # Errors
///
/// A compiled-core failure or a malformed reply (an inconsistent build).
pub fn settle(ended: VerifyLabel, now: u64, gauges: &[Gauge]) -> Result<Step, Error> {
    let mut request = Writer::new();
    request
        .tag(0)
        .tag(verify_label_tag(ended))
        .nat(now.min(NAT_MAX));
    write_gauges(&mut request, gauges);
    ask(&mut request, |reader| {
        Ok(match reader.tag_of(2, "a strength step")? {
            0 => Step::Measure {
                index: reader.nat()?,
            },
            // `tag_of` answers a tag below 2: this is 1.
            _ => Step::End(Label::read(reader)?),
        })
    })
}

/// The label of a result whose verify label is `label` on the state `now`.
///
/// # Errors
///
/// A compiled-core failure or a malformed reply (an inconsistent build).
pub fn label(label: VerifyLabel, now: u64, gauges: &[Gauge]) -> Result<Label, Error> {
    let mut request = Writer::new();
    request
        .tag(1)
        .tag(verify_label_tag(label))
        .nat(now.min(NAT_MAX));
    write_gauges(&mut request, gauges);
    ask(&mut request, Label::read)
}

/// The exit code of a headless run whose own code is `base`: verify's, and
/// 3 instead of 0 when every check (one or more) is confirmed on `now`
/// but done is not certified.
///
/// # Errors
///
/// A compiled-core failure or a malformed reply (an inconsistent build).
pub fn exit(base: u64, now: u64, slots: &[Slot], gauges: &[Gauge]) -> Result<u64, Error> {
    let mut request = Writer::new();
    request.tag(2).nat(base.min(NAT_MAX)).nat(now.min(NAT_MAX));
    write_slots(&mut request, slots);
    write_gauges(&mut request, gauges);
    // `Reader::nat` is fixed to one reader lifetime (see `verify::claims`).
    #[allow(clippy::redundant_closure_for_method_calls)]
    ask(&mut request, |reader| reader.nat())
}

/// Record `mark` for check `index` as `who`: whether it is admitted (only
/// the verifier, only for a check that exists), and the gauges after it.
///
/// # Errors
///
/// A compiled-core failure or a malformed reply (an inconsistent build).
pub fn record(
    who: Actor,
    index: u64,
    mark: Mark,
    gauges: &[Gauge],
) -> Result<(bool, Vec<Gauge>), Error> {
    let mut request = Writer::new();
    request.tag(3).tag(who.tag()).nat(index.min(NAT_MAX));
    mark.write(&mut request);
    write_gauges(&mut request, gauges);
    ask(&mut request, |reader| {
        let admitted = reader.bool()?;
        let count = reader.count()?;
        let mut after = Vec::with_capacity(count);
        for _ in 0..count {
            after.push(Gauge::read(reader)?);
        }
        Ok((admitted, after))
    })
}

/// The strength of `gauge` on the state `now`.
///
/// # Errors
///
/// A compiled-core failure or a malformed reply (an inconsistent build).
pub fn strength(now: u64, gauge: Gauge) -> Result<Strength, Error> {
    let mut request = Writer::new();
    request.tag(4).nat(now.min(NAT_MAX));
    gauge.write(&mut request);
    ask(&mut request, |reader| {
        Ok(match reader.tag_of(4, "a strength")? {
            0 => Strength::Strong,
            1 => Strength::Weak,
            2 => Strength::Unshown,
            // `tag_of` answers a tag below 4: this is 3.
            _ => Strength::Free,
        })
    })
}

#[cfg(test)]
mod tests {
    use super::super::verify::Verdict;
    use super::*;

    fn needs(mark: Mark) -> Gauge {
        Gauge {
            bar: Bar::Needs { pct: 80 },
            mark,
        }
    }

    fn measured(caught: u64, ran: u64, at: u64) -> Mark {
        Mark::Measured {
            caught,
            ran,
            planned: ran,
            at,
        }
    }

    const JUDGE: Gauge = Gauge {
        bar: Bar::Exempt,
        mark: Mark::Unmeasured,
    };

    /// A passed claim measures its gauged checks through the compiled core,
    /// then ends certified only when they caught their share of the breaks.
    #[test]
    fn a_passed_claim_is_done_only_when_its_checks_caught_the_breaks() {
        let open = [JUDGE, needs(Mark::Unmeasured)];
        assert_eq!(
            settle(VerifyLabel::Passed, 7, &open).expect("settle"),
            Step::Measure { index: 1 }
        );
        // The worker records nothing.
        assert_eq!(
            record(Actor::Worker, 1, measured(24, 24, 7), &open).expect("record"),
            (false, open.to_vec())
        );
        let (admitted, strong) =
            record(Actor::Verifier, 1, measured(23, 24, 7), &open).expect("record");
        assert!(admitted);
        assert_eq!(
            settle(VerifyLabel::Passed, 7, &strong).expect("settle"),
            Step::End(Label::Passed)
        );
        let weak = [JUDGE, needs(measured(0, 12, 7))];
        assert_eq!(
            [
                settle(VerifyLabel::Passed, 7, &weak).expect("settle"),
                settle(VerifyLabel::Failed, 7, &open).expect("settle"),
                settle(VerifyLabel::Passed, 7, &[JUDGE]).expect("settle"),
            ],
            [
                Step::End(Label::Uncertified),
                Step::End(Label::Failed),
                Step::End(Label::Uncertified),
            ]
        );
        assert_eq!(
            [
                strength(7, needs(measured(23, 24, 7))).expect("strength"),
                strength(7, needs(measured(0, 12, 7))).expect("strength"),
                strength(8, needs(measured(24, 24, 7))).expect("strength"),
                strength(7, JUDGE).expect("strength"),
            ],
            [
                Strength::Strong,
                Strength::Weak,
                Strength::Unshown,
                Strength::Free
            ]
        );
        assert_eq!(
            label(VerifyLabel::Passed, 7, &weak).expect("label"),
            Label::Uncertified
        );
    }

    /// A run whose checks passed without being shown to catch broken code
    /// exits 3; certified it keeps its code; a failure keeps its own.
    #[test]
    fn an_uncertified_run_exits_three() {
        let confirmed = [Slot::Judged {
            verdict: Verdict::Confirmed,
            at: 7,
        }];
        assert_eq!(
            [
                exit(0, 7, &confirmed, &[needs(measured(0, 12, 7))]).expect("exit"),
                exit(0, 7, &confirmed, &[needs(measured(23, 24, 7))]).expect("exit"),
                exit(0, 7, &[], &[]).expect("exit"),
                exit(2, 7, &confirmed, &[needs(measured(0, 12, 7))]).expect("exit"),
            ],
            [3, 0, 0, 2]
        );
    }
}
