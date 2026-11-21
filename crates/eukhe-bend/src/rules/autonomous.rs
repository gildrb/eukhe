//! What an autonomous run does at a final answer: the compiled core's rule
//! (`bend/autonomous.bend`, entry `bend/ffi_autonomous.bend`, laws
//! `laws/autonomous.bend`). The run goes on until its checks end the claim
//! or its budget admits no more work; it has no limit of its own. A claim
//! that passed does not end a run whose final answer states work left (the
//! final-answer judge's [`Reading`]).

use crate::rules::verify::Label;
use crate::rules::work_left::Reading;
use crate::wire::{Reader, WireError, Writer};
use crate::{call, Entry, Error};

/// Whether the run is autonomous.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    /// The principal set the run to go on without a human.
    Autonomous,
    /// A run that ends at its final answer.
    Attended,
}

/// How the final answer ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Answer {
    /// A stop, a length cut, a tool use.
    Settled,
    /// An error or an abort.
    Broken,
}

/// The run's checks at this answer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Checks {
    /// The run has no check.
    Unchecked,
    /// The claim went back to the worker with its evidence.
    Returned,
    /// The claim ended with this label.
    Ended(Label),
}

/// Whether the run's budget admits work.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Budget {
    /// It admits work (no budget, or one in its working phase).
    Working,
    /// It admits no more work (wrap-up, exhausted).
    Short,
}

/// The facts of one final answer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Facts {
    pub mode: Mode,
    pub answer: Answer,
    pub checks: Checks,
    pub budget: Budget,
    /// The final-answer judge's reading of the answer.
    pub reading: Reading,
}

/// Why an autonomous run stopped.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Cause {
    /// The checks ended the claim with this label.
    Checks(Label),
    /// The budget admits no more work.
    Budget,
}

/// What the run does at the answer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Step {
    /// Nothing: the run is not autonomous, or the answer broke.
    Off,
    /// The checks' return continues the run; it adds nothing.
    Hold,
    /// Continue the run with its continuation prompt.
    Continue,
    /// Stop the run.
    Stop(Cause),
    /// The claim passed and the budget admits work: ask the final-answer
    /// judge for its reading, then decide again with it.
    Ask,
    /// The claim passed but the answer states work left: go on with the
    /// work the answer left.
    Finish,
}

fn label_tag(label: Label) -> u32 {
    match label {
        Label::Verified => 0,
        Label::Failed => 1,
        Label::Unverified => 2,
        Label::Passed => 3,
    }
}

fn read_label(reader: &mut Reader<'_>) -> Result<Label, WireError> {
    Ok(match reader.tag_of(4, "a label")? {
        0 => Label::Verified,
        1 => Label::Failed,
        2 => Label::Unverified,
        // `tag_of` answers a tag below 4: this is 3.
        _ => Label::Passed,
    })
}

fn write_facts(facts: Facts, request: &mut Writer) {
    request
        .bool(match facts.mode {
            Mode::Autonomous => true,
            Mode::Attended => false,
        })
        .tag(match facts.answer {
            Answer::Settled => 0,
            Answer::Broken => 1,
        });
    match facts.checks {
        Checks::Unchecked => {
            request.tag(0);
        }
        Checks::Returned => {
            request.tag(1);
        }
        Checks::Ended(label) => {
            request.tag(2).tag(label_tag(label));
        }
    }
    request
        .tag(match facts.budget {
            Budget::Working => 0,
            Budget::Short => 1,
        })
        .tag(facts.reading.tag());
}

/// The step of an autonomous run at a final answer with `facts`.
///
/// # Errors
///
/// A compiled-core failure or a malformed reply (an inconsistent build).
pub fn step(facts: Facts) -> Result<Step, Error> {
    let mut request = Writer::new();
    write_facts(facts, &mut request);
    let reply = call(Entry::Autonomous, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let step = match reader.tag_of(6, "a step")? {
        0 => Step::Off,
        1 => Step::Hold,
        2 => Step::Continue,
        3 => Step::Stop(match reader.tag_of(2, "a stop cause")? {
            0 => Cause::Checks(read_label(&mut reader)?),
            // `tag_of` answers a tag below 2: this is 1.
            _ => Cause::Budget,
        }),
        4 => Step::Ask,
        // `tag_of` answers a tag below 6: this is 5.
        _ => Step::Finish,
    };
    reader.end()?;
    Ok(step)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn facts(checks: Checks, budget: Budget, reading: Reading) -> Facts {
        Facts {
            mode: Mode::Autonomous,
            answer: Answer::Settled,
            checks,
            budget,
            reading,
        }
    }

    /// Every spelling Rust writes reads back as the core's step.
    #[test]
    fn the_core_answers_each_step() {
        let cases = [
            (
                facts(Checks::Unchecked, Budget::Working, Reading::Unread),
                Step::Continue,
            ),
            (
                facts(Checks::Returned, Budget::Working, Reading::Unread),
                Step::Hold,
            ),
            (
                facts(Checks::Ended(Label::Passed), Budget::Short, Reading::Left),
                Step::Stop(Cause::Checks(Label::Passed)),
            ),
            (
                facts(Checks::Ended(Label::Failed), Budget::Working, Reading::Left),
                Step::Stop(Cause::Checks(Label::Failed)),
            ),
            (
                facts(Checks::Unchecked, Budget::Short, Reading::Unread),
                Step::Stop(Cause::Budget),
            ),
            (
                Facts {
                    answer: Answer::Broken,
                    ..facts(Checks::Unchecked, Budget::Working, Reading::Unread)
                },
                Step::Off,
            ),
            (
                Facts {
                    mode: Mode::Attended,
                    ..facts(Checks::Unchecked, Budget::Working, Reading::Unread)
                },
                Step::Off,
            ),
            (
                facts(
                    Checks::Ended(Label::Passed),
                    Budget::Working,
                    Reading::Unread,
                ),
                Step::Ask,
            ),
            (
                facts(
                    Checks::Ended(Label::Verified),
                    Budget::Working,
                    Reading::Left,
                ),
                Step::Finish,
            ),
            (
                facts(
                    Checks::Ended(Label::Passed),
                    Budget::Working,
                    Reading::Finished,
                ),
                Step::Stop(Cause::Checks(Label::Passed)),
            ),
            (
                facts(
                    Checks::Ended(Label::Verified),
                    Budget::Working,
                    Reading::Unjudged,
                ),
                Step::Stop(Cause::Checks(Label::Verified)),
            ),
        ];
        let got: Vec<Step> = cases.iter().map(|(f, _)| step(*f).unwrap()).collect();
        let want: Vec<Step> = cases.iter().map(|(_, s)| *s).collect();
        assert_eq!(got, want);
    }
}
