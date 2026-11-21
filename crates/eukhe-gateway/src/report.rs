//! What the Signal peer that holds the floor hears of a run: one report
//! when the run ends, nothing while it runs. The compiled Bend core
//! decides (`bend/gateway_report.bend`, entry
//! `bend/ffi_gateway_report.bend`, laws `laws/gateway_report.bend`); this
//! file writes what the gateway held, the event's answer and the run end,
//! and reads what to hold and what to send.

use eukhe_bend::wire::{Reader, WireError, Writer};
use eukhe_bend::{call, expect_core, Entry, Error};

use crate::answer::Answer;

/// Whether work a run started still runs when the run ends.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Work {
    /// A job, a subagent or a workflow run still runs: its end wakes the
    /// session again.
    Running,
    /// Nothing the run started still runs.
    Settled,
}

/// Whether a session event ends the run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum End {
    /// The event ends no run.
    No,
    /// The run ended: whether work it started still runs, and what the
    /// agent reported is left of its goal.
    Run { work: Work, left: Option<String> },
}

/// What the gateway holds after an event, and what it sends now.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Step {
    /// The run's last answer, for the report at its end.
    pub(crate) held: Option<Answer>,
    /// The message the phone gets now.
    pub(crate) send: Option<Answer>,
}

fn put(writer: &mut Writer, answer: Option<&Answer>) {
    match answer {
        None => writer.tag(0),
        Some(Answer::Text(text)) => writer.tag(1).str(text),
        Some(Answer::Failed(reason)) => writer.tag(2).str(reason),
        Some(Answer::Stopped) => writer.tag(3),
    };
}

fn read(reader: &mut Reader<'_>) -> Result<Option<Answer>, WireError> {
    Ok(match reader.tag_of(4, "an answer")? {
        0 => None,
        1 => Some(Answer::Text(reader.str()?.to_owned())),
        2 => Some(Answer::Failed(reader.str()?.to_owned())),
        3.. => Some(Answer::Stopped),
    })
}

/// The step of one event of the bound session: the gateway held `held`,
/// the event answers `answer` (`crate::answer::answer`) and ends the run
/// or not. Every text is one the daemon sent (a model's output, the goal's
/// remaining work), far below the wire's `STR_MAX`.
pub(crate) fn step(held: Option<&Answer>, answer: Option<&Answer>, end: &End) -> Step {
    let mut writer = Writer::new();
    put(&mut writer, held);
    put(&mut writer, answer);
    match end {
        End::No => {
            writer.tag(0);
        }
        End::Run { work, left } => {
            writer.tag(1).bool(match work {
                Work::Running => true,
                Work::Settled => false,
            });
            match left {
                Some(left) => writer.some().str(left),
                None => writer.none(),
            };
        }
    }
    let mut read_step = || -> Result<Step, Error> {
        let reply = call(Entry::GatewayReport, &writer.finish()?)?;
        let mut reader = Reader::reply(&reply)?;
        let held = read(&mut reader)?;
        let send = read(&mut reader)?;
        reader.end()?;
        Ok(Step { held, send })
    };
    expect_core(Entry::GatewayReport, read_step())
}

#[cfg(test)]
mod tests;
