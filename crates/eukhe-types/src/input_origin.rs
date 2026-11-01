//! Who produced a user-role input. A submission, its queued `pi.inbox`
//! item, and the `pi.user` entry it places carry an [`InputOrigin`];
//! consumers classify inputs by this tag, never by the text.

use serde::{Deserialize, Serialize};

use crate::goal::GoalContextKind;
use crate::job::{BashStopper, CellStatus, JobId};
use crate::pi_ai::StreamFailureKind;

/// The producer of one user-role input.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase")]
pub enum InputOrigin {
    /// A person's words, or a client prompt sent on their behalf.
    User,
    /// A goal context the goal engine submitted.
    Goal { context: GoalContextKind },
    /// An autonomous-mode continuation.
    Autonomous { nudge: AutonomousNudge },
    /// A continuation a Director layer added (a forced tool call that the
    /// model has not made yet).
    Director,
    /// The marker that resumes a session the provider quota parked.
    QuotaResume,
    /// A report of work outside this conversation.
    Report { report: Report },
}

/// Why autonomous mode continued a run.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum AutonomousNudge {
    /// The answer had no terminal evidence.
    Continuation,
    /// A quality gate failed.
    GateFailed,
}

/// How a child run ended without an explicit reply.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum ChildExit {
    /// The parent deleted the running child.
    Cancelled,
    /// The child finished without sending a message back.
    NoReply,
}

impl ChildExit {
    /// The header word: `cancelled` or `no-reply`.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Self::Cancelled => "cancelled",
            Self::NoReply => "no-reply",
        }
    }
}

/// Why a child run failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(
    tag = "cause",
    rename_all = "camelCase",
    rename_all_fields = "camelCase"
)]
pub enum ChildFailure {
    /// The child's last model request failed at its provider.
    Provider { kind: StreamFailureKind },
    /// The child's run was aborted before it answered.
    Aborted,
    /// The child stopped mid-run while its parent session was down.
    Interrupted,
    /// No live worker process hosts the child any more (the supervisor's
    /// process verdict, never a count of failed requests). Whatever the
    /// run was doing when its worker died may or may not have taken
    /// effect (ADR 0011: effects unknown).
    WorkerExited,
    /// The task prompt never reached the child.
    Undelivered,
    /// The child showed no progress for `subagentStallMs`; its run was
    /// stopped.
    Stalled,
    /// The child's polls failed `CHILD_POLL_FAILURES` times in a row while
    /// its worker process was alive or restarting.
    Unreachable,
}

impl std::fmt::Display for ChildFailure {
    /// The header word: `provider-<kind>`, `aborted`, `interrupted`,
    /// `worker-exited`, `undelivered`, `stalled`, or `unreachable`.
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Provider { kind } => write!(formatter, "provider-{kind}"),
            Self::Aborted => formatter.write_str("aborted"),
            Self::Interrupted => formatter.write_str("interrupted"),
            Self::WorkerExited => formatter.write_str("worker-exited"),
            Self::Undelivered => formatter.write_str("undelivered"),
            Self::Stalled => formatter.write_str("stalled"),
            Self::Unreachable => formatter.write_str("unreachable"),
        }
    }
}

/// A report delivered as input. Header values are sanitized by the
/// producer: they hold no brackets, newlines, commas, or colons.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "report", rename_all = "camelCase")]
pub enum Report {
    /// A message from another agent session; `sender` is its label
    /// (`child:name`, `parent:name`, or a bare name).
    AgentMessage { sender: String },
    /// A child run ended without an explicit reply.
    ChildExited { child: String, exit: ChildExit },
    /// A child run failed. `failure` is absent on reports recorded before
    /// failures were typed.
    ChildFailed {
        child: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        failure: Option<ChildFailure>,
    },
    /// A heartbeat fire.
    Heartbeat { schedule: String, run: u64 },
    /// A detached kernel bash command finished; `stopped_by` is absent
    /// unless a stop request ended it.
    #[serde(rename_all = "camelCase")]
    BashDone {
        pid: u32,
        exit_code: i64,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        stopped_by: Option<BashStopper>,
    },
    /// A detached `ipython` cell settled.
    JobSettled { job: JobId, status: CellStatus },
}

impl Report {
    /// The header line the model text starts with.
    #[must_use]
    pub fn header(&self) -> String {
        match self {
            Self::AgentMessage { sender } => format!("[agent-message from {sender}]"),
            Self::ChildExited { child, exit } => {
                format!("[child-exited: {} child:{child}]", exit.label())
            }
            Self::ChildFailed {
                child,
                failure: Some(failure),
            } => format!("[child-failed: {failure} child:{child}]"),
            Self::ChildFailed {
                child,
                failure: None,
            } => format!("[child-failed child:{child}]"),
            Self::Heartbeat { schedule, run } => format!("[heartbeat: {schedule} run#{run}]"),
            Self::BashDone {
                pid,
                exit_code,
                stopped_by: None,
            } => format!("[bash-done pid:{pid} exit:{exit_code}]"),
            Self::BashDone {
                pid,
                exit_code,
                stopped_by: Some(stopper),
            } => format!(
                "[bash-done pid:{pid} exit:{exit_code} stopped-by:{}]",
                stopper.label()
            ),
            Self::JobSettled { job, status } => {
                format!("[job-settled job:{job} status:{}]", status.label())
            }
        }
    }

    /// The model text: the header, then a blank line and `body` when the
    /// body is not empty. A report of settled work ([`Report::resumes`])
    /// puts [`RESUME_LINE`] between them ([`RESUME_ALONE`] without a body),
    /// so the turn it wakes takes the task up again.
    #[must_use]
    pub fn render(&self, body: &str) -> String {
        let header = self.header();
        match (self.resumes(), body.is_empty()) {
            (false, true) => header,
            (false, false) => format!("{header}\n\n{body}"),
            (true, true) => format!("{header}\n\n{RESUME_ALONE}"),
            (true, false) => format!("{header}\n\n{RESUME_LINE}\n\n{body}"),
        }
    }

    /// Whether the report hands back settled work to resume the task from:
    /// a finished `bash()` command or job, a child that ended without a
    /// reply or failed. A message, a heartbeat, and a child its parent
    /// cancelled carry no result to resume from.
    #[must_use]
    pub fn resumes(&self) -> bool {
        match self {
            Self::BashDone { .. } | Self::JobSettled { .. } | Self::ChildFailed { .. } => true,
            Self::ChildExited { exit, .. } => match exit {
                ChildExit::NoReply => true,
                ChildExit::Cancelled => false,
            },
            Self::AgentMessage { .. } | Self::Heartbeat { .. } => false,
        }
    }

    /// The body of `text`, a text [`Report::render`] produced (the resume
    /// line dropped; a text rendered before it existed reads the same).
    ///
    /// # Errors
    ///
    /// `text` does not start with this report's header.
    pub fn body<'a>(&self, text: &'a str) -> Result<&'a str, ReportTextError> {
        let header = self.header();
        let rest = text
            .strip_prefix(&header)
            .ok_or(ReportTextError { header })?;
        let rest = rest.strip_prefix("\n\n").unwrap_or(rest);
        if !self.resumes() {
            return Ok(rest);
        }
        if rest == RESUME_ALONE {
            return Ok("");
        }
        Ok(rest
            .strip_prefix(RESUME_LINE)
            .map_or(rest, |after| after.strip_prefix("\n\n").unwrap_or(after)))
    }
}

/// The line after the header of a report of settled work with a body
/// (omp's async-result notice): the woken turn resumes the task with the
/// result instead of acknowledging the notice.
pub const RESUME_LINE: &str = "Resume your work using the result below.";
/// The resume line of a report of settled work without a body.
pub const RESUME_ALONE: &str = "Resume your work.";

/// A report's text that does not start with the report's header.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("report text does not start with its header {header}")]
pub struct ReportTextError {
    header: String,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn report_body_is_the_text_after_its_rendered_header() {
        let report = Report::ChildExited {
            child: "scout".to_owned(),
            exit: ChildExit::NoReply,
        };
        let text = report.render("Last assistant text: hi");
        assert_eq!(report.body(&text), Ok("Last assistant text: hi"));
        assert_eq!(report.body(&report.render("")), Ok(""));
        assert_eq!(
            report.body("[child-failed child:scout]\n\nboom"),
            Err(ReportTextError {
                header: "[child-exited: no-reply child:scout]".to_owned()
            })
        );
    }

    /// A report of settled work tells the woken turn to resume the task;
    /// a message, a heartbeat, or a cancelled child does not. Its body reads
    /// back without the line, also from a text rendered before the line.
    #[test]
    fn settled_work_reports_resume_the_task() {
        let settled = Report::JobSettled {
            job: JobId::new("cell-1").expect("a header-safe id"),
            status: CellStatus::Ok,
        };
        assert_eq!(
            settled.render("42"),
            "[job-settled job:cell-1 status:ok]\n\nResume your work using the result below.\n\n42"
        );
        assert_eq!(
            settled.render(""),
            "[job-settled job:cell-1 status:ok]\n\nResume your work."
        );
        assert_eq!(settled.body(&settled.render("42")), Ok("42"));
        assert_eq!(settled.body(&settled.render("")), Ok(""));
        assert_eq!(
            settled.body("[job-settled job:cell-1 status:ok]\n\n42"),
            Ok("42")
        );
        let cancelled = Report::ChildExited {
            child: "scout".to_owned(),
            exit: ChildExit::Cancelled,
        };
        assert_eq!(
            cancelled.render("Deleted"),
            "[child-exited: cancelled child:scout]\n\nDeleted"
        );
        let message = Report::AgentMessage {
            sender: "child:scout".to_owned(),
        };
        assert_eq!(
            message.render("hi"),
            "[agent-message from child:scout]\n\nhi"
        );
    }
}
