//! Who produced a user-role input. A submission, its queued `pi.inbox`
//! item, and the `pi.user` entry it places carry an [`InputOrigin`];
//! consumers classify inputs by this tag, never by the text.

use serde::{Deserialize, Serialize};

use crate::goal::GoalContextKind;
use crate::job::{CellStatus, JobId};
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
}

impl std::fmt::Display for ChildFailure {
    /// The header word: `provider-<kind>`, `aborted`, `interrupted`,
    /// `worker-exited`, or `undelivered`.
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Provider { kind } => write!(formatter, "provider-{kind}"),
            Self::Aborted => formatter.write_str("aborted"),
            Self::Interrupted => formatter.write_str("interrupted"),
            Self::WorkerExited => formatter.write_str("worker-exited"),
            Self::Undelivered => formatter.write_str("undelivered"),
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
    /// A detached kernel bash command finished.
    #[serde(rename_all = "camelCase")]
    BashDone { pid: u32, exit_code: i64 },
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
            Self::BashDone { pid, exit_code } => format!("[bash-done pid:{pid} exit:{exit_code}]"),
            Self::JobSettled { job, status } => {
                format!("[job-settled job:{job} status:{}]", status.label())
            }
        }
    }

    /// The model text: the header, then a blank line and `body` when the
    /// body is not empty.
    #[must_use]
    pub fn render(&self, body: &str) -> String {
        let header = self.header();
        if body.is_empty() {
            header
        } else {
            format!("{header}\n\n{body}")
        }
    }

    /// The body of `text`, a text [`Report::render`] produced.
    ///
    /// # Errors
    ///
    /// `text` does not start with this report's header.
    pub fn body<'a>(&self, text: &'a str) -> Result<&'a str, ReportTextError> {
        let header = self.header();
        let rest = text
            .strip_prefix(&header)
            .ok_or(ReportTextError { header })?;
        Ok(rest.strip_prefix("\n\n").unwrap_or(rest))
    }
}

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
}
