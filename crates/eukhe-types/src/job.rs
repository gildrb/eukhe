//! The one job primitive (ADR 0010): work a session started that settles
//! after the call that started it stopped blocking the turn. A detached
//! `ipython` cell (its call outlived the runtime's blocking budget) and a
//! background kernel `bash()` handle are both jobs; each settles through one
//! [`JobSettled`] row, which wakes an idle session or steers a busy one.

use std::fmt;

use serde::{Deserialize, Serialize};

use crate::input_origin::Report;

/// A job's id, unique within its session. It is a report header value, so
/// it holds no brackets, whitespace, commas, or colons.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(try_from = "String", into = "String")]
pub struct JobId(String);

/// A job id with a character a report header cannot carry.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("job id {0:?} is empty or holds a bracket, whitespace, comma, or colon")]
pub struct JobIdError(String);

impl JobId {
    /// # Errors
    ///
    /// `id` is empty or holds a bracket, whitespace, comma, or colon.
    pub fn new(id: impl Into<String>) -> Result<Self, JobIdError> {
        let id = id.into();
        let header_safe = !id.is_empty()
            && !id
                .chars()
                .any(|c| c.is_whitespace() || matches!(c, '[' | ']' | ',' | ':'));
        if header_safe {
            Ok(Self(id))
        } else {
            Err(JobIdError(id))
        }
    }

    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for JobId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl TryFrom<String> for JobId {
    type Error = JobIdError;

    fn try_from(id: String) -> Result<Self, Self::Error> {
        Self::new(id)
    }
}

impl From<JobId> for String {
    fn from(id: JobId) -> Self {
        id.0
    }
}

/// How a detached cell ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum CellStatus {
    /// The cell ran to its end.
    Ok,
    /// The cell raised.
    Error,
    /// The cell honored a cancel's interrupt.
    Aborted,
    /// The cell ignored a cancel's interrupt past the grace, so its kernel
    /// was killed: its effects are unknown (ADR 0011).
    Killed,
}

impl CellStatus {
    /// The status as a report header value.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Self::Ok => "ok",
            Self::Error => "error",
            Self::Aborted => "aborted",
            Self::Killed => "killed",
        }
    }
}

/// One settled job: the row that wakes the session.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase")]
pub enum JobSettled {
    /// A detached `ipython` cell ended; `output` is its whole projection,
    /// bounded once by the producer (ADR 0009).
    Cell {
        job: JobId,
        status: CellStatus,
        output: String,
    },
    /// A background kernel `bash()` command exited; its output stays with
    /// the handle.
    #[serde(rename_all = "camelCase")]
    Bash {
        pid: u32,
        command: String,
        exit_code: i64,
    },
}

impl JobSettled {
    /// The report the woken input carries.
    #[must_use]
    pub fn report(&self) -> Report {
        match self {
            Self::Cell { job, status, .. } => Report::JobSettled {
                job: job.clone(),
                status: *status,
            },
            Self::Bash { pid, exit_code, .. } => Report::BashDone {
                pid: *pid,
                exit_code: *exit_code,
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_job_id_is_a_header_safe_value() {
        assert_eq!(
            JobId::new("cell-1a2b").map(String::from),
            Ok("cell-1a2b".to_owned())
        );
        for bad in ["", "a b", "a:b", "a,b", "[a", "a]", "a\nb"] {
            assert!(JobId::new(bad).is_err(), "{bad:?}");
        }
        assert!(serde_json::from_str::<JobId>("\"a:b\"").is_err());
    }

    #[test]
    fn a_settled_cell_reports_its_job_and_status() {
        let settled = JobSettled::Cell {
            job: JobId::new("cell-1a2b").expect("id"),
            status: CellStatus::Killed,
            output: "partial".to_owned(),
        };
        assert_eq!(
            settled.report().render("partial"),
            "[job-settled job:cell-1a2b status:killed]\n\npartial"
        );
        assert_eq!(
            serde_json::to_value(&settled).expect("encodes"),
            serde_json::json!({
                "kind": "cell",
                "job": "cell-1a2b",
                "status": "killed",
                "output": "partial",
            })
        );
    }

    #[test]
    fn a_settled_bash_command_keeps_the_bash_done_report() {
        let settled = JobSettled::Bash {
            pid: 7,
            command: "sleep 1".to_owned(),
            exit_code: 2,
        };
        assert_eq!(settled.report().header(), "[bash-done pid:7 exit:2]");
    }
}
