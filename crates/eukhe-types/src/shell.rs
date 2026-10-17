//! The shell's approval vocabulary (docs/tools.md, S7): the effect class
//! of one step of a `bash` script, the question the host asks the
//! attached client about a step whose class is not in the auto set, and
//! the client's answer.

use serde::{Deserialize, Serialize};

/// What one step (a simple command) may do. A command the classification
/// table does not know is [`ShellEffect::Exec`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ShellEffect {
    /// Reads files or shell state only.
    Read,
    /// Changes files.
    Write,
    /// Runs a program the table does not know.
    Exec,
    /// Talks to the network.
    Net,
}

impl ShellEffect {
    /// The effect's wire name.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Read => "read",
            Self::Write => "write",
            Self::Exec => "exec",
            Self::Net => "net",
        }
    }
}

/// The host asks the attached client whether one step may run (the
/// `shell_approval` frame).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ShellApprovalRequest {
    /// Unique within the session; the answer names it.
    pub request_id: String,
    /// The step's place in the script, from 0, in the order steps run.
    pub step: u64,
    /// The step as it will run, after expansion.
    pub command: String,
    pub effect: ShellEffect,
}

/// The client's answer to one [`ShellApprovalRequest`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ShellVerdict {
    Approve,
    Deny,
}
