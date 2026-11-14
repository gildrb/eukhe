//! Verified-completion wire state. The `acceptance_update` session event
//! and the attach snapshot's `state.acceptance` field carry this object to
//! every attached surface (TUI, ACP, CLI, SDK clients), so the shared
//! vocabulary lives in eukhe-types; the verifier (evidence, verdicts, the
//! compiled core's decisions) lives in eukhe-core. Field shape: camelCase,
//! optional keys omitted.

use serde::{Deserialize, Serialize};

/// What one acceptance check asks. Set by the task's owner, never by the
/// worker.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(
    tag = "kind",
    rename_all = "camelCase",
    rename_all_fields = "camelCase"
)]
pub enum CheckSpec {
    /// A shell command the harness runs in the session cwd: confirmed
    /// exactly when it exits with `expect` and no `protect` file changed.
    Command {
        command: String,
        /// The expected exit code.
        #[serde(default)]
        expect: u32,
        /// The time limit; the default when absent.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        timeout_ms: Option<u64>,
        /// Files the worker must not change (the check's own tests or
        /// script), relative to the session cwd.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        protect: Vec<String>,
    },
    /// A condition a judge (a separate model request) decides from evidence the harness
    /// gathers: the output of the other checks of the round and of the
    /// `evidence` commands (the workspace diff when there is neither).
    Judge {
        condition: String,
        /// Shell commands whose output the judge reads.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        evidence: Vec<String>,
        /// The judge's model (`provider/id`); the session's when absent.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        model: Option<String>,
    },
    /// A loop's until-condition: a shell command that exits 0 when the
    /// condition holds and 1 when it does not yet.
    Until {
        command: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        timeout_ms: Option<u64>,
    },
    /// The task's intent: an independent judge reads the user's own
    /// messages (never the worker's), decides what the conversation asks
    /// for now (a later requirement extends the task, a dropped one is
    /// gone, a side question adds none) and whether the final state, as
    /// the harness observes it, meets it.
    Intent {
        /// The judge's model (`provider/id`); the session's when absent.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        model: Option<String>,
    },
}

impl CheckSpec {
    /// The intent check with the session's model.
    #[must_use]
    pub fn intent() -> Self {
        Self::Intent { model: None }
    }
}

/// The checks an owner's surface sets (the CLI's flags, `/accept`, the
/// `set_acceptance` command, a parent's spawn): `explicit`, then the
/// intent check unless `intent` is false or `explicit` already holds one.
/// The intent check goes last: its judge reads the round's other checks.
#[must_use]
pub fn owner_checks(explicit: Vec<CheckSpec>, intent: bool) -> Vec<CheckSpec> {
    let mut checks = explicit;
    if intent
        && !checks
            .iter()
            .any(|check| matches!(check, CheckSpec::Intent { .. }))
    {
        checks.push(CheckSpec::intent());
    }
    checks
}

/// The verdict of one check on one state.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CheckVerdict {
    Confirmed,
    Refuted,
    /// The check itself failed to judge (no exit code, a timeout, a judge
    /// with no readable answer): never read as passed or failed.
    Broken,
    /// Nothing was learned (a cancelled check).
    Unjudged,
}

impl CheckVerdict {
    /// The wire slug.
    #[must_use]
    pub fn slug(self) -> &'static str {
        match self {
            Self::Confirmed => "confirmed",
            Self::Refuted => "refuted",
            Self::Broken => "broken",
            Self::Unjudged => "unjudged",
        }
    }
}

/// The label of a result.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AcceptanceLabel {
    /// There is a check, every check is confirmed on the final state and
    /// the run's programs ran confined. No confinement exists yet, so no
    /// result carries it.
    Verified,
    /// A check is refuted on the final state.
    Failed,
    /// Neither: no checks, or a check that did not judge the final state,
    /// is broken or unjudged.
    Unverified,
    /// There is a check and every check is confirmed on the final state,
    /// while the run's programs ran unconfined: they could reach what the
    /// checks read.
    ChecksPassedUnconfined,
}

impl AcceptanceLabel {
    /// The wire slug.
    #[must_use]
    pub fn slug(self) -> &'static str {
        match self {
            Self::Verified => "verified",
            Self::Failed => "failed",
            Self::Unverified => "unverified",
            Self::ChecksPassedUnconfined => "checks_passed_unconfined",
        }
    }

    /// The label as surfaces show it.
    #[must_use]
    pub fn text(self) -> &'static str {
        match self {
            Self::Verified => "verified",
            Self::Failed => "failed",
            Self::Unverified => "unverified",
            Self::ChecksPassedUnconfined => "checks passed, unconfined",
        }
    }

    /// Every check is confirmed on the final state: verified or checks
    /// passed, unconfined.
    #[must_use]
    pub fn passed(self) -> bool {
        matches!(self, Self::Verified | Self::ChecksPassedUnconfined)
    }
}

/// A file a check protects, as its owner left it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ProtectedFile {
    pub path: String,
    /// The sha256 of its bytes when the check was set; `None`: no such
    /// file then.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sha256: Option<String>,
}

/// The last verdict of a check, with what the harness observed.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CheckResult {
    pub verdict: CheckVerdict,
    /// The state the verdict judged: the conversation's newest tool
    /// result then. A later effect of the worker makes it stale.
    pub at: u64,
    /// One line: how the check ended (`exited with code 1`, `the judge
    /// answered FAIL`, `protected file changed: tests/x.py`).
    pub summary: String,
    /// What the harness observed (the command's output, the judge's
    /// reply), cut to a bound.
    pub evidence: String,
    /// When the verdict was recorded (ms since the epoch).
    pub judged_at: u64,
}

/// One acceptance check and its last verdict.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AcceptanceCheck {
    pub spec: CheckSpec,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub protected: Vec<ProtectedFile>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub result: Option<CheckResult>,
}

/// How the last claim ended.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AcceptanceEnd {
    pub label: AcceptanceLabel,
    /// The state the claim was judged on.
    pub at: u64,
    /// When it ended (ms since the epoch).
    pub ended_at: u64,
}

/// The acceptance of one conversation as every surface reads it (the
/// `acceptance_update` event payload and `state.acceptance`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AcceptanceState {
    /// The label of the result on the conversation's state now: the
    /// compiled core's. `unverified` with no checks.
    pub label: AcceptanceLabel,
    /// The conversation's state now: it moves with the newest effect, the
    /// newest user message and the workspace; 0 before any of them.
    pub state: u64,
    /// The revision of the checks: it grows each time the owner sets them.
    pub revision: u64,
    pub checks: Vec<AcceptanceCheck>,
    /// A claim of "done" waits for its verdict.
    pub claimed: bool,
    /// How many times in a row a refuted claim went back to the worker.
    pub tries: u64,
    /// The most returns in a row before a refuted claim ends failed.
    pub max_returns: u64,
    /// How the last claim ended; cleared by the worker's next effect and
    /// by a change of the checks.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub last_end: Option<AcceptanceEnd>,
}

impl Default for AcceptanceState {
    fn default() -> Self {
        Self {
            label: AcceptanceLabel::Unverified,
            state: 0,
            revision: 0,
            checks: Vec::new(),
            claimed: false,
            tries: 0,
            max_returns: DEFAULT_MAX_RETURNS,
            last_end: None,
        }
    }
}

/// The checks a session starts with: the CLI's `--accept-cmd` and
/// `--accept-judge` flags, a client's create config (`acceptance`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AcceptanceSeed {
    /// The explicit checks.
    #[serde(default)]
    pub checks: Vec<CheckSpec>,
    /// The most returns in a row; the default when absent.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub max_returns: Option<u64>,
    /// Whether the intent check joins the explicit ones (default true).
    #[serde(default = "yes", skip_serializing_if = "is_yes")]
    pub intent: bool,
}

impl AcceptanceSeed {
    /// The checks the session starts with: [`owner_checks`] of this seed.
    #[must_use]
    pub fn specs(&self) -> Vec<CheckSpec> {
        owner_checks(self.checks.clone(), self.intent)
    }
}

fn yes() -> bool {
    true
}

#[allow(clippy::trivially_copy_pass_by_ref)]
fn is_yes(value: &bool) -> bool {
    *value
}

/// The default of [`AcceptanceState::max_returns`].
pub const DEFAULT_MAX_RETURNS: u64 = 3;
