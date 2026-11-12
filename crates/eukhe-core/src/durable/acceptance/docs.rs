//! The acceptance document of one conversation (`eukhe.acceptance`): the
//! checks its owner set, each check's last verdict with its evidence, the
//! pending claim, the returns in a row, how the last claim ended, and the
//! verifier's last decision at a final answer (keyed by the generation
//! task, so a rerun after a crash repeats it). The compiled core
//! (`eukhe_bend::rules::verify`) decides every change; this file maps the
//! document to the core's acceptance and back.

use std::path::PathBuf;

use eukhe_bend::rules::verify::{self, Slot, Verdict};
use eukhe_durable::documents::{ConversationDoc, DocDefinition};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::{LatestFork, TaskId};
use eukhe_types::acceptance::{
    AcceptanceCheck, AcceptanceEnd, CheckResult, CheckVerdict, DEFAULT_MAX_RETURNS,
};
use serde::{Deserialize, Serialize};

/// The acceptance of one conversation; a fork starts with no checks, so a
/// fork is unverified until its owner sets checks.
pub(crate) static ACCEPTANCE_DOC: ConversationDoc<AcceptanceDoc> = match ConversationDoc::define(
    DocDefinition {
        kind: ACCEPTANCE_DOC_KIND,
        version: 1,
        initial: AcceptanceDoc::default,
        migrate: None,
        checkpoint_when: Some(|_, _, _| true),
    },
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("eukhe.acceptance has a valid version"),
};

/// The document kind of [`ACCEPTANCE_DOC`].
pub(crate) const ACCEPTANCE_DOC_KIND: &str = "eukhe.acceptance";

fn default_max_returns() -> u64 {
    DEFAULT_MAX_RETURNS
}

/// `eukhe.acceptance`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct AcceptanceDoc {
    /// The revision of the checks: it grows each time the owner sets them.
    #[serde(default)]
    pub revision: u64,
    #[serde(default)]
    pub checks: Vec<AcceptanceCheck>,
    /// A claim of "done" waits for its verdict.
    #[serde(default)]
    pub claimed: bool,
    /// The waiting claim is the goal's (`goal.complete()`): its verdict
    /// completes or pauses the goal.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub goal_claim: bool,
    /// Returns to the worker in a row.
    #[serde(default)]
    pub tries: u64,
    /// The most returns in a row before a refuted claim ends failed.
    #[serde(default = "default_max_returns")]
    pub max_returns: u64,
    /// How the last claim ended; the worker's next effect clears it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub last_end: Option<AcceptanceEnd>,
    /// The verifier's decision at the last final answer it judged.
    #[serde(default, rename = "yield", skip_serializing_if = "Option::is_none")]
    pub yield_record: Option<YieldRecord>,
    /// The workspace the checks judge (the session cwd when they were
    /// set): its fingerprint is part of the state.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub workspace: Option<PathBuf>,
}

impl Default for AcceptanceDoc {
    fn default() -> Self {
        Self {
            revision: 0,
            checks: Vec::new(),
            claimed: false,
            goal_claim: false,
            tries: 0,
            max_returns: DEFAULT_MAX_RETURNS,
            last_end: None,
            yield_record: None,
            workspace: None,
        }
    }
}

/// The verifier's decision at the final answer of generation `task_id`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct YieldRecord {
    pub task_id: TaskId,
    /// The evidence text that continues the run; `None` ends it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub r#continue: Option<String>,
}

pub(crate) fn verdict_of(verdict: Verdict) -> CheckVerdict {
    match verdict {
        Verdict::Confirmed => CheckVerdict::Confirmed,
        Verdict::Refuted => CheckVerdict::Refuted,
        Verdict::Broken => CheckVerdict::Broken,
        Verdict::Unjudged => CheckVerdict::Unjudged,
    }
}

fn core_verdict(verdict: CheckVerdict) -> Verdict {
    match verdict {
        CheckVerdict::Confirmed => Verdict::Confirmed,
        CheckVerdict::Refuted => Verdict::Refuted,
        CheckVerdict::Broken => Verdict::Broken,
        CheckVerdict::Unjudged => Verdict::Unjudged,
    }
}

impl AcceptanceDoc {
    /// The slots of the checks, as the compiled core reads them.
    pub(crate) fn slots(&self) -> Vec<Slot> {
        self.checks
            .iter()
            .map(|check| match &check.result {
                None => Slot::Open,
                Some(result) => Slot::Judged {
                    verdict: core_verdict(result.verdict),
                    at: result.at,
                },
            })
            .collect()
    }

    /// The acceptance the compiled core decides on.
    pub(crate) fn core(&self) -> verify::Acceptance {
        verify::Acceptance {
            revision: self.revision,
            slots: self.slots(),
            claimed: self.claimed,
            tries: self.tries,
        }
    }

    /// Take the acceptance the compiled core answered: its revision,
    /// claim and tries, and per slot an open one clears the check's
    /// result, the slot at `recorded`'s index takes that result, and every
    /// other judged slot must be the result the check already holds.
    ///
    /// # Errors
    ///
    /// The core's slots do not match the checks (an inconsistent build).
    pub(crate) fn adopt(
        &mut self,
        next: &verify::Acceptance,
        recorded: Option<(usize, CheckResult)>,
    ) -> SessionResult<()> {
        if next.slots.len() != self.checks.len() {
            return Err(SessionError::error(format!(
                "the compiled core answered {} acceptance slots for {} checks",
                next.slots.len(),
                self.checks.len()
            )));
        }
        let mut recorded = recorded;
        for (index, (check, slot)) in self.checks.iter_mut().zip(&next.slots).enumerate() {
            match *slot {
                Slot::Open => check.result = None,
                Slot::Judged { verdict, at } => {
                    if let Some((_, result)) = recorded.take_if(|(at_index, _)| *at_index == index)
                    {
                        check.result = Some(result);
                    }
                    let held = check.result.as_ref().is_some_and(|result| {
                        result.verdict == verdict_of(verdict) && result.at == at
                    });
                    if !held {
                        return Err(SessionError::error(format!(
                            "the compiled core answered a verdict for acceptance check {index} that the session does not hold"
                        )));
                    }
                }
            }
        }
        self.revision = next.revision;
        self.claimed = next.claimed;
        // A goal's claim lasts as long as the claim it rides on.
        self.goal_claim = self.goal_claim && next.claimed;
        self.tries = next.tries;
        Ok(())
    }
}
