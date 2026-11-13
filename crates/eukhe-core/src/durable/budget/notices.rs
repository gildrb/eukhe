//! What a budget tells the agent and the user (spec/README.md B6, B7, B8):
//! the texts, what is left as they show it, and their delivery to the
//! session's main conversation.
//!
//! The agent learns of its budget at its first request after the budget
//! was set or added to, learns that it runs low when a grant says two
//! steps of its largest actual spend no longer fit (once until budget is
//! added), and is told to wrap up in the request that is its final
//! answer. The first two are written into the
//! conversation as rows the model reads (a busy conversation places them
//! at its next boundary, an idle one at once); a notice never starts a run
//! nor continues one. The wrap-up also shows as a display-only row. Each
//! has a request id made of its kind and the budget's limits, so a rerun
//! or a restart under the same budget does not repeat it.

use std::sync::{Arc, PoisonError};

use eukhe_budget::Refusal;
use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_durable::harness::types::{SubmissionDraft, WriteSubmissionDraft};
use eukhe_types::budget::{BudgetAmounts, BudgetDimension, BudgetLimits, BudgetReport};

use super::{BudgetError, BudgetGate};
use crate::durable::deps::{HarnessCell, SessionClosing};
use crate::durable::main_conversation::main_conversation;
use crate::durable::rlm::CustomNotice;

/// The custom type of the row that shows the wrap-up of a budget
/// (display-only: the user sees it, the model reads the notice in its
/// final-answer request).
pub const BUDGET_NOTICE_CUSTOM_TYPE: &str = "eukhe.budget";

/// The custom type of the rows that tell the agent its budget (set, runs
/// low): the model reads them, the user sees them.
pub const BUDGET_STATUS_CUSTOM_TYPE: &str = "eukhe.budget.status";

/// The error of a request the gate stopped at its granted time.
pub(super) const REQUEST_STOPPED: &str =
    "Budget exhausted (time): the request was stopped. Add budget to continue.";

/// The tool error of a call the gate stopped at its granted time.
pub(super) const TOOL_STOPPED: &str = "Budget exhausted (time): the tool call was stopped.";

/// What a notice is for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum NoticeKind {
    /// The task has a budget: it was set or added to.
    Set,
    /// The budget runs low.
    Low,
    /// The work budget is used up: the final answer is due.
    WrapUp,
}

/// One notice of a gate, for its session to deliver.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Notice {
    pub kind: NoticeKind,
    /// Stable under one budget: a rerun does not deliver it twice.
    pub request_id: String,
    pub text: String,
}

/// Receives a gate's notices. Called on the task of the request or tool
/// call that caused the notice; it must not block.
pub(super) type NoticeSink = Arc<dyn Fn(Notice) + Send + Sync>;

/// The notices a gate gave since its budget was last set or added to.
#[derive(Debug, Default)]
pub(super) struct Told {
    set: bool,
    low: bool,
    wrap_up: bool,
}

impl BudgetGate {
    /// Send the gate's notices to `sink` (the first sink stays).
    pub(super) fn deliver_notices(&self, sink: NoticeSink) {
        // A second sink is dropped: the first one delivers.
        let _ = self.notices.set(sink);
    }

    /// Give the notice of `kind` under the budget `report` shows, unless
    /// it was given since the budget was last set or added to.
    pub(super) fn tell(
        &self,
        kind: NoticeKind,
        report: &BudgetReport,
        text: impl FnOnce() -> String,
    ) {
        {
            let mut told = self.told.lock().unwrap_or_else(PoisonError::into_inner);
            let given = match kind {
                NoticeKind::Set => &mut told.set,
                NoticeKind::Low => &mut told.low,
                NoticeKind::WrapUp => &mut told.wrap_up,
            };
            if std::mem::replace(given, true) {
                return;
            }
        }
        let Some(sink) = self.notices.get() else {
            return;
        };
        let slug = match kind {
            NoticeKind::Set => "set",
            NoticeKind::Low => "low",
            NoticeKind::WrapUp => "wrap-up",
        };
        let mut budget: Vec<String> = BudgetDimension::ALL
            .into_iter()
            .map(|dimension| {
                report
                    .limits
                    .get(dimension)
                    .map_or_else(|| "-".to_owned(), |limit| limit.to_string())
            })
            .collect();
        budget.push(
            report
                .deadline_ms
                .map_or_else(|| "-".to_owned(), |deadline| deadline.to_string()),
        );
        sink(Notice {
            kind,
            request_id: format!("budget:{}:{slug}:{}", self.agent(), budget.join(":")),
            text: text(),
        });
    }
}

/// What is left in each dimension the budget limits, as a notice shows it:
/// `$0.0123, 12.3k tokens, 1m 20s, 7 tool calls, 3 requests` (money with 4
/// decimals below a dollar, else 2; time until the deadline; each amount
/// rounded down).
pub(super) fn remaining(report: &BudgetReport) -> String {
    shown(&report.limits, report.free)
}

/// `amounts` in each dimension `limits` limits, as a notice shows them
/// (see [`remaining`]; `time_ms` is a duration).
fn shown(limits: &BudgetLimits, amounts: BudgetAmounts) -> String {
    let left: Vec<String> = BudgetDimension::ALL
        .into_iter()
        .filter(|dimension| limits.get(*dimension).is_some())
        .map(|dimension| {
            let left = amounts.get(dimension);
            match dimension {
                BudgetDimension::Cost if left < 1_000_000 => format!("$0.{:04}", left / 100),
                BudgetDimension::Cost => {
                    format!("${}.{:02}", left / 1_000_000, left % 1_000_000 / 10_000)
                }
                BudgetDimension::Tokens if left < 1_000 => format!("{left} tokens"),
                BudgetDimension::Tokens if left < 1_000_000 => {
                    format!("{}.{}k tokens", left / 1_000, left % 1_000 / 100)
                }
                BudgetDimension::Tokens => {
                    format!(
                        "{}.{}M tokens",
                        left / 1_000_000,
                        left % 1_000_000 / 100_000
                    )
                }
                BudgetDimension::Time => {
                    let seconds = left / 1_000;
                    if seconds < 60 {
                        format!("{seconds}s")
                    } else if seconds < 3_600 {
                        format!("{}m {}s", seconds / 60, seconds % 60)
                    } else {
                        format!("{}h {}m", seconds / 3_600, seconds % 3_600 / 60)
                    }
                }
                BudgetDimension::ToolCalls if left == 1 => "1 tool call".to_owned(),
                BudgetDimension::ToolCalls => format!("{left} tool calls"),
                BudgetDimension::Requests if left == 1 => "1 request".to_owned(),
                BudgetDimension::Requests => format!("{left} requests"),
            }
        })
        .collect();
    if left.is_empty() {
        "no limit".to_owned()
    } else {
        left.join(", ")
    }
}

/// The notice of a budget that was set or added to.
pub(super) fn set_text(report: &BudgetReport) -> String {
    format!(
        "[budget] This task has a budget: {}. Nothing can be spent past it: plan your work to fit. In the Python kernel (the python tool) `await budget.status()` returns what is left.",
        remaining(report)
    )
}

/// The notice of a budget that runs low: what the agent can still spend
/// (what is free and what its requests in flight hold, which settle at
/// what they actually spend), and the part of it its final answer keeps
/// (`keep`).
pub(super) fn low_text(report: &BudgetReport, keep: BudgetAmounts) -> String {
    let unspent = BudgetDimension::ALL
        .into_iter()
        .filter(|dimension| *dimension != BudgetDimension::Time)
        .fold(report.free, |sum, dimension| {
            sum.with(
                dimension,
                sum.get(dimension)
                    .saturating_add(report.held.get(dimension)),
            )
        });
    format!(
        "[budget] Low: {} left, of which the final answer keeps {}. Two more steps of the largest size so far would not fit. Finish what matters most; when the work budget is used up you get one final answer without tools.",
        shown(&report.limits, unspent),
        shown(&report.limits, keep)
    )
}

/// The notice that ends a final-answer request of at most `cap` output
/// tokens: the `short` budget is used up.
pub(super) fn wrap_up_text(short: &str, report: &BudgetReport, cap: u64) -> String {
    format!(
        "[budget] The {short} budget of this task is used up for work: {} left, too little for another step beside the final answer. Tools are no longer available. Give your final answer now: what is done, what is not, and how to continue. At most {cap} output tokens.",
        remaining(report)
    )
}

/// The word for what ran short when a reservation was refused: the
/// dimension the refusal names, else the one that ended the work phase.
pub(super) fn short_label(refusal: Refusal, report: &BudgetReport) -> &'static str {
    match refusal {
        Refusal::Short(dimension) => dimension.label(),
        Refusal::Stopped => report.short.map_or("work", BudgetDimension::label),
    }
}

/// The error of a model request that was not sent: the `short` budget is
/// used up.
pub(super) fn request_refused(short: &str) -> String {
    format!("Budget exhausted ({short}): the request was not sent. Add budget to continue.")
}

/// The tool error of a call that did not run: the `short` budget is used
/// up.
pub(super) fn tool_refused(short: &str) -> String {
    format!("Budget exhausted ({short}): this tool call was not run. Give your final answer now.")
}

/// The error of a request or tool call the ledger could not admit
/// (`refused`: what did not happen): a ledger that fails refuses.
pub(super) fn ledger_failed(refused: &str, error: &BudgetError) -> String {
    format!("Budget ledger failed: {refused}. {error}")
}

/// Deliver `notice` to the session's main conversation as a passive write:
/// the set and low notices as rows the model reads, the wrap-up as a
/// display-only row. A write never starts or continues a run: a busy
/// conversation places it at its next boundary, an idle one at once. A
/// closing session takes none; a notice that cannot be delivered is
/// logged.
#[tracing::instrument(skip_all, fields(kind = ?notice.kind, request_id = %notice.request_id))]
pub(super) async fn deliver(harness: HarnessCell, closing: SessionClosing, notice: Notice) {
    let Some(harness) = harness.get() else {
        tracing::warn!("budget notice dropped: the session's Harness is not open");
        return;
    };
    let custom_type = match notice.kind {
        NoticeKind::Set | NoticeKind::Low => BUDGET_STATUS_CUSTOM_TYPE,
        NoticeKind::WrapUp => BUDGET_NOTICE_CUSTOM_TYPE,
    };
    let entry = match CustomNotice::new(custom_type, notice.text, true, None).draft() {
        Ok(entry) => entry,
        Err(error) => {
            tracing::warn!(%error, "budget notice row not built");
            return;
        }
    };
    let draft = SubmissionDraft::Write(WriteSubmissionDraft {
        request_id: Some(notice.request_id),
        entry,
    });
    let submitted = closing
        .admit(|| async {
            let conversation = main_conversation(&harness, &BACKGROUND_CONTEXT).await?;
            conversation
                .submit(draft, &BACKGROUND_CONTEXT)
                .await
                .map(drop)
        })
        .await;
    match submitted {
        Some(Ok(())) | None => {}
        Some(Err(error)) => tracing::warn!(%error, "budget notice not delivered"),
    }
}
