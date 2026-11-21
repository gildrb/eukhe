//! What a budget tells the agent and the user (spec/README.md B6, B7, B8):
//! the texts, what is left as they show it, and their delivery to the
//! session's main conversation.
//!
//! The agent learns of its budget in the first request after the budget
//! was set or added to, learns that it runs low in the request after a
//! grant said two steps of its largest actual spend no longer fit (once
//! until budget is added), and is told to wrap up in the request that is
//! its final answer. The first two are rows the model reads, written into
//! the main conversation before the request they are due in reads its
//! context ([`notice_hook`]): they come before the request's answer, and
//! a low budget a final answer found is never written after it. The
//! wrap-up is the last message of the final answer's request and shows as
//! a display-only row. A notice never starts a run nor continues one.
//! Each has a request id made of its kind and the budget's limits, so a
//! rerun or a restart under the same budget does not repeat it.

use std::sync::{Arc, PoisonError, Weak};

use eukhe_budget::Refusal;
use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::harness::define::{define_extension, hook};
use eukhe_durable::harness::types::{
    Extension, GenerationHooks, HookApi, PlaceQueued, SubmissionDraft, WriteSubmissionDraft,
};
use eukhe_durable::harness::GENERATION_TASK;
use eukhe_types::budget::{
    BudgetAmounts, BudgetDimension, BudgetLimits, BudgetReport, LimitSource, PlanShare,
};
use futures::FutureExt as _;

use super::runs::BelowFloor;
use super::BudgetGate;
use crate::durable::deps::{HarnessCell, SessionClosing};
use crate::durable::main_conversation::{main_conversation, main_conversation_id};
use crate::durable::rlm::CustomNotice;
use crate::durable::HostDeps;

/// The custom type of the row that shows the wrap-up of a budget
/// (display-only: the user sees it, the model reads the notice in its
/// final-answer request).
pub const BUDGET_NOTICE_CUSTOM_TYPE: &str = "eukhe.budget";

/// The custom type of the rows that tell the agent its budget (set, runs
/// low): the model reads them, the user sees them.
pub const BUDGET_STATUS_CUSTOM_TYPE: &str = "eukhe.budget.status";

/// The error of a request the gate stopped at its granted time.
pub(super) const REQUEST_STOPPED: &str =
    "Budget exhausted (time): the request was stopped at its granted time.";

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

/// The notices a gate gave since its budget was last set or added to, and
/// those of them the agent's next request is still to carry.
#[derive(Debug, Default)]
pub(super) struct Told {
    set: bool,
    low: bool,
    wrap_up: bool,
    due: Vec<Notice>,
}

impl BudgetGate {
    /// Send the gate's wrap-up notices to `sink` (the first sink stays).
    pub(super) fn deliver_notices(&self, sink: NoticeSink) {
        // A second sink is dropped: the first one delivers.
        let _ = self.notices.set(sink);
    }

    /// The notice of `kind` under the budget `report` shows, unless it was
    /// given since the budget was last set or added to; it is given now.
    fn give(
        &self,
        kind: NoticeKind,
        report: &BudgetReport,
        text: impl FnOnce() -> String,
    ) -> Option<Notice> {
        {
            let mut told = self.told.lock().unwrap_or_else(PoisonError::into_inner);
            let given = match kind {
                NoticeKind::Set => &mut told.set,
                NoticeKind::Low => &mut told.low,
                NoticeKind::WrapUp => &mut told.wrap_up,
            };
            if std::mem::replace(given, true) {
                return None;
            }
        }
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
        Some(Notice {
            kind,
            request_id: format!("budget:{}:{slug}:{}", self.agent(), budget.join(":")),
            text: text(),
        })
    }

    /// Give the notice of `kind` (see [`Self::give`]) to the sink now: the
    /// wrap-up, which its own request carries.
    pub(super) fn tell(
        &self,
        kind: NoticeKind,
        report: &BudgetReport,
        text: impl FnOnce() -> String,
    ) {
        let Some(sink) = self.notices.get() else {
            return;
        };
        if let Some(notice) = self.give(kind, report, text) {
            sink(notice);
        }
    }

    /// Give the notice of `kind` (see [`Self::give`]) to the agent's next
    /// request ([`Self::due`]): a low budget, found by a grant whose
    /// request is already built.
    pub(super) fn tell_next(
        &self,
        kind: NoticeKind,
        report: &BudgetReport,
        text: impl FnOnce() -> String,
    ) {
        if let Some(notice) = self.give(kind, report, text) {
            self.told
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .due
                .push(notice);
        }
    }

    /// Whether the agent's next request may have notices due: the budget
    /// was not yet looked at since it was last set or added to, or a grant
    /// gave a notice since.
    pub(super) fn may_have_due(&self) -> bool {
        let told = self.told.lock().unwrap_or_else(PoisonError::into_inner);
        !told.set || !told.due.is_empty()
    }

    /// The notices the agent's next request carries, oldest first: the
    /// budget, once the run's limits are known (its first effect starts the
    /// session's first run; a run without limits is told nothing), and
    /// what grants gave since. Blocking file IO.
    pub(super) fn due(&self) -> Vec<Notice> {
        let mut due = Vec::new();
        let set = self.told.lock().unwrap_or_else(PoisonError::into_inner).set;
        if !set {
            match self.ensure_run() {
                Err(error) => tracing::warn!(%error, "the budget notice waits: no run started"),
                Ok(()) => match self.report() {
                    Some(report) if !report.limits.is_unlimited() => {
                        due.extend(self.give(NoticeKind::Set, &report, || set_text(&report)));
                    }
                    // Nothing to tell until the budget is set or added to.
                    Some(_) | None => {
                        self.told.lock().unwrap_or_else(PoisonError::into_inner).set = true;
                    }
                },
            }
        }
        due.append(&mut self.told.lock().unwrap_or_else(PoisonError::into_inner).due);
        due
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
        "[budget] This task has a budget: {}. Every model request and tool call reserves its worst case before it runs: plan your work to fit. In the Python kernel (the python tool) `await budget.status()` returns what is left.",
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
        "[budget] The {short} budget of this task is used up for work: {} left, too little for another step beside the final answer. Tools are no longer available. Give your final answer now: what is done, what is left, and that the {short} limit ended the work. At most {cap} output tokens.",
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
    format!("Budget exhausted ({short}): the request was not sent.")
}

/// The tool error of a call that did not run: the `short` budget is used
/// up.
pub(super) fn tool_refused(short: &str) -> String {
    format!("Budget exhausted ({short}): this tool call was not run. Give your final answer now.")
}

/// The error of a request or tool call the ledger could not admit
/// (`refused`: what did not happen): a ledger that fails refuses.
pub(super) fn ledger_failed(refused: &str, error: &dyn std::fmt::Display) -> String {
    format!("Budget ledger failed: {refused}. {error}")
}

/// `amount` of `dimension` as the floor's error writes it: money and time
/// as a notice shows them, counts as numbers.
fn floor_amount(dimension: BudgetDimension, amount: u64) -> String {
    match dimension {
        BudgetDimension::Cost | BudgetDimension::Time => shown(
            &BudgetLimits::default().with(dimension, Some(1)),
            BudgetAmounts::default().with(dimension, amount),
        ),
        BudgetDimension::Tokens | BudgetDimension::ToolCalls | BudgetDimension::Requests => {
            amount.to_string()
        }
    }
}

/// The error of a run's first request that does not fit its `limits`
/// beside the final answer (the `short` dimension): it asks `first`, the
/// final answer keeps `keep`.
pub(super) fn floor_text(
    short: BudgetDimension,
    limits: &BudgetLimits,
    first: BudgetAmounts,
    keep: BudgetAmounts,
) -> String {
    format!(
        "Budget too small for the run's first request: {} limit {}; the request needs {} and the final answer keeps {}. Nothing was sent: the run ended before its first request.",
        short.label(),
        floor_amount(short, limits.get(short).unwrap_or_default()),
        floor_amount(short, first.get(short)),
        floor_amount(short, keep.get(short)),
    )
}

/// The refusal of limits below the floor of one request, said when they
/// are set: the short dimension, its limit and who set it, and the least
/// the run's first request and its final answer ask in it.
impl std::fmt::Display for BelowFloor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let from = match &self.source {
            LimitSource::UntilFinished | LimitSource::Set => String::new(),
            LimitSource::LimitsProfile => " (limits profile)".to_owned(),
            LimitSource::Profile => " (budget.profile)".to_owned(),
            LimitSource::Preset(name) => format!(" (/b {name})"),
        };
        write!(
            f,
            "Below the floor of one request: {} limit {}{from}; the run's first request needs at least {} and the final answer keeps {}. The budget is as it was.",
            self.dimension.label(),
            floor_amount(self.dimension, self.limit),
            floor_amount(self.dimension, self.request),
            floor_amount(self.dimension, self.keep),
        )
    }
}

/// The notice that ends a final-answer request of at most `cap` output
/// tokens: the run reached its share of the plan's quota.
pub(super) fn plan_wrap_text(plan: &PlanShare, cap: u64) -> String {
    let (label, used) = plan.windows.get(plan.wrapped_by).map_or(("", 0), |window| {
        (window.label.as_str(), window.used_permille / 10)
    });
    format!(
        "[budget] Plan usage of the {label} window is at {used} % (limits on keep {} % of the window for the user): this run ends here. Tools are no longer available. Give your final answer now: what is done, what is left, and that the plan's {label} window ended the work. At most {cap} output tokens.",
        plan.reserve_percent
    )
}

/// The write of `notice`'s row: the set and low notices as rows the model
/// reads, the wrap-up as a display-only row; `None` (logged) when the row
/// cannot be built.
fn row(notice: Notice) -> Option<SubmissionDraft> {
    let custom_type = match notice.kind {
        NoticeKind::Set | NoticeKind::Low => BUDGET_STATUS_CUSTOM_TYPE,
        NoticeKind::WrapUp => BUDGET_NOTICE_CUSTOM_TYPE,
    };
    match CustomNotice::new(custom_type, notice.text, true, None).draft() {
        Ok(entry) => Some(SubmissionDraft::Write(WriteSubmissionDraft {
            request_id: Some(notice.request_id),
            entry,
        })),
        Err(error) => {
            tracing::warn!(%error, "budget notice row not built");
            None
        }
    }
}

/// Deliver the wrap-up `notice` to the session's main conversation as a
/// passive write: a busy conversation places it at its next boundary, an
/// idle one at once. A closing session takes none; a notice that cannot be
/// delivered is logged.
#[tracing::instrument(skip_all, fields(kind = ?notice.kind, request_id = %notice.request_id))]
pub(super) async fn deliver(harness: HarnessCell, closing: SessionClosing, notice: Notice) {
    let Some(harness) = harness.get() else {
        tracing::warn!("budget notice dropped: the session's Harness is not open");
        return;
    };
    let Some(draft) = row(notice) else {
        return;
    };
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

/// The name of the budget's extension.
const BUDGET_EXTENSION: &str = "eukhe.budget.notices";

/// The budget's extension: a `before_prepare` hook of `pi.generation` that
/// writes the notices due ([`BudgetGate::due`]) into the session's main
/// conversation and places them before its request reads the context. The
/// model reads the budget in the run's first request and a low budget in
/// the request after the grant that found it. Other conversations are told
/// nothing. The deps are held weakly (they hold the Harness that holds
/// this hook); a notice that cannot be written is logged and the request
/// goes on.
pub(crate) fn extension(deps: &Arc<HostDeps>) -> Arc<Extension> {
    let deps: Weak<HostDeps> = Arc::downgrade(deps);
    let notices = hook(
        &*GENERATION_TASK,
        GenerationHooks {
            before_prepare: Some(Arc::new(move |api: &HookApi, cx: &Context| {
                let (deps, conversation_id, cx) = (deps.clone(), api.conversation_id(), cx.clone());
                async move {
                    let Some(deps) = deps.upgrade() else {
                        return Ok(None);
                    };
                    if !deps.budget.may_have_due() {
                        return Ok(None);
                    }
                    let harness = deps.harness.require()?;
                    if main_conversation_id(&harness, &cx).await? != conversation_id {
                        return Ok(None);
                    }
                    let gate = Arc::clone(&deps.budget);
                    let due = match tokio::task::spawn_blocking(move || gate.due()).await {
                        Ok(due) => due,
                        Err(error) => {
                            tracing::warn!(%error, "budget notices not read");
                            return Ok(None);
                        }
                    };
                    let Some(conversation) = harness.conversation(conversation_id, &cx).await?
                    else {
                        return Ok(None);
                    };
                    let mut written = false;
                    for draft in due.into_iter().filter_map(row) {
                        match conversation.submit(draft, &cx).await {
                            Ok(_) => written = true,
                            Err(error) => tracing::warn!(%error, "budget notice not written"),
                        }
                    }
                    Ok(written.then_some(PlaceQueued))
                }
                .boxed()
            })),
            ..GenerationHooks::default()
        },
    );
    define_extension(Extension {
        name: BUDGET_EXTENSION.to_owned(),
        hooks: vec![notices],
        ..Extension::default()
    })
}
