//! The tool-call side of a task's budget (spec/README.md B1, B4): a tool
//! call reserves one call and its blocking time before it runs, and
//! settles the one call after. A call that does not fit does not run: the
//! model reads a tool error that tells it to give its final answer. A
//! budget with a deadline stops a call at its granted time.

use std::future::Future;
use std::sync::Arc;
use std::time::Duration;

use eukhe_budget::{Reserved, Use, TOOL_MIN_MS};
use eukhe_chord::context::{with_cancel, Context};
use eukhe_durable::harness::types::{ToolExecute, ToolExecutionResult};
use eukhe_types::budget::BudgetAmounts;
use eukhe_types::pi_ai::{TextContent, UserContentBlock};
use futures::FutureExt as _;

use super::notices::{self, NoticeKind};
use super::{BudgetGate, Held};

/// How long a tool call may block when the settings name no blocking
/// budget.
const DEFAULT_TOOL_TIME_MS: u64 = 600_000;
/// How long past its granted time a call that was granted its whole
/// blocking budget may still end by itself: at that budget the tool
/// detaches its work and returns, and the gate must not cancel the call
/// while it does.
const DETACH_GRACE_MS: u64 = 5_000;

/// How a tool call came through the gate.
#[derive(Debug, PartialEq, Eq)]
pub(super) enum ToolOutcome<T> {
    /// It ran: its result.
    Ran(T),
    /// It did not run, or was stopped at its granted time: the tool error
    /// the model reads.
    Refused(String),
}

impl BudgetGate {
    /// What one tool call asks: the call and its blocking time (the
    /// settings' blocking budget; the ledger clips it to what is left
    /// before the deadline).
    pub(super) fn tool_offer(&self) -> BudgetAmounts {
        let blocking = self.settings.as_ref().map_or(0, |settings| {
            let budget = settings.manager().get_tool_blocking_budget();
            u64::try_from(budget.as_millis()).unwrap_or(u64::MAX)
        });
        BudgetAmounts {
            tool_calls: 1,
            time_ms: if blocking == 0 {
                DEFAULT_TOOL_TIME_MS
            } else {
                blocking
            },
            ..BudgetAmounts::default()
        }
    }

    /// One tool call `label` behind the gate: reserve its
    /// [`Self::tool_offer`], leaving the agent's final-answer reserve free;
    /// `run` the call under `cx` when granted; settle the one call. A
    /// budget with a deadline also cancels the call's context once its
    /// granted time passed. A session without a budget just runs the call.
    pub(super) async fn gated_call<T, F, Fut>(
        self: &Arc<Self>,
        label: String,
        cx: Context,
        run: F,
    ) -> ToolOutcome<T>
    where
        F: FnOnce(Context) -> Fut,
        Fut: Future<Output = T>,
    {
        let offer = self.tool_offer();
        let blocking = offer.time_ms;
        let one_call = BudgetAmounts {
            time_ms: 0,
            ..offer
        };
        let reserved = self
            .reserve(Use::Work, label, self.keep(), vec![offer], TOOL_MIN_MS)
            .await;
        let (reservation, report) = match reserved {
            Ok(None) => return ToolOutcome::Ran(run(cx).await),
            Err(error) => {
                return ToolOutcome::Refused(notices::ledger_failed(
                    "this tool call was not run",
                    &error,
                ))
            }
            Ok(Some(Reserved::Refused { refusal, report })) => {
                return ToolOutcome::Refused(notices::tool_refused(notices::short_label(
                    refusal, &report,
                )))
            }
            Ok(Some(Reserved::Granted {
                reservation,
                report,
            })) => (reservation, report),
        };
        if reservation.low {
            let keep = self.keep();
            self.tell(NoticeKind::Low, &report, || {
                notices::low_text(&report, keep)
            });
        }
        let held = Held::start(self, reservation.id, reservation.amount, Use::Work);
        let outcome = if report.deadline_ms.is_none() {
            ToolOutcome::Ran(run(cx).await)
        } else {
            let granted = reservation.amount.time_ms;
            let grace = if granted >= blocking {
                DETACH_GRACE_MS
            } else {
                0
            };
            let stop_after = Duration::from_millis(granted.saturating_add(grace));
            let (stoppable, stop) = with_cancel(&cx);
            let call = run(stoppable);
            tokio::pin!(call);
            tokio::select! {
                biased;
                result = &mut call => ToolOutcome::Ran(result),
                () = tokio::time::sleep(stop_after) => {
                    stop.cancel(None);
                    // The cancelled call ends by itself; what it
                    // returns gives way to the budget's error.
                    drop(call.await);
                    ToolOutcome::Refused(notices::TOOL_STOPPED.to_owned())
                }
            }
        };
        held.settle(one_call).await;
        outcome
    }

    /// `execute` of the tool `name` behind the gate
    /// ([`Self::gated_call`]); a call the gate refuses or stops returns its
    /// tool error.
    pub(crate) fn wrap_tool(self: &Arc<Self>, name: &str, execute: ToolExecute) -> ToolExecute {
        let gate = Arc::clone(self);
        let label = format!("tool:{name}");
        Arc::new(move |args, api, cx| {
            if !gate.ledger.exists() {
                return execute(args, api, cx);
            }
            let gate = Arc::clone(&gate);
            let label = label.clone();
            let execute = Arc::clone(&execute);
            async move {
                match gate
                    .gated_call(label, cx, |cx| execute(args, api, cx))
                    .await
                {
                    ToolOutcome::Ran(result) => result,
                    ToolOutcome::Refused(text) => Ok(ToolExecutionResult {
                        output: Some(vec![UserContentBlock::Text(TextContent::new(text))]),
                        is_error: Some(true),
                        ..ToolExecutionResult::default()
                    }),
                }
            }
            .boxed()
        })
    }
}
