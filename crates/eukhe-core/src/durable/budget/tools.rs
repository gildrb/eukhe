//! The tool-call side of a task's budget (spec/README.md B1, B4, B10): a
//! tool call reserves one call and its time before it runs, and settles
//! the one call after. A call that does not fit does not run: the model
//! reads a tool error that tells it to give its final answer. A budget
//! with a deadline stops a call at its granted time, where the deadline
//! (with the final-answer reserves) cuts it.

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

/// What one tool call asks: the call, and longer than any call blocks. A
/// call blocks its blocking budget and detaches, but an explicit wait
/// (`jobs.wait`, `rlm.collect`) blocks up to 30 minutes: so a call asks a
/// day, which a budget with a deadline cuts to the time left before it
/// (the ledger clips it). Only the deadline stops a call.
pub(super) const TOOL_OFFER: BudgetAmounts = BudgetAmounts {
    cost_micros: 0,
    tokens: 0,
    time_ms: 24 * 60 * 60 * 1000,
    tool_calls: 1,
    requests: 0,
};

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
    /// One tool call `label` behind the gate: reserve [`TOOL_OFFER`],
    /// leaving the agent's final-answer reserve free;
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
        let offer = TOOL_OFFER;
        let one_call = BudgetAmounts {
            time_ms: 0,
            ..offer
        };
        let reserved = self
            .reserve(
                Use::Work,
                label,
                None,
                self.keep(),
                vec![offer],
                TOOL_MIN_MS,
            )
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
            let stop_after = Duration::from_millis(reservation.amount.time_ms);
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
