//! The goal extension's `pi.generation` hooks: the goal and autonomous
//! continuation loop on the Harness.
//!
//! - `before_request`: an active goal whose conversation's last run ended in
//!   a terminal provider failure fails (old `finish_for_terminal_message` at
//!   the failed turn and the restore-resurrection guard): a failed run ends
//!   without a final answer, so the next generation of the conversation
//!   settles it.
//! - `after_response`: every settled response spends the goal and autonomous
//!   budgets once per generation; a goal crossing its budget turns
//!   `budget_limited` and steers the run with the budget-limit context.
//! - `on_yield`: at a final answer an active goal mints one continuation
//!   (with the no-progress backoff and cap); otherwise an enabled autonomous
//!   run consults its gates and limits. Queued user input and unsettled RLM
//!   children hold the continuation (the queued run or the child's report
//!   run reaches its own final answer). An aborted run never reaches
//!   `on_yield`.
//!
//! Every decision is recorded in `eukhe.goal.loop` keyed by the generation
//! task, in the same commit as its goal change, so a rerun after a crash
//! repeats the decision instead of charging the goal twice.

use std::sync::Arc;
use std::time::Duration;

use eukhe_chord::context::{await_with_context, Context};
use eukhe_durable::entries::ASSISTANT_ENTRY;
use eukhe_durable::harness::define::hook;
use eukhe_durable::harness::types::{
    GenerationHooks, HookApi, HookRegistration, WhenBusy, YieldContinuation,
};
use eukhe_durable::harness::{Conversation, ConversationEntryQuery, GENERATION_TASK};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::{EntryRecord, TaskId};
use eukhe_types::pi_ai::{AssistantMessage, Message, UserContent};
use futures::FutureExt;

use super::autonomous::{decide, AutonomousDocState, AutonomousYield};
use super::docs::{
    open_doc, read_doc, write_doc, YieldOutcome, YieldRecord, AUTONOMOUS_DOC, GOAL_DOC, LOOP_DOC,
};
use super::host::GoalsHost;
use super::ops::{goal_context, submit_goal_context, user_input_queued};
use super::state::{
    accounted, failed, mint, mint_after_backoff, owns_continuation_wakeup, served, spends_budget,
    stamp, terminal_provider_failure, Mint, UsageOutcome,
};
use crate::autonomous::now_millis;
use crate::durable::children::has_unsettled_children;
use crate::goals::{GoalContextKind, GoalState, GoalStatus};

/// How many of the newest entries the failed-run check reads.
const RECENT_ENTRIES: usize = 16;

/// The goal extension's hook registration on `pi.generation`.
pub(crate) fn generation_hooks(host: &GoalsHost) -> HookRegistration {
    let before = host.clone();
    let after = host.clone();
    let yielded = host.clone();
    hook(
        &*GENERATION_TASK,
        GenerationHooks {
            before_request: Some(Arc::new(move |_, api, cx| {
                let host = before.clone();
                let api = api.clone();
                let cx = cx.clone();
                async move {
                    host.settle_failed_run(&api, &cx).await?;
                    Ok(None)
                }
                .boxed()
            })),
            after_response: Some(Arc::new(move |message, api, cx| {
                let host = after.clone();
                let message = message.clone();
                let api = api.clone();
                let cx = cx.clone();
                async move { host.account_response(&message, &api, &cx).await }.boxed()
            })),
            on_yield: Some(Arc::new(move |message, api, cx| {
                let host = yielded.clone();
                let message = message.clone();
                let api = api.clone();
                let cx = cx.clone();
                async move {
                    Ok(host
                        .on_yield(&message, &api, &cx)
                        .await?
                        .map(|text| YieldContinuation {
                            r#continue: UserContent::Text(text),
                        }))
                }
                .boxed()
            })),
            after_tools: None,
        },
    )
}

/// The newest assistant entry among `entries` (newest first) when it is a
/// terminal provider failure of another generation settled after the goal's
/// last write: the run it ended failed the goal.
fn stale_failure(entries: &[EntryRecord], current: TaskId, goal: &GoalState) -> Option<String> {
    let entry = entries
        .iter()
        .find(|entry| entry.kind == ASSISTANT_ENTRY.kind())?;
    if entry.by_task_id == Some(current) {
        return None;
    }
    let Some(Message::Assistant(message)) = entry.model.as_ref()?.first() else {
        return None;
    };
    if goal
        .updated_at
        .is_some_and(|updated_at| message.timestamp <= updated_at)
    {
        return None;
    }
    terminal_provider_failure(message)
}

impl GoalsHost {
    /// Fail an active goal whose conversation's last run ended in a
    /// terminal provider failure.
    async fn settle_failed_run(&self, api: &HookApi, cx: &Context) -> SessionResult<()> {
        let conversation_id = api.conversation_id();
        let Some(goal) = read_doc(api, &GOAL_DOC, conversation_id, cx).await? else {
            return Ok(());
        };
        if goal.status != GoalStatus::Active {
            return Ok(());
        }
        let conversation = self.conversation(conversation_id, cx).await?;
        let page = conversation
            .entries(ConversationEntryQuery::default(), RECENT_ENTRIES, None, cx)
            .await?;
        let current = api.task_id();
        if stale_failure(&page.items, current, &goal).is_none() {
            return Ok(());
        }
        let entries = page.items;
        conversation
            .commit(
                move |tx| async move {
                    let (draft, goal) = open_doc(&tx, &GOAL_DOC, conversation_id).await?;
                    let error = stale_failure(&entries, current, &goal);
                    if let Some(next) = error.and_then(|error| failed(&goal, Some(&error))) {
                        write_doc(&draft, &stamp(next, now_millis()))?;
                    }
                    Ok(())
                },
                cx,
            )
            .await
    }

    /// Account one settled response against the goal and the autonomous
    /// run, once per generation.
    async fn account_response(
        &self,
        message: &AssistantMessage,
        api: &HookApi,
        cx: &Context,
    ) -> SessionResult<()> {
        if !spends_budget(message.stop_reason) {
            return Ok(());
        }
        let conversation_id = api.conversation_id();
        let goal_active = read_doc(api, &GOAL_DOC, conversation_id, cx)
            .await?
            .is_some_and(|goal| goal.status == GoalStatus::Active);
        let autonomous_enabled = read_doc(api, &AUTONOMOUS_DOC, conversation_id, cx)
            .await?
            .is_some_and(|state| state.enabled);
        if !goal_active && !autonomous_enabled {
            return Ok(());
        }
        let conversation = self.conversation(conversation_id, cx).await?;
        let task_id = api.task_id();
        let usage = message.usage;
        let budget_limited = conversation
            .commit(
                move |tx| async move {
                    let now = now_millis();
                    let (loop_draft, mut loop_state) =
                        open_doc(&tx, &LOOP_DOC, conversation_id).await?;
                    let goal = if goal_active {
                        Some(open_doc(&tx, &GOAL_DOC, conversation_id).await?)
                    } else {
                        None
                    };
                    let autonomous = if autonomous_enabled {
                        Some(open_doc(&tx, &AUTONOMOUS_DOC, conversation_id).await?)
                    } else {
                        None
                    };
                    if loop_state.accounted == Some(task_id) {
                        // A rerun: report a crossing this generation already
                        // made, so its steer is (re)submitted.
                        return Ok(goal
                            .map(|(_, goal)| goal)
                            .filter(|goal| goal.status == GoalStatus::BudgetLimited));
                    }
                    let mut crossed = None;
                    let mut row = None;
                    if let Some((draft, goal)) = goal {
                        match accounted(&goal, &usage) {
                            UsageOutcome::Accounted(next) => write_doc(&draft, &stamp(next, now))?,
                            UsageOutcome::BudgetReached(next) => {
                                let written = stamp(next, now);
                                write_doc(&draft, &written)?;
                                row = Some(goal_context(&written, GoalContextKind::BudgetLimit)?.1);
                                crossed = Some(written);
                            }
                            UsageOutcome::Ignored => {}
                        }
                    }
                    if let Some((draft, mut state)) = autonomous {
                        state.account(&usage);
                        write_doc(&draft, &state)?;
                    }
                    loop_state.accounted = Some(task_id);
                    write_doc(&loop_draft, &loop_state)?;
                    if let Some(row) = row {
                        tx.append_entry(conversation_id, row).await?;
                    }
                    Ok(crossed)
                },
                cx,
            )
            .await?;
        // The budget-limit wrap-up steer (old `_shouldStopAfterTurn`'s budget
        // arm): the steering boundary places it next.
        if let Some(goal) = budget_limited {
            if let Some(goal_id) = goal.goal_id.clone() {
                let (text, _) =
                    goal_context(&served(&goal, now_millis()), GoalContextKind::BudgetLimit)?;
                submit_goal_context(
                    &conversation,
                    format!("goal:{goal_id}:budget-limit"),
                    text,
                    WhenBusy::Steer,
                    cx,
                )
                .await?;
            }
        }
        Ok(())
    }

    /// The continuation decision at a final answer; `Some` continues the run
    /// with that user text.
    async fn on_yield(
        &self,
        answer: &AssistantMessage,
        api: &HookApi,
        cx: &Context,
    ) -> SessionResult<Option<String>> {
        let conversation_id = api.conversation_id();
        let task_id = api.task_id();
        let recorded = read_doc(api, &LOOP_DOC, conversation_id, cx)
            .await?
            .and_then(|state| state.yield_record)
            .filter(|record| record.task_id == task_id);
        let conversation = self.conversation(conversation_id, cx).await?;
        let mut outcome = if let Some(record) = recorded {
            record.outcome
        } else {
            // Queued user input owns the boundary; unsettled children
            // hold the continuation until their report run.
            if user_input_queued(api, conversation_id, cx).await?
                || has_unsettled_children(api, conversation_id, cx).await?
            {
                return Ok(None);
            }
            let goal = read_doc(api, &GOAL_DOC, conversation_id, cx)
                .await?
                .unwrap_or_default();
            if !owns_continuation_wakeup(&goal) {
                return self
                    .autonomous_yield(&conversation, answer, task_id, cx)
                    .await;
            }
            let answer = answer.clone();
            commit_mint(
                &conversation,
                task_id,
                move |goal, now| mint(goal, &answer, now),
                cx,
            )
            .await?
        };
        loop {
            match outcome {
                YieldOutcome::Continue { text } => return Ok(Some(text)),
                YieldOutcome::End => return Ok(None),
                YieldOutcome::Wait { until } => {
                    let now = now_millis();
                    if until > now {
                        await_with_context(
                            tokio::time::sleep(Duration::from_millis(until - now)),
                            cx,
                        )
                        .await
                        .map_err(SessionError::Aborted)?;
                    }
                    outcome = if user_input_queued(api, conversation_id, cx).await? {
                        commit_mint(&conversation, task_id, |_, _| Mint::Refuse(None), cx).await?
                    } else {
                        commit_mint(
                            &conversation,
                            task_id,
                            |goal, _| mint_after_backoff(goal),
                            cx,
                        )
                        .await?
                    };
                }
            }
        }
    }

    /// The autonomous arm of a final answer (the goal does not own it).
    async fn autonomous_yield(
        &self,
        conversation: &Conversation,
        answer: &AssistantMessage,
        task_id: TaskId,
        cx: &Context,
    ) -> SessionResult<Option<String>> {
        let conversation_id = conversation.id();
        let Some(before) = read_doc(
            &self.harness.require()?,
            &AUTONOMOUS_DOC,
            conversation_id,
            cx,
        )
        .await?
        .filter(|state| state.enabled) else {
            return Ok(None);
        };
        let mut runtime = before.to_runtime();
        let decided = decide(&mut runtime, answer.stop_reason, self.gates.as_ref()).await;
        let (text, stop) = match decided {
            AutonomousYield::Inactive => return Ok(None),
            AutonomousYield::Continue(text) => (Some(text), None),
            AutonomousYield::Stop(stop) => (None, Some(stop)),
        };
        conversation
            .commit(
                move |tx| async move {
                    let (loop_draft, mut loop_state) =
                        open_doc(&tx, &LOOP_DOC, conversation_id).await?;
                    let (draft, current) = open_doc(&tx, &AUTONOMOUS_DOC, conversation_id).await?;
                    // An `/autonomous` change while the gates ran wins.
                    let unchanged = current.enabled && current.started_at == before.started_at;
                    let outcome = match (&text, unchanged) {
                        (Some(text), true) => YieldOutcome::Continue { text: text.clone() },
                        (None, true) | (_, false) => YieldOutcome::End,
                    };
                    if unchanged {
                        let last_stop = stop.or(current.last_stop);
                        write_doc(
                            &draft,
                            &AutonomousDocState::from_runtime(&runtime, last_stop),
                        )?;
                    }
                    loop_state.yield_record = Some(YieldRecord {
                        task_id,
                        outcome: outcome.clone(),
                    });
                    write_doc(&loop_draft, &loop_state)?;
                    Ok(match outcome {
                        YieldOutcome::Continue { text } => Some(text),
                        YieldOutcome::End | YieldOutcome::Wait { .. } => None,
                    })
                },
                cx,
            )
            .await
    }
}

/// Apply a goal mint in one commit and record its outcome for `task_id`.
async fn commit_mint<F>(
    conversation: &Conversation,
    task_id: TaskId,
    decide: F,
    cx: &Context,
) -> SessionResult<YieldOutcome>
where
    F: FnOnce(&GoalState, u64) -> Mint + Send + 'static,
{
    let conversation_id = conversation.id();
    conversation
        .commit(
            move |tx| async move {
                let now = now_millis();
                let (loop_draft, mut loop_state) =
                    open_doc(&tx, &LOOP_DOC, conversation_id).await?;
                let (goal_draft, goal) = open_doc(&tx, &GOAL_DOC, conversation_id).await?;
                let mut row = None;
                let outcome = match decide(&goal, now) {
                    Mint::Refuse(change) => {
                        if let Some(next) = change {
                            write_doc(&goal_draft, &stamp(next, now))?;
                        }
                        YieldOutcome::End
                    }
                    Mint::Backoff { state, until } => {
                        write_doc(&goal_draft, &stamp(state, now))?;
                        YieldOutcome::Wait { until }
                    }
                    Mint::Continue(state) => {
                        let written = stamp(state, now);
                        write_doc(&goal_draft, &written)?;
                        let (text, context) =
                            goal_context(&written, GoalContextKind::Continuation)?;
                        row = Some(context);
                        YieldOutcome::Continue { text }
                    }
                };
                loop_state.yield_record = Some(YieldRecord {
                    task_id,
                    outcome: outcome.clone(),
                });
                write_doc(&loop_draft, &loop_state)?;
                if let Some(row) = row {
                    tx.append_entry(conversation_id, row).await?;
                }
                Ok(outcome)
            },
            cx,
        )
        .await
}
