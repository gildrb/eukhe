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
//! - `before_request`: also forces the tool of the topmost forced-call
//!   Director the model did not call yet (`stream.forceTool`).
//! - `after_response`: also counts the response to a forced request: a
//!   call of the tool makes the forced call; the miss that fails the
//!   generation removes the layer and records the failure in a display row.
//! - `on_yield`: at a final answer the Director stack decides
//!   (`crate::durable::directors`): an active goal mints one continuation;
//!   otherwise an enabled autonomous run consults its gates and limits;
//!   reminders lead the continuation, or stay on the stack when no
//!   continuation comes; a forced call not made yet continues the run
//!   forced. Queued user input and unsettled RLM children hold the
//!   continuation (the queued run or the child's report run reaches its
//!   own final answer). An aborted run never reaches `on_yield`.
//!
//! Every decision is recorded in `eukhe.goal.loop` keyed by the generation
//! task, in the same commit as its goal, autonomous and stack changes, so a
//! rerun after a crash repeats the decision instead of charging the goal
//! twice.

use std::sync::{Arc, PoisonError};

use eukhe_chord::context::Context;
use eukhe_durable::entries::ASSISTANT_ENTRY;
use eukhe_durable::harness::define::hook;
use eukhe_durable::harness::types::{
    GenerationHooks, HookApi, HookRegistration, RequestMessages, WhenBusy, YieldContinuation,
};
use eukhe_durable::harness::{
    Conversation, ConversationEntryQuery, ForcedToolError, GENERATION_TASK, LIVE_DOC,
};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::{EntryDraft, EntryRecord, ScanOrder, SubmissionId, TaskId};
use eukhe_types::input_origin::InputOrigin;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, Message, StopReason, UserContent,
};
use futures::FutureExt;

use super::autonomous::{decide, AutonomousDocState, AutonomousYield};
use super::docs::{
    open_doc, read_doc, write_doc, GoalProgress, YieldOutcome, YieldRecord, AUTONOMOUS_DOC,
    GOAL_DOC, LOOP_DOC,
};
use super::host::GoalsHost;
use super::ops::{goal_context, submit_goal_context, user_input_queued};
use super::state::{
    accounted, failed, mint, owns_continuation_wakeup, paused, served, spends_budget, stall_check,
    stamp, terminal_provider_failure, Prior, Stall, UsageOutcome,
};
use crate::autonomous::{now_millis, AutonomousRuntimeState};
use crate::durable::children::{has_unsettled_children, WorkLedger};
use crate::durable::directors::{
    DirectorLimits, DirectorState, End, Layer, LayerKind, Loop, RunLoop, Verdict, DIRECTORS_DOC,
    DIRECTOR_NOTICE_CUSTOM_TYPE,
};
use crate::durable::entries::custom_entry_draft;
use crate::durable::workflow::unsettled_runs;
use crate::goals::{GoalContextKind, GoalState, GoalStatus};

#[cfg(test)]
mod bridge;

/// How many of the newest entries the failed-run check reads.
const RECENT_ENTRIES: usize = 16;

/// How many entries one read of the goal's progress check takes.
const WORK_PAGE: usize = 256;

/// The goal extension's hook registration on `pi.generation`.
pub(crate) fn generation_hooks(host: &GoalsHost) -> HookRegistration {
    let before = host.clone();
    let after = host.clone();
    let yielded = host.clone();
    hook(
        &*GENERATION_TASK,
        GenerationHooks {
            before_request: Some(Arc::new(move |request, api, cx| {
                let host = before.clone();
                let request = request.clone();
                let api = api.clone();
                let cx = cx.clone();
                async move {
                    host.settle_failed_run(&api, &cx).await?;
                    let forced = read_doc(&api, &DIRECTORS_DOC, api.conversation_id(), &cx)
                        .await?
                        .and_then(|state: DirectorState| state.forced_tool());
                    Ok(forced.map(|force_tool| RequestMessages {
                        messages: request.messages,
                        force_tool: Some(force_tool),
                    }))
                }
                .boxed()
            })),
            after_response: Some(Arc::new(move |message, api, cx| {
                let host = after.clone();
                let message = message.clone();
                let api = api.clone();
                let cx = cx.clone();
                async move {
                    host.account_response(&message, &api, &cx).await?;
                    host.mark_forced_response(&message, &api, &cx).await
                }
                .boxed()
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
                        .map(|(text, origin)| YieldContinuation {
                            r#continue: UserContent::Text(text),
                            origin,
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
                    GoalContextKind::BudgetLimit,
                    text,
                    WhenBusy::Steer,
                    cx,
                )
                .await?;
            }
        }
        Ok(())
    }

    /// The Director stack's step at a final answer; `Some` continues the
    /// run with that user text and origin.
    #[tracing::instrument(skip_all)]
    async fn on_yield(
        &self,
        answer: &AssistantMessage,
        api: &HookApi,
        cx: &Context,
    ) -> SessionResult<Option<(String, InputOrigin)>> {
        let conversation_id = api.conversation_id();
        let task_id = api.task_id();
        let loop_state = read_doc(api, &LOOP_DOC, conversation_id, cx)
            .await?
            .unwrap_or_default();
        let recorded = loop_state
            .yield_record
            .filter(|record| record.task_id == task_id);
        if let Some(record) = recorded {
            return Ok(match record.outcome {
                YieldOutcome::Continue { text, origin } => Some((text, origin)),
                YieldOutcome::End => None,
            });
        }
        // Queued user input owns the boundary; unsettled children and
        // workflow runs hold the continuation until their report run.
        if user_input_queued(api, conversation_id, cx).await?
            || has_unsettled_children(api, conversation_id, cx).await?
            || unsettled_runs(api, conversation_id, cx).await?.count > 0
        {
            return Ok(None);
        }
        let input = read_doc(api, &LIVE_DOC, conversation_id, cx)
            .await?
            .and_then(|live| live.run)
            .and_then(|run| run.inputs.first().copied());
        // The work the session did so far, for the goal's progress check:
        // the cache reads the entries it did not read yet.
        let conversation = self.conversation(conversation_id, cx).await?;
        let read = self
            .work
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .get(&conversation_id)
            .and_then(WorkLedger::last);
        let mut cursor = None;
        let work = loop {
            let page = conversation
                .entries(
                    ConversationEntryQuery {
                        min_entry_id: read,
                        max_entry_id: None,
                        order: Some(ScanOrder::Ascending),
                    },
                    WORK_PAGE,
                    cursor,
                    cx,
                )
                .await?;
            let mut cache = self.work.lock().unwrap_or_else(PoisonError::into_inner);
            let ledger = cache.entry(conversation_id).or_default();
            for entry in &page.items {
                if ledger.last().is_none_or(|last| entry.id > last) {
                    ledger.read_entry(entry);
                }
            }
            match page.next {
                Some(next) => cursor = Some(next),
                None => break ledger.count(),
            }
        };
        let mut decided = None;
        loop {
            let limits = (self.limits)();
            let seen = Seen {
                goal: read_doc(api, &GOAL_DOC, conversation_id, cx).await?,
                autonomous: read_doc(api, &AUTONOMOUS_DOC, conversation_id, cx).await?,
            };
            let goal = seen.goal.clone().unwrap_or_default();
            let autonomous = seen
                .autonomous
                .clone()
                .unwrap_or_else(AutonomousDocState::initial);
            let mut state = read_doc(api, &DIRECTORS_DOC, conversation_id, cx)
                .await?
                .unwrap_or_default();
            begin(&mut state, input, &goal, &autonomous, limits);
            if state.stack.is_empty() {
                // No Director: the loop hands back, and nothing is written.
                return Ok(None);
            }
            if decided.is_none() {
                // The gates run outside the commit, when the step reaches
                // the autonomous run.
                let check = goal_check(
                    loop_state.progress.as_ref(),
                    input,
                    &goal,
                    work,
                    limits.stall_steps,
                );
                if let Judged::NeedAutonomous =
                    judge(&state.stack, &goal, &autonomous, None, check, now_millis())?
                {
                    let mut runtime = autonomous.to_runtime();
                    let decision =
                        decide(&mut runtime, answer.stop_reason, self.gates.as_ref()).await;
                    decided = Some(AutonomousDecided {
                        before: autonomous,
                        runtime,
                        decision,
                    });
                }
            }
            match commit_step(
                &conversation,
                StepInput {
                    task_id,
                    input,
                    seen,
                    decided: decided.clone(),
                    limits,
                    work,
                },
                cx,
            )
            .await?
            {
                Step::Retry => decided = None,
                Step::Done {
                    continuation,
                    abort,
                } => {
                    return match abort {
                        Some(error) => Err(SessionError::other(error)),
                        None => Ok(continuation),
                    };
                }
            }
        }
    }

    /// Count the response to a forced request for the layer that forced it
    /// (the topmost forced call not made yet): a call of its tool makes the
    /// call; a response without it is a miss. Only the responses that the
    /// generation judges count: a stop, a length cut, or tool use. The
    /// generation fails with [`ForcedToolError::NotCalled`] at the miss
    /// after the `tries` retries, so that miss removes the layer and
    /// appends the display row of the failure in one commit: the next
    /// request goes unforced.
    #[tracing::instrument(skip_all)]
    async fn mark_forced_response(
        &self,
        message: &AssistantMessage,
        api: &HookApi,
        cx: &Context,
    ) -> SessionResult<()> {
        match message.stop_reason {
            StopReason::Stop | StopReason::Length | StopReason::ToolUse => {}
            StopReason::Pending
            | StopReason::Error
            | StopReason::Aborted
            | StopReason::Deferred => return Ok(()),
        }
        let conversation_id = api.conversation_id();
        let forced = read_doc(api, &DIRECTORS_DOC, conversation_id, cx)
            .await?
            .and_then(|state| state.forced_tool());
        if forced.is_none() {
            return Ok(());
        }
        let calls: Vec<String> = message
            .content
            .iter()
            .filter_map(|block| match block {
                AssistantContentBlock::ToolCall(call) => Some(call.name.clone()),
                AssistantContentBlock::Text(_) | AssistantContentBlock::Thinking(_) => None,
            })
            .collect();
        self.conversation(conversation_id, cx)
            .await?
            .commit(
                move |tx| async move {
                    let (draft, mut state) = open_doc(&tx, &DIRECTORS_DOC, conversation_id).await?;
                    let Some(index) = state.stack.iter().rposition(|layer| {
                        matches!(layer.kind, LayerKind::ForceTool { called: false, .. })
                    }) else {
                        return Ok(());
                    };
                    let failed = match &mut state.stack[index].kind {
                        LayerKind::ForceTool {
                            tool,
                            tries,
                            called,
                            missed,
                        } => {
                            if calls.contains(tool) {
                                *called = true;
                                None
                            } else {
                                *missed += 1;
                                (*missed > *tries).then(|| ForcedToolError::NotCalled {
                                    tool: tool.clone(),
                                    attempts: *missed,
                                })
                            }
                        }
                        LayerKind::Goal | LayerKind::Autonomous | LayerKind::Reminder { .. } => {
                            None
                        }
                    };
                    if let Some(error) = failed {
                        state.stack.remove(index);
                        tx.append_entry(conversation_id, forced_call_failure(&error)?)
                            .await?;
                    }
                    write_doc(&draft, &state)
                },
                cx,
            )
            .await
    }
}

/// The autonomous decision of a step on the state `before`, made before
/// the step's commit (the gates run outside it).
#[derive(Debug, Clone)]
struct AutonomousDecided {
    before: AutonomousDocState,
    runtime: AutonomousRuntimeState,
    decision: AutonomousYield,
}

/// The goal and autonomous documents as the step read them before its
/// commit (`None`: absent; the commit does not create them).
#[derive(Debug, Clone)]
struct Seen {
    goal: Option<GoalState>,
    autonomous: Option<AutonomousDocState>,
}

/// The verdicts of one step, top layer first, and what they write.
#[derive(Debug, Default, PartialEq)]
struct Pass {
    verdicts: Vec<Verdict>,
    /// The reminders' texts, top first: they lead the continuation.
    reminders: Vec<String>,
    /// The continuation of the layer that said Again.
    continuation: Option<(String, InputOrigin)>,
    /// Written when the loop goes on: the goal's continuation slot and its
    /// context row.
    goal_slot: Option<(GoalState, EntryDraft)>,
    /// Written when the loop goes on: the autonomous run after its
    /// continuation.
    autonomous_continued: Option<AutonomousDocState>,
    /// Written whatever the loop does: the stopped autonomous run.
    autonomous_stopped: Option<AutonomousDocState>,
    /// The forced call whose layer aborted.
    abort: Option<ForcedToolError>,
    /// Written whatever the loop does: the verdict of the goal's progress
    /// check, when the active goal judged.
    goal_stall: Option<Stall>,
    /// Written whatever the loop does: the goal the progress check paused,
    /// and the notice row that tells the user why.
    goal_paused: Option<(GoalState, EntryDraft)>,
}

/// The goal's progress check at a step: its verdict, and the count of
/// continuations in a row with no new work that pauses the goal
/// (`directors.stallSteps`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct GoalCheck {
    stall: Stall,
    cap: u64,
}

/// The goal's progress check at a continuation of the run whose first
/// input is `input`, the session's work being `work` now. The first check
/// of a run or of a goal has nothing to compare with: it starts the count.
fn goal_check(
    prior: Option<&GoalProgress>,
    input: Option<SubmissionId>,
    goal: &GoalState,
    work: u64,
    cap: u64,
) -> GoalCheck {
    let prior = prior
        .filter(|prior| prior.input == input && prior.goal_id == goal.goal_id)
        .map(|prior| Prior {
            stalls: prior.stalls,
            work: prior.work,
        });
    GoalCheck {
        stall: stall_check(cap, prior, work),
        cap,
    }
}

/// The judgment of a step.
#[derive(Debug, PartialEq)]
enum Judged {
    Pass(Box<Pass>),
    /// The step reaches the autonomous run, whose gates did not run yet.
    NeedAutonomous,
}

/// Start a new loop when the stored one belongs to another run (its first
/// input differs) or ended, refreshing the goal and autonomous budgets;
/// then put the goal and the autonomous run on the stack (the goal above
/// the autonomous run) when they drive continuations and have no layer
/// yet. They go below the pushed layers (reminders and forced calls), so
/// those decide first and a reminder rides on their continuation. They
/// always have room: `directors.stackCap` caps the pushed layers only, and
/// the stack keeps one place for each of them ([`DirectorLimits::bound`]).
fn begin(
    state: &mut DirectorState,
    input: Option<SubmissionId>,
    goal: &GoalState,
    autonomous: &AutonomousDocState,
    limits: DirectorLimits,
) {
    let remaining = autonomous
        .limits
        .max_continuations
        .saturating_sub(autonomous.continuations_used);
    let fresh = state
        .run
        .as_ref()
        .is_none_or(|run| run.input != input || run.end.is_some());
    if fresh {
        state.run = Some(RunLoop {
            input,
            left: limits.max_steps,
            end: None,
        });
        for layer in &mut state.stack {
            match layer.kind {
                LayerKind::Goal => layer.budget = limits.max_steps,
                LayerKind::Autonomous => layer.budget = remaining,
                LayerKind::Reminder { .. } | LayerKind::ForceTool { .. } => {}
            }
        }
    }
    let wanted = [
        (autonomous.enabled, LayerKind::Autonomous, remaining),
        (
            owns_continuation_wakeup(goal),
            LayerKind::Goal,
            limits.max_steps,
        ),
    ];
    for (drives, kind, budget) in wanted {
        if drives && !state.stack.iter().any(|layer| layer.kind == kind) {
            let below_pushed = state
                .stack
                .iter()
                .position(|layer| layer.kind.is_pushed())
                .unwrap_or(state.stack.len());
            state.stack.insert(below_pushed, Layer { kind, budget });
        }
    }
}

/// The verdict of each layer of `stack` (bottom first), top first, down to
/// the first one that decides (not Defer, not Leave), from the session
/// state:
/// - Goal: an active goal mints a continuation (Again), or yields when its
///   progress check stops it (the goal pauses); a paused, budget-limited,
///   complete or failed goal yields; a cleared goal leaves.
/// - Autonomous: defers to a goal that drives continuations; leaves when
///   disabled; else its gates and limits continue (Again) or stop (Yield).
/// - Reminder: its text leads the continuation (Lead): it leaves with the
///   continuation, and stays when the step ends the loop.
/// - `ForceTool`: leaves once the model called the tool; else Again while
///   it has budget (the continuation only names the forced call: the
///   forced request's soft prompt asks for it), then Abort.
fn judge(
    stack: &[Layer],
    goal: &GoalState,
    autonomous: &AutonomousDocState,
    decided: Option<&AutonomousDecided>,
    check: GoalCheck,
    now: u64,
) -> SessionResult<Judged> {
    let mut pass = Pass::default();
    for layer in stack.iter().rev() {
        let verdict = match &layer.kind {
            LayerKind::Goal => match goal.status {
                GoalStatus::Active => match (check.stall, mint(goal)) {
                    // An active goal without an objective drives nothing.
                    (_, None) => Verdict::Leave,
                    (Stall::Stop { stalls }, Some(_)) => {
                        let reason = format!(
                            "No progress: {stalls} goal continuations in a row made no tool call with a new result"
                        );
                        if let Some(state) = paused(goal, &reason) {
                            let row = custom_entry_draft(
                                DIRECTOR_NOTICE_CUSTOM_TYPE,
                                UserContent::Text(format!(
                                    "The goal paused. {reason}. Change the plan or remove the blocker, then resume the goal."
                                )),
                                true,
                                Some(serde_json::json!({
                                    "goalId": goal.goal_id,
                                    "stalls": stalls,
                                })),
                                now,
                            )?;
                            pass.goal_paused = Some((stamp(state, now), row));
                        }
                        pass.goal_stall = Some(check.stall);
                        Verdict::Yield
                    }
                    (Stall::Go { stalls }, Some(state)) => {
                        let written = stamp(state, now);
                        let (text, row) = goal_context(&written, GoalContextKind::Continuation)?;
                        // The model reads why the next continuations count.
                        let text = if stalls == 0 {
                            text
                        } else {
                            format!(
                                "{text}\n\n[goal: no progress] {stalls} goal continuations in a row made no tool call with a new result. Take one concrete step that changes something now. If something blocks you, say what it is and stop: after {} continuations with no progress the goal pauses.",
                                check.cap
                            )
                        };
                        pass.continuation = Some((
                            text,
                            InputOrigin::Goal {
                                context: GoalContextKind::Continuation,
                            },
                        ));
                        pass.goal_slot = Some((written, row));
                        pass.goal_stall = Some(check.stall);
                        Verdict::Again
                    }
                },
                GoalStatus::Paused
                | GoalStatus::BudgetLimited
                | GoalStatus::Complete
                | GoalStatus::Error => Verdict::Yield,
                GoalStatus::Idle => Verdict::Leave,
            },
            LayerKind::Autonomous => {
                if owns_continuation_wakeup(goal) {
                    Verdict::Defer
                } else if !autonomous.enabled {
                    Verdict::Leave
                } else {
                    let Some(decided) = decided else {
                        return Ok(Judged::NeedAutonomous);
                    };
                    // An `/autonomous` change while the gates ran wins: the
                    // run yields.
                    if decided.before.started_at == autonomous.started_at {
                        match &decided.decision {
                            AutonomousYield::Inactive => Verdict::Yield,
                            AutonomousYield::Continue { text, nudge } => {
                                pass.continuation =
                                    Some((text.clone(), InputOrigin::Autonomous { nudge: *nudge }));
                                pass.autonomous_continued = Some(AutonomousDocState::from_runtime(
                                    &decided.runtime,
                                    autonomous.last_stop,
                                ));
                                Verdict::Again
                            }
                            AutonomousYield::Stop(stop) => {
                                pass.autonomous_stopped = Some(AutonomousDocState::from_runtime(
                                    &decided.runtime,
                                    Some(*stop),
                                ));
                                Verdict::Yield
                            }
                        }
                    } else {
                        Verdict::Yield
                    }
                }
            }
            LayerKind::Reminder { text } => {
                pass.reminders.push(text.clone());
                Verdict::Lead
            }
            LayerKind::ForceTool {
                tool,
                called,
                missed,
                ..
            } => {
                if *called {
                    Verdict::Leave
                } else if layer.budget > 0 {
                    pass.continuation = Some((
                        format!("[director: forced call to `{tool}`]"),
                        InputOrigin::Director,
                    ));
                    Verdict::Again
                } else {
                    pass.abort = Some(ForcedToolError::NotCalled {
                        tool: tool.clone(),
                        attempts: *missed,
                    });
                    Verdict::Abort
                }
            }
        };
        let decisive = !matches!(verdict, Verdict::Defer | Verdict::Leave | Verdict::Lead);
        pass.verdicts.push(verdict);
        if decisive {
            break;
        }
    }
    Ok(Judged::Pass(Box::new(pass)))
}

/// What a step's commit works on.
#[derive(Debug)]
struct StepInput {
    task_id: TaskId,
    input: Option<SubmissionId>,
    seen: Seen,
    decided: Option<AutonomousDecided>,
    limits: DirectorLimits,
    /// The session's work now ([`WorkLedger::count`]).
    work: u64,
}

/// What a step's commit did.
#[derive(Debug)]
enum Step {
    /// The step reaches the autonomous run, whose gates must run first.
    Retry,
    /// The step's decision: the continuation, and the forced call that
    /// failed the loop.
    Done {
        continuation: Option<(String, InputOrigin)>,
        abort: Option<ForcedToolError>,
    },
}

/// One step of the loop in one commit: judge the stack on the committed
/// state, tick the loop, and write the stack, the goal and autonomous
/// changes, the goal's context row, the goal's progress check (and the
/// notice of a goal it paused), and the decision for `task_id` (a rerun
/// repeats it).
#[tracing::instrument(skip_all)]
async fn commit_step(
    conversation: &Conversation,
    step: StepInput,
    cx: &Context,
) -> SessionResult<Step> {
    let conversation_id = conversation.id();
    conversation
        .commit(
            move |tx| async move {
                let StepInput {
                    task_id,
                    input,
                    seen,
                    decided,
                    limits,
                    work,
                } = step;
                let now = now_millis();
                let (loop_draft, mut loop_state) =
                    open_doc(&tx, &LOOP_DOC, conversation_id).await?;
                let goal = match seen.goal {
                    Some(_) => Some(open_doc(&tx, &GOAL_DOC, conversation_id).await?),
                    None => None,
                };
                let autonomous = match seen.autonomous {
                    Some(_) => Some(open_doc(&tx, &AUTONOMOUS_DOC, conversation_id).await?),
                    None => None,
                };
                let (directors_draft, mut state) =
                    open_doc(&tx, &DIRECTORS_DOC, conversation_id).await?;
                let goal_state = goal
                    .as_ref()
                    .map(|(_, goal)| goal.clone())
                    .unwrap_or_default();
                let autonomous_state = autonomous
                    .as_ref()
                    .map_or_else(AutonomousDocState::initial, |(_, state)| state.clone());
                begin(&mut state, input, &goal_state, &autonomous_state, limits);
                let check = goal_check(
                    loop_state.progress.as_ref(),
                    input,
                    &goal_state,
                    work,
                    limits.stall_steps,
                );
                let judged = judge(
                    &state.stack,
                    &goal_state,
                    &autonomous_state,
                    decided.as_ref(),
                    check,
                    now,
                )?;
                let pass = match judged {
                    Judged::NeedAutonomous => return Ok(Step::Retry),
                    Judged::Pass(pass) => *pass,
                };
                let left = state.run.as_ref().map_or(limits.max_steps, |run| run.left);
                let run = Loop {
                    left,
                    stack: std::mem::take(&mut state.stack),
                    end: None,
                };
                // A reminder leaves only with the continuation it leads
                // (`Verdict::Lead`): when the step ends the loop, it stays.
                let ticked = run.tick(&pass.verdicts, limits.bound());
                state.stack = ticked.stack;
                state.run = Some(RunLoop {
                    input,
                    left: ticked.left,
                    end: ticked.end,
                });
                write_doc(&directors_draft, &state)?;
                if let (Some(stopped), Some((draft, _))) = (pass.autonomous_stopped, &autonomous) {
                    write_doc(draft, &stopped)?;
                }
                if let Some(stall) = pass.goal_stall {
                    loop_state.progress = Some(GoalProgress {
                        input,
                        goal_id: goal_state.goal_id.clone(),
                        work,
                        stalls: match stall {
                            Stall::Go { stalls } | Stall::Stop { stalls } => stalls,
                        },
                    });
                }
                let mut notice = None;
                if let (Some((paused, row)), Some((draft, _))) = (pass.goal_paused, &goal) {
                    write_doc(draft, &paused)?;
                    notice = Some(row);
                }
                let mut row = None;
                let outcome = match (ticked.end, pass.continuation) {
                    (None, Some((text, origin))) => {
                        if let (Some((slot, context)), Some((draft, _))) = (pass.goal_slot, &goal) {
                            write_doc(draft, &slot)?;
                            row = Some(context);
                        }
                        if let (Some(continued), Some((draft, _))) =
                            (pass.autonomous_continued, &autonomous)
                        {
                            write_doc(draft, &continued)?;
                        }
                        let text = pass
                            .reminders
                            .into_iter()
                            .chain(std::iter::once(text))
                            .collect::<Vec<_>>()
                            .join("\n\n");
                        YieldOutcome::Continue { text, origin }
                    }
                    (None, None) | (Some(End::Hand | End::Failed), _) => YieldOutcome::End,
                };
                loop_state.yield_record = Some(YieldRecord {
                    task_id,
                    outcome: outcome.clone(),
                });
                write_doc(&loop_draft, &loop_state)?;
                if let Some(row) = row {
                    tx.append_entry(conversation_id, row).await?;
                }
                if let Some(notice) = notice {
                    tx.append_entry(conversation_id, notice).await?;
                }
                let abort = pass.abort.filter(|_| ticked.end == Some(End::Failed));
                if let Some(error) = &abort {
                    tx.append_entry(conversation_id, forced_call_failure(error)?)
                        .await?;
                }
                Ok(Step::Done {
                    continuation: match outcome {
                        YieldOutcome::Continue { text, origin } => Some((text, origin)),
                        YieldOutcome::End => None,
                    },
                    abort,
                })
            },
            cx,
        )
        .await
}

/// The display row of a forced call that failed: the user sees why the run
/// ended and that the forced call left the stack; the model does not.
fn forced_call_failure(error: &ForcedToolError) -> SessionResult<EntryDraft> {
    Ok(custom_entry_draft(
        DIRECTOR_NOTICE_CUSTOM_TYPE,
        UserContent::Text(format!("{error}. The forced call left the Director stack.")),
        true,
        Some(serde_json::to_value(error).map_err(SessionError::other)?),
        now_millis(),
    )?)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn forced(called: bool, budget: u64, missed: u32) -> Layer {
        Layer {
            kind: LayerKind::ForceTool {
                tool: "lookup".to_owned(),
                tries: 1,
                called,
                missed,
            },
            budget,
        }
    }

    /// `judge` of `stack` with no goal and no autonomous run.
    fn judged(stack: &[Layer]) -> Judged {
        judge(
            stack,
            &GoalState::default(),
            &AutonomousDocState::initial(),
            None,
            GoalCheck {
                stall: Stall::Go { stalls: 0 },
                cap: crate::durable::directors::DEFAULT_STALL_STEPS,
            },
            0,
        )
        .expect("judge")
    }

    #[test]
    fn a_forced_call_not_made_continues_while_it_has_budget_then_aborts() {
        assert_eq!(
            judged(&[forced(false, 1, 0)]),
            Judged::Pass(Box::new(Pass {
                verdicts: vec![Verdict::Again],
                continuation: Some((
                    "[director: forced call to `lookup`]".to_owned(),
                    InputOrigin::Director,
                )),
                ..Pass::default()
            }))
        );
        // The error counts the forced requests that missed the call.
        assert_eq!(
            judged(&[forced(false, 0, 2)]),
            Judged::Pass(Box::new(Pass {
                verdicts: vec![Verdict::Abort],
                abort: Some(ForcedToolError::NotCalled {
                    tool: "lookup".to_owned(),
                    attempts: 2,
                }),
                ..Pass::default()
            }))
        );
    }

    #[test]
    fn made_calls_and_reminders_leave_and_the_next_layer_decides() {
        let reminder = Layer {
            kind: LayerKind::Reminder {
                text: "Run the tests.".to_owned(),
            },
            budget: 0,
        };
        // Bottom first: the disabled autonomous run leaves too.
        let stack = [
            Layer {
                kind: LayerKind::Autonomous,
                budget: 3,
            },
            forced(false, 0, 2),
            forced(true, 1, 0),
            reminder,
        ];
        assert_eq!(
            judged(&stack),
            Judged::Pass(Box::new(Pass {
                verdicts: vec![Verdict::Lead, Verdict::Leave, Verdict::Abort],
                reminders: vec!["Run the tests.".to_owned()],
                abort: Some(ForcedToolError::NotCalled {
                    tool: "lookup".to_owned(),
                    attempts: 2,
                }),
                ..Pass::default()
            }))
        );
    }
}
