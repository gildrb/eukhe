//! The autonomous extension's `pi.generation` hooks: the autonomous
//! continuation loop and the Director stack on the Harness.
//!
//! - `before_request`: forces the tool of the topmost forced-call Director
//!   the model did not call yet (`stream.forceTool`).
//! - `after_response`: counts the response to a forced request: a call of
//!   the tool makes the forced call; the miss that fails the generation
//!   removes the layer and records the failure in a display row.
//! - `on_yield`: at a final answer the Director stack decides
//!   (`crate::durable::directors`): an autonomous run asks the compiled
//!   core (`eukhe_bend::rules::autonomous`), from what the checks did with
//!   the answer, the session's budget and, for a claim that passed, the
//!   final-answer judge's reading (asked first, one request: a passing
//!   claim whose answer states work left goes on with that work), and each
//!   continuation it makes passes the run's progress check (`progress.rs`):
//!   continuations in a row with no new work are counted; at
//!   `directors.stallSteps` the continuation asks once for another
//!   approach, at twice that the run ends, not done, with a display row.
//!   Reminders lead the continuation, or stay on the stack when no
//!   continuation comes; a forced call not made yet continues the run
//!   forced. Queued user input and unsettled RLM children hold the
//!   continuation (the queued run or the child's report run reaches its
//!   own final answer). An aborted run never reaches `on_yield`.
//! - `on_truncated`: the display row of a final answer that hit the output
//!   limit and that the stop Directors kept as it is (`eukhe.output_limit`:
//!   the Harness's warning, shown after the answer, never model context).
//!
//! The autonomous run has no limit of its own: a budget the user set
//! (`crate::durable::budget`) is its only one. Every decision is recorded
//! in `eukhe.goal.loop` keyed by the generation task, in the same commit
//! as its autonomous and stack changes, so a rerun after a crash repeats
//! the decision.

use std::sync::Arc;

use eukhe_bend::rules::work_left::Reading;
use eukhe_chord::context::Context;
use eukhe_durable::harness::define::hook;
use eukhe_durable::harness::types::{
    GenerationHooks, HookApi, HookRegistration, RequestMessages, YieldContinuation,
};
use eukhe_durable::harness::{Conversation, ForcedToolError, GENERATION_TASK, LIVE_DOC};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::{EntryDraft, EntryId, SubmissionId, TaskId};
use eukhe_types::custom_type::OUTPUT_LIMIT_NOTICE_CUSTOM_TYPE;
use eukhe_types::input_origin::InputOrigin;
use eukhe_types::pi_ai::{AssistantContentBlock, AssistantMessage, StopReason, UserContent};
use futures::FutureExt;

use super::docs::{
    open_doc, read_doc, write_doc, RunProgress, YieldOutcome, YieldRecord, AUTONOMOUS_DOC, LOOP_DOC,
};
use super::host::AutonomousHost;
use super::ops::{budget_report, user_input_queued};
use super::run::{decide, AutonomousDocState, AutonomousYield};
use crate::autonomous::{no_progress_reason, now_millis, AutonomousStop, SessionBudget};
use crate::durable::acceptance::{checks_at, AnswerChecks};
use crate::durable::children::has_unsettled_children;
use crate::durable::directors::{
    compared, found_left, judge_answer, left_continuation, left_notice, newest_input, read_work,
    stall_check, DirectorLimits, DirectorState, End, Last, Layer, LayerKind, Loop, RunLoop, Stall,
    Verdict, DIRECTORS_DOC, DIRECTOR_NOTICE_CUSTOM_TYPE,
};
use crate::durable::entries::custom_entry_draft;
use crate::durable::workflow::unsettled_runs;

/// The autonomous extension's hook registration on `pi.generation`.
pub(crate) fn generation_hooks(host: &AutonomousHost) -> HookRegistration {
    let after = host.clone();
    let yielded = host.clone();
    hook(
        &*GENERATION_TASK,
        GenerationHooks {
            before_prepare: None,
            before_request: Some(Arc::new(move |request, api, cx| {
                let request = request.clone();
                let api = api.clone();
                let cx = cx.clone();
                async move {
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
                async move { host.mark_forced_response(&message, &api, &cx).await }.boxed()
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
            on_truncated: Some(Arc::new(|warning: &str, _: &HookApi, _: &Context| {
                let row = custom_entry_draft(
                    OUTPUT_LIMIT_NOTICE_CUSTOM_TYPE,
                    UserContent::Text(warning.to_owned()),
                    /*display*/ true,
                    None,
                    now_millis(),
                );
                async move { Ok(Some(row?)) }.boxed()
            })),
            after_tools: None,
            pending_work: None,
        },
    )
}

impl AutonomousHost {
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
        let autonomous = read_doc(api, &AUTONOMOUS_DOC, conversation_id, cx).await?;
        let mut state = read_doc(api, &DIRECTORS_DOC, conversation_id, cx)
            .await?
            .unwrap_or_default();
        let limits = (self.limits)();
        begin(
            &mut state,
            input,
            &autonomous
                .clone()
                .unwrap_or_else(AutonomousDocState::initial),
            limits,
        );
        if state.stack.is_empty() {
            // No Director: the loop hands back, and nothing is written.
            return Ok(None);
        }
        // The work the session did so far, for the run's progress check:
        // the cache reads the entries it did not read yet.
        let conversation = self.conversation(conversation_id, cx).await?;
        let work = read_work(&self.work, &conversation, cx).await?;
        // What the session's budget admits now, and what the checks did
        // with this answer (the verifier ran before this hook).
        let budget = SessionBudget::of(budget_report(&self.budget).await?.as_ref());
        let checks = checks_at(api, conversation_id, task_id, cx).await?;
        let (reading, left) = self
            .read_passing_claim(answer, autonomous.as_ref(), checks, budget, api, cx)
            .await?;
        let newest_input = newest_input(&conversation, cx).await?;
        let Step {
            continuation,
            abort,
        } = commit_step(
            &conversation,
            StepInput {
                task_id,
                input,
                seen: Seen { autonomous },
                answer: AnswerAt {
                    stop_reason: answer.stop_reason,
                    checks,
                    reading,
                    left,
                },
                limits,
                work,
                newest_input,
                session: SessionTerms { budget },
            },
            cx,
        )
        .await?;
        match abort {
            Some(error) => Err(SessionError::other(error)),
            None => Ok(continuation),
        }
    }

    /// The final-answer judge's reading of `answer` when the core asks for
    /// it (`autonomous_asks_iff`: a claim of the autonomous run that passed
    /// while the budget admits work), with the items it listed as left;
    /// else not read. One request, before the step's commit: the step
    /// decides with it.
    async fn read_passing_claim(
        &self,
        answer: &AssistantMessage,
        autonomous: Option<&AutonomousDocState>,
        checks: AnswerChecks,
        budget: SessionBudget,
        api: &HookApi,
        cx: &Context,
    ) -> SessionResult<(Reading, Vec<String>)> {
        let Some(autonomous) = autonomous else {
            return Ok((Reading::Unread, Vec::new()));
        };
        Ok(
            match decide(
                autonomous,
                answer.stop_reason,
                checks,
                budget.rule(),
                Reading::Unread,
            )? {
                AutonomousYield::Ask => {
                    judge_answer(&*self.judge, api.conversation_id(), answer, cx).await
                }
                AutonomousYield::Inactive
                | AutonomousYield::Continue { .. }
                | AutonomousYield::Stop { .. }
                | AutonomousYield::Finish { .. } => (Reading::Unread, Vec::new()),
            },
        )
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
                        LayerKind::Autonomous | LayerKind::Reminder { .. } => None,
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

/// The autonomous document as the step read it before its commit
/// (`None`: absent; the commit does not create it).
#[derive(Debug, Clone)]
struct Seen {
    autonomous: Option<AutonomousDocState>,
}

/// The session's budget as a step sees it: what it admits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct SessionTerms {
    budget: SessionBudget,
}

/// The verdicts of one step, top layer first, and what they write.
#[derive(Debug, Default, PartialEq)]
struct Pass {
    verdicts: Vec<Verdict>,
    /// The reminders' texts, top first: they lead the continuation.
    reminders: Vec<String>,
    /// The continuation of the layer that said Again.
    continuation: Option<(String, InputOrigin)>,
    /// Written when the loop goes on: the autonomous run after its
    /// continuation.
    autonomous_continued: Option<AutonomousDocState>,
    /// Appended when the loop goes on: the display row that tells the user
    /// the autonomous run went on with the work its answer left.
    left_row: Option<EntryDraft>,
    /// Written whatever the loop does: the stopped autonomous run.
    autonomous_stopped: Option<AutonomousDocState>,
    /// The forced call whose layer aborted.
    abort: Option<ForcedToolError>,
    /// Written whatever the loop does: the verdict of the run's progress
    /// check, when the run would continue.
    stall: Option<Stall>,
    /// Written whatever the loop does: the display row of a run the
    /// progress check ended.
    notice: Option<EntryDraft>,
}

/// The run's progress check at a step: its verdict, and the count of
/// continuations in a row with no new work that steers the run
/// (`directors.stallSteps`; twice it ends the run not done).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RunCheck {
    stall: Stall,
    cap: u64,
}

/// The run's progress check at a continuation of the run whose first
/// input is `input`, the session's work being `work` now. The first check
/// of a run has nothing to compare with: it starts the count.
fn run_check(
    prior: Option<&RunProgress>,
    input: Option<SubmissionId>,
    work: u64,
    cap: u64,
) -> RunCheck {
    let last = prior.map(|prior| Last {
        same_run: prior.input == input,
        stalls: prior.stalls,
        work: prior.work,
    });
    RunCheck {
        stall: stall_check(cap, compared(last), work),
        cap,
    }
}

/// What the model reads after an autonomous continuation the progress
/// check let go on with stalls: the count, and at the cap the request to
/// change approach; nothing without a stall.
fn stall_note(check: RunCheck) -> Option<String> {
    let end = check.cap.saturating_mul(2);
    match check.stall {
        Stall::Go { stalls: 0 } | Stall::Stop { .. } => None,
        Stall::Go { stalls } => Some(format!(
            "[autonomous: no progress] {stalls} autonomous continuations in a row made no tool call with a new result. Take one concrete step that changes something now. At {end} in a row the run ends, not done."
        )),
        Stall::Steer { stalls } => Some(format!(
            "[autonomous: change approach] {stalls} autonomous continuations in a row made no tool call with a new result: the current approach is not working. Change it: try another method, use a read-only helper to investigate, or re-plan the remaining work, then keep going. At {end} continuations in a row with no progress the run ends, not done."
        )),
    }
}

/// The display row of a run the progress check ended after `stalls`
/// continuations in a row with no new work.
fn no_progress_notice(stalls: u64, now: u64) -> SessionResult<EntryDraft> {
    Ok(custom_entry_draft(
        DIRECTOR_NOTICE_CUSTOM_TYPE,
        UserContent::Text(format!(
            "The autonomous run ended, not done: {}.",
            no_progress_reason(stalls)
        )),
        true,
        Some(serde_json::json!({ "stop": "noProgress", "stalls": stalls })),
        now,
    )?)
}

/// What the step knows of the final answer: how it ended, what the checks
/// did with it, and the final-answer judge's reading of it with the items
/// it listed as left (read only for a claim of the autonomous run that
/// passed).
#[derive(Debug, Clone, PartialEq, Eq)]
struct AnswerAt {
    stop_reason: StopReason,
    checks: AnswerChecks,
    reading: Reading,
    left: Vec<String>,
}

/// Start a new loop when the stored one belongs to another run (its first
/// input differs) or ended, refreshing the autonomous budget (the run's
/// continuation steps); then put the autonomous run on the stack when it
/// drives continuations and has no layer yet. It goes below the pushed
/// layers (reminders and forced calls), so those decide first and a
/// reminder rides on its continuation. It always has room:
/// `directors.stackCap` caps the pushed layers only, and the stack keeps
/// its place ([`DirectorLimits::bound`]).
fn begin(
    state: &mut DirectorState,
    input: Option<SubmissionId>,
    autonomous: &AutonomousDocState,
    limits: DirectorLimits,
) {
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
                LayerKind::Autonomous => layer.budget = limits.max_steps,
                LayerKind::Reminder { .. } | LayerKind::ForceTool { .. } => {}
            }
        }
    }
    if autonomous.enabled
        && !state
            .stack
            .iter()
            .any(|layer| layer.kind == LayerKind::Autonomous)
    {
        let below_pushed = state
            .stack
            .iter()
            .position(|layer| layer.kind.is_pushed())
            .unwrap_or(state.stack.len());
        state.stack.insert(
            below_pushed,
            Layer {
                kind: LayerKind::Autonomous,
                budget: limits.max_steps,
            },
        );
    }
}

/// The verdict of each layer of `stack` (bottom first), top first, down to
/// the first one that decides (not Leave, not Lead), from the session
/// state:
/// - Autonomous: leaves when off; else the compiled core decides from the
///   checks' outcome at the answer, the budget and the final-answer
///   judge's reading: a continuation (Again: with its prompt, or with the
///   work the answer of a passing claim left) that the progress check
///   lets go on (at its cap asking for another approach), or Yield (the
///   checks' return continues the run, the run stopped, or the progress
///   check ended it not done).
/// - Reminder: its text leads the continuation (Lead): it leaves with the
///   continuation, and stays when the step ends the loop.
/// - `ForceTool`: leaves once the model called the tool; else Again while
///   it has budget (the continuation only names the forced call: the
///   forced request's soft prompt asks for it), then Abort.
fn judge(
    stack: &[Layer],
    autonomous: &AutonomousDocState,
    answer: &AnswerAt,
    check: RunCheck,
    session: SessionTerms,
    now: u64,
) -> SessionResult<Pass> {
    let mut pass = Pass::default();
    for layer in stack.iter().rev() {
        let verdict = match &layer.kind {
            LayerKind::Autonomous => {
                if autonomous.enabled {
                    autonomous_verdict(&mut pass, autonomous, answer, check, session, now)?
                } else {
                    Verdict::Leave
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
    Ok(pass)
}

/// The enabled autonomous run's verdict: the compiled core's step, and for
/// a continuation (with its prompt, or with the work the answer of a
/// passing claim left) the progress check's.
fn autonomous_verdict(
    pass: &mut Pass,
    autonomous: &AutonomousDocState,
    answer: &AnswerAt,
    check: RunCheck,
    session: SessionTerms,
    now: u64,
) -> SessionResult<Verdict> {
    let (text, origin, next, left_row) = match decide(
        autonomous,
        answer.stop_reason,
        answer.checks,
        session.budget.rule(),
        answer.reading,
    )? {
        // A reading not given (the run changed between the read and the
        // commit): the answer stands.
        AutonomousYield::Inactive | AutonomousYield::Ask => return Ok(Verdict::Yield),
        AutonomousYield::Stop { next, .. } => {
            pass.autonomous_stopped = Some(next);
            return Ok(Verdict::Yield);
        }
        AutonomousYield::Continue { text, nudge, next } => {
            (text, InputOrigin::Autonomous { nudge }, next, None)
        }
        AutonomousYield::Finish { next } => (
            left_continuation(&answer.left),
            InputOrigin::Director,
            next,
            Some(left_notice(&answer.left)?),
        ),
    };
    pass.stall = Some(check.stall);
    Ok(match check.stall {
        Stall::Stop { stalls } => {
            pass.autonomous_stopped = Some(AutonomousDocState {
                last_stop: Some(AutonomousStop::NoProgress { stalls }),
                ..autonomous.clone()
            });
            pass.notice = Some(no_progress_notice(stalls, now)?);
            Verdict::Yield
        }
        Stall::Go { .. } | Stall::Steer { .. } => {
            // The model reads why the next continuations count.
            let text = match stall_note(check) {
                Some(note) => format!("{text}\n\n{note}"),
                None => text,
            };
            pass.continuation = Some((text, origin));
            pass.autonomous_continued = Some(next);
            pass.left_row = left_row;
            Verdict::Again
        }
    })
}

/// What a step's commit works on.
#[derive(Debug)]
struct StepInput {
    task_id: TaskId,
    input: Option<SubmissionId>,
    seen: Seen,
    answer: AnswerAt,
    limits: DirectorLimits,
    /// The session's work now (`WorkLedger::count`).
    work: u64,
    /// The conversation's newest input entry now.
    newest_input: Option<EntryId>,
    /// The session's budget at the step.
    session: SessionTerms,
}

/// What a step's commit did: the continuation, and the forced call that
/// failed the loop.
#[derive(Debug)]
struct Step {
    continuation: Option<(String, InputOrigin)>,
    abort: Option<ForcedToolError>,
}

/// One step of the loop in one commit: judge the stack on the committed
/// state, tick the loop, and write the stack, what the run found left of
/// its task, the autonomous changes, the run's progress check (and the
/// notice of a run it ended), and the decision for `task_id` (a rerun
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
                    answer,
                    limits,
                    work,
                    newest_input,
                    session,
                } = step;
                let now = now_millis();
                let (loop_draft, mut loop_state) =
                    open_doc(&tx, &LOOP_DOC, conversation_id).await?;
                let autonomous = match seen.autonomous {
                    Some(_) => Some(open_doc(&tx, &AUTONOMOUS_DOC, conversation_id).await?),
                    None => None,
                };
                let (directors_draft, mut state) =
                    open_doc(&tx, &DIRECTORS_DOC, conversation_id).await?;
                let autonomous_state = autonomous
                    .as_ref()
                    .map_or_else(AutonomousDocState::initial, |(_, state)| state.clone());
                begin(&mut state, input, &autonomous_state, limits);
                let check = run_check(
                    loop_state.progress.as_ref(),
                    input,
                    work,
                    limits.stall_steps,
                );
                let pass = judge(
                    &state.stack,
                    &autonomous_state,
                    &answer,
                    check,
                    session,
                    now,
                )?;
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
                // What the run found left: the work the judge read in its
                // answer, or why the progress check ended it.
                let no_progress = match pass.stall {
                    Some(Stall::Stop { stalls }) => Some(no_progress_reason(stalls)),
                    Some(Stall::Go { .. } | Stall::Steer { .. }) | None => None,
                };
                state.found_left = found_left(
                    state.found_left.as_ref(),
                    input,
                    no_progress,
                    answer.reading,
                    &answer.left,
                    newest_input,
                );
                write_doc(&directors_draft, &state)?;
                if let (Some(stopped), Some((draft, _))) = (pass.autonomous_stopped, &autonomous) {
                    write_doc(draft, &stopped)?;
                }
                if let Some(stall) = pass.stall {
                    loop_state.progress = Some(RunProgress {
                        input,
                        work,
                        stalls: stall.stalls(),
                    });
                }
                let mut left_row = None;
                let outcome = match (ticked.end, pass.continuation) {
                    (None, Some((text, origin))) => {
                        if let (Some(continued), Some((draft, _))) =
                            (pass.autonomous_continued, &autonomous)
                        {
                            write_doc(draft, &continued)?;
                        }
                        left_row = pass.left_row;
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
                if let Some(left_row) = left_row {
                    tx.append_entry(conversation_id, left_row).await?;
                }
                if let Some(notice) = pass.notice {
                    tx.append_entry(conversation_id, notice).await?;
                }
                let abort = pass.abort.filter(|_| ticked.end == Some(End::Failed));
                if let Some(error) = &abort {
                    tx.append_entry(conversation_id, forced_call_failure(error)?)
                        .await?;
                }
                Ok(Step {
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

    /// The session terms of a budget that admits work.
    fn working() -> SessionTerms {
        SessionTerms {
            budget: SessionBudget::Working,
        }
    }

    fn check(stall: Stall) -> RunCheck {
        RunCheck {
            stall,
            cap: crate::durable::directors::DEFAULT_STALL_STEPS,
        }
    }

    /// A settled final answer without checks.
    fn answer() -> AnswerAt {
        AnswerAt {
            stop_reason: StopReason::Stop,
            checks: AnswerChecks::Unchecked,
            reading: Reading::Unread,
            left: Vec::new(),
        }
    }

    /// `judge` of `stack` with no autonomous run.
    fn judged(stack: &[Layer]) -> Pass {
        judge(
            stack,
            &AutonomousDocState::initial(),
            &answer(),
            check(Stall::Go { stalls: 0 }),
            working(),
            0,
        )
        .expect("judge")
    }

    #[test]
    fn a_forced_call_not_made_continues_while_it_has_budget_then_aborts() {
        assert_eq!(
            judged(&[forced(false, 1, 0)]),
            Pass {
                verdicts: vec![Verdict::Again],
                continuation: Some((
                    "[director: forced call to `lookup`]".to_owned(),
                    InputOrigin::Director,
                )),
                ..Pass::default()
            }
        );
        // The error counts the forced requests that missed the call.
        assert_eq!(
            judged(&[forced(false, 0, 2)]),
            Pass {
                verdicts: vec![Verdict::Abort],
                abort: Some(ForcedToolError::NotCalled {
                    tool: "lookup".to_owned(),
                    attempts: 2,
                }),
                ..Pass::default()
            }
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
            Pass {
                verdicts: vec![Verdict::Lead, Verdict::Leave, Verdict::Abort],
                reminders: vec!["Run the tests.".to_owned()],
                abort: Some(ForcedToolError::NotCalled {
                    tool: "lookup".to_owned(),
                    attempts: 2,
                }),
                ..Pass::default()
            }
        );
    }

    fn running() -> AutonomousDocState {
        AutonomousDocState {
            enabled: true,
            ..AutonomousDocState::initial()
        }
    }

    fn autonomous_stack() -> [Layer; 1] {
        [Layer {
            kind: LayerKind::Autonomous,
            budget: 3,
        }]
    }

    /// An autonomous run: without checks it continues with its prompt; a
    /// claim the checks returned yields to their return, adding nothing;
    /// a claim that ended stops the run with its label.
    #[test]
    fn the_autonomous_layer_follows_the_core() {
        let run = running();
        let stack = autonomous_stack();
        let at = |checks| {
            judge(
                &stack,
                &run,
                &AnswerAt {
                    stop_reason: StopReason::Stop,
                    checks,
                    reading: Reading::Unread,
                    left: Vec::new(),
                },
                check(Stall::Go { stalls: 0 }),
                working(),
                0,
            )
            .expect("judge")
        };
        let stop = AutonomousStop::Checks(eukhe_types::acceptance::AcceptanceLabel::Failed);
        assert_eq!(
            [
                at(AnswerChecks::Unchecked),
                at(AnswerChecks::Returned),
                at(AnswerChecks::Ended(
                    eukhe_types::acceptance::AcceptanceLabel::Failed
                )),
            ],
            [
                Pass {
                    verdicts: vec![Verdict::Again],
                    continuation: Some((
                        crate::autonomous::autonomous_continuation_text(&run.continuation_prompt),
                        InputOrigin::Autonomous {
                            nudge: eukhe_types::input_origin::AutonomousNudge::Continuation,
                        },
                    )),
                    autonomous_continued: Some(AutonomousDocState {
                        continuations_used: 1,
                        ..run.clone()
                    }),
                    stall: Some(Stall::Go { stalls: 0 }),
                    ..Pass::default()
                },
                Pass {
                    verdicts: vec![Verdict::Yield],
                    ..Pass::default()
                },
                Pass {
                    verdicts: vec![Verdict::Yield],
                    autonomous_stopped: Some(AutonomousDocState {
                        last_stop: Some(stop),
                        ..run.clone()
                    }),
                    ..Pass::default()
                },
            ]
        );
    }

    /// The progress check's verdict reaches the autonomous continuation:
    /// a stalled one carries the count, the cap asks once for another
    /// approach and goes on, and twice the cap ends the run not done with
    /// its display row; nothing waits for anyone.
    #[test]
    fn a_stalled_autonomous_run_is_steered_then_ends_not_done() {
        let run = running();
        let stack = autonomous_stack();
        let at = |stall| judge(&stack, &run, &answer(), check(stall), working(), 7).expect("judge");
        let prompt = crate::autonomous::autonomous_continuation_text(&run.continuation_prompt);
        let continuation = |stalls| match at(Stall::Go { stalls }).continuation {
            Some((text, _)) => text,
            None => panic!("a continuation"),
        };
        assert_eq!(continuation(0), prompt);
        assert_eq!(
            continuation(2),
            format!("{prompt}\n\n[autonomous: no progress] 2 autonomous continuations in a row made no tool call with a new result. Take one concrete step that changes something now. At 6 in a row the run ends, not done.")
        );
        let steered = at(Stall::Steer { stalls: 3 });
        assert_eq!(
            (steered.verdicts, steered.continuation.map(|(text, _)| text)),
            (
                vec![Verdict::Again],
                Some(format!("{prompt}\n\n[autonomous: change approach] 3 autonomous continuations in a row made no tool call with a new result: the current approach is not working. Change it: try another method, use a read-only helper to investigate, or re-plan the remaining work, then keep going. At 6 continuations in a row with no progress the run ends, not done."))
            )
        );
        assert_eq!(
            at(Stall::Stop { stalls: 6 }),
            Pass {
                verdicts: vec![Verdict::Yield],
                autonomous_stopped: Some(AutonomousDocState {
                    last_stop: Some(AutonomousStop::NoProgress { stalls: 6 }),
                    ..run.clone()
                }),
                stall: Some(Stall::Stop { stalls: 6 }),
                notice: Some(no_progress_notice(6, 7).expect("row")),
                ..Pass::default()
            }
        );
    }
}
