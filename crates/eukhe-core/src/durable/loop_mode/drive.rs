//! Carrying out the compiled core's answers: one commit per decision (the
//! event's facts in, the core's next state and act out, the state written
//! in that commit), the condition command, and the iteration's submission.
//!
//! Exactly once across a crash: the state of an iteration is written
//! before its prompt is sent; a prompt sent as a submission carries the
//! request id `loop:<loop>:<iteration>` (a second submit names the same
//! submission), and a prompt sent as the continuation of a final answer is
//! recorded with the answering generation task, so a rerun of that task
//! repeats the continuation instead of deciding again.

use std::sync::Arc;

use eukhe_bend::rules::loop_mode::{step, LoopAct, LoopEvent, TurnOutcome};
use eukhe_chord::context::Context;
use eukhe_durable::harness::types::{InputSubmissionDraft, WhenBusy};
use eukhe_durable::harness::{Conversation, Harness, LIVE_DOC};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::{ConversationId, TaskId};
use eukhe_types::input_origin::InputOrigin;
use eukhe_types::loop_mode::{LoopCondition, LoopEnd, LoopEvidence, LoopLimit, LoopPhase};
use eukhe_types::pi_ai::UserContent;
use serde_json::json;

use super::args::{enabled_message, end_message, CONDITION_TIMEOUT_MS};
use super::docs::{LoopDoc, LoopYield, LOOP_MODE_DOC};
use super::LOOP_NOTICE_CUSTOM_TYPE;
use crate::autonomous::{now_millis, GateCommandRunner};
use crate::durable::children::has_unsettled_children;
use crate::durable::entries::custom_entry_draft;
use crate::durable::goals::{conversation_of, open_doc, read_doc, user_input_queued, write_doc};
use crate::durable::workflow::unsettled_runs;
use crate::durable::HarnessCell;

/// The services of the loop: the session's Harness, the runner of the
/// condition command (in the session cwd), and whether the budget funds
/// one more turn (blocking: ledger file IO).
#[derive(Clone)]
pub(crate) struct LoopHost {
    pub(crate) harness: HarnessCell,
    pub(crate) gates: Arc<dyn GateCommandRunner>,
    pub(crate) funded: Arc<dyn Fn() -> bool + Send + Sync>,
}

/// Where a decision is carried out.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Mode {
    /// At the final answer of this generation task: an iteration starts as
    /// the answer's continuation.
    Yield(TaskId),
    /// Outside a run: an iteration starts as a submission.
    Idle,
}

/// What happened, before the facts the commit adds (the clock, the
/// iteration the state names).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Input {
    Enter {
        limit: Option<LoopLimit>,
        condition: Option<LoopCondition>,
        prompt: Option<String>,
    },
    Stop,
    Abort,
    Prompt {
        text: String,
    },
    /// The turn in flight settled.
    TurnSettled(TurnOutcome),
    Judged {
        iteration: u64,
        evidence: LoopEvidence,
        output: String,
    },
    /// Take up the pending work.
    TakeUp,
}

/// The facts of one decision that Rust gathers outside the commit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Facts {
    /// The session is not idle: queued user input, unsettled children or
    /// workflow runs, or (outside a run) a run in flight.
    pub(crate) blocked: bool,
    /// The budget funds one more turn.
    pub(crate) funded: bool,
}

pub(crate) fn core_error(error: &eukhe_bend::Error) -> SessionError {
    SessionError::error(format!("the loop's decision failed: {error}"))
}

/// The display row of a loop's end.
fn notice_row(
    text: String,
    end: LoopEnd,
    timestamp: u64,
) -> SessionResult<eukhe_durable::types::EntryDraft> {
    Ok(custom_entry_draft(
        LOOP_NOTICE_CUSTOM_TYPE,
        UserContent::Text(text),
        true,
        Some(json!({ "end": end.slug() })),
        timestamp,
    )?)
}

/// One decision in one commit: the event built from `input`, `facts` and
/// the stored state goes to the compiled core; its next state and what
/// Rust keeps beside it are written; a reported end appends its display
/// row when `notice` (a command reports its own). Returns the written
/// document and the core's act.
///
/// # Errors
///
/// The core's refusal (a number past the wire), or commit failures.
pub(crate) async fn decide(
    conversation: &Conversation,
    input: Input,
    facts: Facts,
    mode: Mode,
    notice: bool,
    cx: &Context,
) -> SessionResult<(LoopDoc, LoopAct)> {
    let conversation_id = conversation.id();
    conversation
        .commit(
            move |tx| async move {
                let now = now_millis();
                let (draft, before) = open_doc(&tx, &LOOP_MODE_DOC, conversation_id).await?;
                let mut doc = before.clone();
                let mut started = None;
                let event = match input {
                    Input::Enter {
                        limit,
                        condition,
                        prompt,
                    } => {
                        started = Some(limit);
                        LoopEvent::Enter {
                            limit,
                            condition,
                            prompt,
                            now_ms: now,
                        }
                    }
                    Input::Stop => LoopEvent::Stop,
                    Input::Abort => LoopEvent::Abort,
                    Input::Prompt { text } => LoopEvent::Prompt { text },
                    Input::TurnSettled(outcome) => match before.state.phase {
                        LoopPhase::Turn => LoopEvent::Settled {
                            iteration: before.state.iteration,
                            outcome,
                            blocked: facts.blocked,
                            now_ms: now,
                            funded: facts.funded,
                        },
                        // The turn settled before and its check never
                        // answered: take the check up.
                        LoopPhase::Judging => LoopEvent::Restart,
                        LoopPhase::Off
                        | LoopPhase::Armed
                        | LoopPhase::Paused
                        | LoopPhase::Ended { .. } => return Ok((before, LoopAct::Rest)),
                    },
                    Input::Judged {
                        iteration,
                        evidence,
                        output,
                    } => {
                        doc.check_output = (!output.trim().is_empty()).then_some(output);
                        LoopEvent::Judged {
                            iteration,
                            evidence,
                            blocked: facts.blocked,
                            now_ms: now,
                            funded: facts.funded,
                        }
                    }
                    Input::TakeUp => LoopEvent::Restart,
                };
                let (next, act) = step(&before.state, &event).map_err(|e| core_error(&e))?;
                doc.state = next;
                if let (Some(limit), false) = (started, before.state.phase.is_on()) {
                    // A new loop: nothing of the last one stays.
                    doc = LoopDoc {
                        state: doc.state,
                        loop_id: Some(format!("{now:x}")),
                        limit,
                        started_at_ms: Some(now),
                        ..LoopDoc::default()
                    };
                    doc.message = Some(enabled_message(&doc));
                }
                let waits = matches!(doc.state.phase, LoopPhase::Armed | LoopPhase::Paused);
                if waits && doc.state.phase != before.state.phase {
                    doc.waiting_since_ms = Some(now);
                }
                match &act {
                    LoopAct::Report(end) => {
                        let text = end_message(&doc, *end);
                        doc.message = Some(text.clone());
                        doc.yield_record = None;
                        doc.held = false;
                        if notice {
                            tx.append_entry(conversation_id, notice_row(text, *end, now)?)
                                .await?;
                        }
                    }
                    LoopAct::Submit { iteration, .. } => {
                        doc.yield_record = match mode {
                            Mode::Yield(task_id) => Some(LoopYield {
                                task_id,
                                iteration: *iteration,
                            }),
                            Mode::Idle => None,
                        };
                    }
                    LoopAct::Adopt { iteration } => {
                        doc.adopted = Some(*iteration);
                        doc.waiting_since_ms = None;
                    }
                    LoopAct::Rest
                    | LoopAct::Judge { .. }
                    | LoopAct::Resume { .. }
                    | LoopAct::Defer => {}
                }
                if doc != before {
                    write_doc(&draft, &doc)?;
                }
                Ok((doc, act))
            },
            cx,
        )
        .await
}

impl LoopHost {
    /// The conversation `conversation_id` of the open Harness.
    pub(crate) async fn conversation(
        &self,
        conversation_id: ConversationId,
        cx: &Context,
    ) -> SessionResult<Conversation> {
        conversation_of(&self.harness.require()?, conversation_id, cx).await
    }

    /// The facts of a decision in `mode` on `conversation_id`.
    pub(crate) async fn facts(
        &self,
        harness: &Harness,
        conversation_id: ConversationId,
        mode: Mode,
        cx: &Context,
    ) -> SessionResult<Facts> {
        let mut blocked = user_input_queued(harness, conversation_id, cx).await?
            || has_unsettled_children(harness, conversation_id, cx).await?
            || unsettled_runs(harness, conversation_id, cx).await?.count > 0;
        if mode == Mode::Idle && !blocked {
            blocked = read_doc(harness, &LIVE_DOC, conversation_id, cx)
                .await?
                .is_some_and(|live| live.run.is_some());
        }
        let funded = Arc::clone(&self.funded);
        let funded = tokio::task::spawn_blocking(move || funded())
            .await
            .map_err(SessionError::other)?;
        Ok(Facts { blocked, funded })
    }

    /// Run the condition command once and read its evidence: the exit
    /// status, never the output.
    async fn check(&self, condition: &LoopCondition) -> (LoopEvidence, String) {
        match self
            .gates
            .run_gate(&condition.command, CONDITION_TIMEOUT_MS)
            .await
        {
            Err(error) => (LoopEvidence::SpawnFailed, format!("{error:#}")),
            Ok(run) if run.timed_out => (LoopEvidence::TimedOut, String::new()),
            Ok(run) => {
                let output = if run.stdout.trim().is_empty() {
                    run.stderr
                } else {
                    run.stdout
                };
                match run.status.and_then(|code| u64::try_from(code).ok()) {
                    Some(code) => (LoopEvidence::Exited { code }, output),
                    None => (LoopEvidence::NoStatus, output),
                }
            }
        }
    }

    /// Send iteration `iteration` as a submission of `doc`'s loop: the
    /// request id names it, so a second send queues nothing. Returns
    /// whether that submission is already settled (its turn is over).
    async fn send(
        &self,
        conversation: &Conversation,
        doc: &LoopDoc,
        iteration: u64,
        text: String,
        cx: &Context,
    ) -> SessionResult<bool> {
        let loop_id = doc.loop_id.as_deref().unwrap_or("0");
        let request_id = if doc.resends == 0 {
            format!("loop:{loop_id}:{iteration}")
        } else {
            format!("loop:{loop_id}:{iteration}:{}", doc.resends)
        };
        let submission = conversation
            .submit(
                InputSubmissionDraft {
                    request_id: Some(request_id),
                    content: UserContent::Text(text),
                    when_busy: Some(WhenBusy::FollowUp),
                    origin: InputOrigin::Loop { iteration },
                    entry: None,
                },
                cx,
            )
            .await?;
        Ok(submission.status(cx).await?.state.is_settled())
    }

    /// Decide on `input`, then carry out every act it leads to: run the
    /// condition command and decide on its evidence, start the next
    /// iteration (as the continuation this returns in [`Mode::Yield`], as
    /// a submission in [`Mode::Idle`]), or take up a turn in flight.
    ///
    /// # Errors
    ///
    /// Read, commit or submission failures.
    pub(crate) async fn drive(
        &self,
        conversation: &Conversation,
        mut input: Input,
        mode: Mode,
        cx: &Context,
    ) -> SessionResult<Option<(String, InputOrigin)>> {
        let harness = self.harness.require()?;
        loop {
            let facts = self.facts(&harness, conversation.id(), mode, cx).await?;
            let (doc, act) = decide(conversation, input, facts, mode, true, cx).await?;
            match act {
                LoopAct::Judge { iteration } => {
                    let (evidence, output) = match &doc.state.condition {
                        Some(condition) => self.check(condition).await,
                        None => (LoopEvidence::SpawnFailed, String::new()),
                    };
                    input = Input::Judged {
                        iteration,
                        evidence,
                        output,
                    };
                }
                LoopAct::Submit { iteration, text } => {
                    return match mode {
                        Mode::Yield(_) => Ok(Some((text, InputOrigin::Loop { iteration }))),
                        Mode::Idle => {
                            self.start(conversation, &doc, iteration, text, cx).await?;
                            Ok(None)
                        }
                    };
                }
                LoopAct::Resume { iteration, text } => {
                    if mode == Mode::Idle {
                        self.take_up_turn(conversation, &doc, iteration, text, cx)
                            .await?;
                    }
                    return Ok(None);
                }
                LoopAct::Rest | LoopAct::Adopt { .. } | LoopAct::Report(_) | LoopAct::Defer => {
                    return Ok(None);
                }
            }
        }
    }

    /// Start iteration `iteration` as a submission; a submission the
    /// session refuses pauses the loop.
    pub(crate) async fn start(
        &self,
        conversation: &Conversation,
        doc: &LoopDoc,
        iteration: u64,
        text: String,
        cx: &Context,
    ) -> SessionResult<()> {
        if let Err(error) = self.send(conversation, doc, iteration, text, cx).await {
            self.halt(conversation, cx).await?;
            return Err(error);
        }
        Ok(())
    }

    /// The turn in flight did not run to its end: the loop pauses.
    async fn halt(&self, conversation: &Conversation, cx: &Context) -> SessionResult<()> {
        let facts = Facts {
            blocked: false,
            funded: true,
        };
        decide(
            conversation,
            Input::TurnSettled(TurnOutcome::Halted),
            facts,
            Mode::Idle,
            true,
            cx,
        )
        .await?;
        Ok(())
    }

    /// Take up iteration `iteration`'s turn while nothing runs: a prompt
    /// that never was sent is sent; a turn whose prompt was sent (the
    /// user's own, a final answer's continuation, or a submission that
    /// already settled) is over without the loop being told, and the loop
    /// pauses.
    async fn take_up_turn(
        &self,
        conversation: &Conversation,
        doc: &LoopDoc,
        iteration: u64,
        text: String,
        cx: &Context,
    ) -> SessionResult<()> {
        let continued = doc
            .yield_record
            .is_some_and(|record| record.iteration == iteration);
        if continued || doc.adopted == Some(iteration) {
            return self.halt(conversation, cx).await;
        }
        if self.send(conversation, doc, iteration, text, cx).await? {
            return self.halt(conversation, cx).await;
        }
        Ok(())
    }
}
