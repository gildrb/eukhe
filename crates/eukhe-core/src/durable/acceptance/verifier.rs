//! The verifier: at a final answer it judges the claim that the task is
//! done. It gathers the evidence of each acceptance check on the
//! conversation's state now, records each verdict, and lets the compiled
//! core (`eukhe_bend::rules::verify::advance`) decide the step: run the
//! next check, give the evidence back to the worker, or end the claim
//! verified, failed or unverified.
//!
//! - A session without a goal claims at every final answer; an active
//!   goal claims with `goal.complete()`, and its final answers before that
//!   are no claim.
//! - Queued user input, unsettled children and workflow runs, and jobs
//!   whose end wakes the session hold the verdict: the run they start
//!   reaches its own final answer.
//! - Every verdict is committed before the next step, with what the
//!   harness observed; the decision of a final answer is recorded by its
//!   generation task, so a rerun after a crash repeats it and a check
//!   whose verdict was not committed runs again.
//! - The worker's next effect clears the recorded end: the result has to
//!   be earned again on the new state. Until then a further final answer
//!   is no new claim: the verdict of that state stands.

use std::sync::{Arc, Weak};

use eukhe_bend::rules::verify::{self, Action, Actor, AnswerFacts, Op};
use eukhe_chord::context::Context;
use eukhe_durable::harness::define::hook;
use eukhe_durable::harness::types::{
    GenerationHooks, HookApi, HookRegistration, YieldContinuation,
};
use eukhe_durable::harness::{Conversation, GENERATION_TASK};
use eukhe_durable::session::SessionResult;
use eukhe_durable::types::{EntryDraft, TaskId};
use eukhe_types::acceptance::{
    AcceptanceCheck, AcceptanceEnd, AcceptanceLabel, CheckSpec, CheckVerdict,
};
use eukhe_types::input_origin::InputOrigin;
use eukhe_types::pi_ai::UserContent;
use futures::FutureExt;
use serde_json::json;

use super::docs::{AcceptanceDoc, YieldRecord, ACCEPTANCE_DOC};
use super::evidence::Gatherer;
use super::ops::{core_error, doc_state, label_of};
use super::ACCEPTANCE_CUSTOM_TYPE;
use crate::autonomous::now_millis;
use crate::durable::children::has_unsettled_children;
use crate::durable::entries::custom_entry_draft;
use crate::durable::goals::{
    conversation_of, end_claimed_goal, open_doc, owns_continuation_wakeup, read_doc,
    user_input_queued, write_doc, ClaimEnd, GOAL_DOC,
};
use crate::durable::pending::{pending_work, PendingWorkError};
use crate::durable::workflow::unsettled_runs;
use crate::durable::{HarnessCell, HostDeps};

/// The verifier of one session.
#[derive(Clone)]
pub(crate) struct Verifier {
    pub(crate) harness: HarnessCell,
    pub(crate) gatherer: Gatherer,
    /// The session's deps (held weakly: the deps hold the Harness that
    /// holds this hook), for the running work that holds a verdict: jobs
    /// whose end wakes the session. `None` for a Harness without them.
    pub(crate) deps: Option<Weak<HostDeps>>,
}

/// The verifier's `pi.generation` hooks.
pub(crate) fn generation_hooks(verifier: &Verifier) -> HookRegistration {
    let yielded = verifier.clone();
    let effects = verifier.clone();
    hook(
        &*GENERATION_TASK,
        GenerationHooks {
            before_prepare: None,
            before_request: None,
            after_response: None,
            on_yield: Some(Arc::new(move |_, api, cx| {
                let verifier = yielded.clone();
                let api = api.clone();
                let cx = cx.clone();
                async move {
                    Ok(verifier
                        .on_yield(&api, &cx)
                        .await?
                        .map(|text| YieldContinuation {
                            r#continue: UserContent::Text(text),
                            origin: InputOrigin::Director,
                        }))
                }
                .boxed()
            })),
            after_tools: Some(Arc::new(move |_, _, api, cx| {
                let verifier = effects.clone();
                let api = api.clone();
                let cx = cx.clone();
                async move { verifier.after_tools(&api, &cx).await }.boxed()
            })),
            pending_work: None,
        },
    )
}

/// One step of a claim's verdict, as its commit left it.
enum Step {
    /// The verdict is decided: the text that continues the run, if any.
    Decided(Option<String>),
    /// Run this check, then record its verdict for `revision`.
    Run {
        revision: u64,
        index: usize,
        check: Box<AcceptanceCheck>,
        round: Vec<AcceptanceCheck>,
    },
}

impl Verifier {
    /// The verdict of a final answer: `Some` continues the run with the
    /// evidence of a refuted claim.
    #[tracing::instrument(skip_all)]
    async fn on_yield(&self, api: &HookApi, cx: &Context) -> SessionResult<Option<String>> {
        let conversation_id = api.conversation_id();
        let task_id = api.task_id();
        // No acceptance document: the conversation never had a check.
        let Some(doc) = read_doc(api, &ACCEPTANCE_DOC, conversation_id, cx).await? else {
            return Ok(None);
        };
        if let Some(record) = doc
            .yield_record
            .as_ref()
            .filter(|record| record.task_id == task_id)
        {
            return Ok(record.r#continue.clone());
        }
        let conversation = conversation_of(&self.harness.require()?, conversation_id, cx).await?;
        let now = doc_state(&conversation, &doc, cx).await?;
        let facts = AnswerFacts {
            held: self.held(api, cx).await?,
            checked: !doc.checks.is_empty(),
            goal: read_doc(api, &GOAL_DOC, conversation_id, cx)
                .await?
                .is_some_and(|goal| owns_continuation_wakeup(&goal)),
            claimed: doc.claimed,
            ended: doc.last_end.as_ref().is_some_and(|end| end.at == now),
        };
        // Whether this answer is a claim is the compiled core's decision
        // (`laws/verify.bend` R7).
        if !verify::claims(facts).map_err(core_error)? {
            return Ok(None);
        }
        self.settle(&conversation, task_id, cx).await
    }

    /// Whether queued input or running work owns the next boundary: queued
    /// user input, unsettled children and workflow runs, and jobs whose end
    /// wakes the session. The run they start reaches its own final answer.
    async fn held(&self, api: &HookApi, cx: &Context) -> SessionResult<bool> {
        let conversation_id = api.conversation_id();
        if user_input_queued(api, conversation_id, cx).await?
            || has_unsettled_children(api, conversation_id, cx).await?
            || unsettled_runs(api, conversation_id, cx).await?.count > 0
        {
            return Ok(true);
        }
        let Some(deps) = self.deps.as_ref().and_then(Weak::upgrade) else {
            return Ok(false);
        };
        let harness = deps.harness.require()?;
        match pending_work(&deps, &harness, conversation_id, cx).await {
            Ok(work) => Ok(!work.is_none()),
            Err(PendingWorkError::Read(error)) => Err(error),
        }
    }

    /// Judge the claim of `conversation` to its verdict.
    async fn settle(
        &self,
        conversation: &Conversation,
        task_id: TaskId,
        cx: &Context,
    ) -> SessionResult<Option<String>> {
        let conversation_id = conversation.id();
        let harness = self.harness.require()?;
        let mut runs = 0_usize;
        loop {
            let current = read_doc(&harness, &ACCEPTANCE_DOC, conversation_id, cx)
                .await?
                .unwrap_or_default();
            let now = doc_state(conversation, &current, cx).await?;
            let step = conversation
                .commit(
                    move |tx| async move {
                        let (draft, mut doc) =
                            open_doc(&tx, &ACCEPTANCE_DOC, conversation_id).await?;
                        if let Some(record) = doc
                            .yield_record
                            .as_ref()
                            .filter(|record| record.task_id == task_id)
                        {
                            return Ok(Step::Decided(record.r#continue.clone()));
                        }
                        if !doc.claimed {
                            let (_, claimed) = verify::act(Actor::Worker, Op::Claim, &doc.core())
                                .map_err(core_error)?;
                            doc.adopt(&claimed, None)?;
                        }
                        // Read before the step clears the claim.
                        let goal_claimed = doc.goal_claim;
                        let (action, next) = verify::advance(now, doc.max_returns, &doc.core())
                            .map_err(core_error)?;
                        let step = match action {
                            Action::Run { index } => {
                                let index = usize::try_from(index).unwrap_or(usize::MAX);
                                let Some(check) = doc.checks.get(index) else {
                                    return Err(eukhe_durable::session::SessionError::error(
                                        format!("the compiled core asked for acceptance check {index}, which the session does not hold"),
                                    ));
                                };
                                Step::Run {
                                    revision: doc.revision,
                                    index,
                                    check: Box::new(check.clone()),
                                    round: doc.checks.clone(),
                                }
                            }
                            Action::Rest => {
                                doc.adopt(&next, None)?;
                                Step::Decided(None)
                            }
                            Action::Return => {
                                // The text and the row show the verdicts the
                                // claim was judged by: the core reopens a
                                // broken or unjudged check, so it runs again.
                                let mut judged = doc.clone();
                                doc.adopt(&next, None)?;
                                judged.tries = doc.tries;
                                doc.last_end = None;
                                let text = return_text(&judged);
                                doc.yield_record = Some(YieldRecord {
                                    task_id,
                                    r#continue: Some(text.clone()),
                                });
                                tx.append_entry(conversation_id, verdict_row(&judged, now, None)?)
                                    .await?;
                                Step::Decided(Some(text))
                            }
                            Action::End(label) => {
                                doc.adopt(&next, None)?;
                                let label = label_of(label);
                                doc.last_end = Some(AcceptanceEnd {
                                    label,
                                    at: now,
                                    ended_at: now_millis(),
                                });
                                doc.yield_record = Some(YieldRecord {
                                    task_id,
                                    r#continue: None,
                                });
                                tx.append_entry(
                                    conversation_id,
                                    verdict_row(&doc, now, Some(label))?,
                                )
                                .await?;
                                if goal_claimed {
                                    end_claimed_goal(&tx, conversation_id, &goal_end(&doc, label))
                                        .await?;
                                }
                                Step::Decided(None)
                            }
                        };
                        write_doc(&draft, &doc)?;
                        Ok(step)
                    },
                    cx,
                )
                .await?;
            let (revision, index, check, round) = match step {
                Step::Decided(continuation) => return Ok(continuation),
                Step::Run {
                    revision,
                    index,
                    check,
                    round,
                } => (revision, index, check, round),
            };
            // Each check runs once per state; a state that keeps moving
            // leaves the claim waiting, unverified.
            runs += 1;
            if runs > round.len().saturating_mul(2).saturating_add(4) {
                return Ok(None);
            }
            let (verdict, result) = self
                .gatherer
                .check(conversation, &check, &round, now, cx)
                .await?;
            conversation
                .commit(
                    move |tx| async move {
                        let (draft, mut doc) =
                            open_doc(&tx, &ACCEPTANCE_DOC, conversation_id).await?;
                        let record = Op::Record {
                            revision,
                            index: u64::try_from(index).unwrap_or(u64::MAX),
                            verdict,
                            at: now,
                        };
                        let (admitted, next) = verify::act(Actor::Verifier, record, &doc.core())
                            .map_err(core_error)?;
                        // Refused: the owner changed the checks meanwhile.
                        if admitted {
                            doc.adopt(&next, Some((index, result)))?;
                            write_doc(&draft, &doc)?;
                        }
                        Ok(())
                    },
                    cx,
                )
                .await?;
        }
    }

    /// The worker's effect clears how the last claim ended: the result
    /// has to be earned again on the new state.
    async fn after_tools(&self, api: &HookApi, cx: &Context) -> SessionResult<()> {
        let conversation_id = api.conversation_id();
        let ended = read_doc(api, &ACCEPTANCE_DOC, conversation_id, cx)
            .await?
            .is_some_and(|doc| doc.last_end.is_some());
        if !ended {
            return Ok(());
        }
        conversation_of(&self.harness.require()?, conversation_id, cx)
            .await?
            .commit(
                move |tx| async move {
                    let (draft, mut doc) = open_doc(&tx, &ACCEPTANCE_DOC, conversation_id).await?;
                    doc.last_end = None;
                    write_doc(&draft, &doc)
                },
                cx,
            )
            .await
    }
}

/// How the verifier ends a goal's claim.
fn goal_end(doc: &AcceptanceDoc, label: AcceptanceLabel) -> ClaimEnd {
    match label {
        AcceptanceLabel::Verified => ClaimEnd::Complete(format!(
            "Goal achieved (verified: {} confirmed)",
            count_checks(doc.checks.len())
        )),
        AcceptanceLabel::Failed | AcceptanceLabel::Unverified => ClaimEnd::Pause(format!(
            "Acceptance {}: {}",
            label.slug(),
            outcome_line(doc)
        )),
    }
}

fn count_checks(count: usize) -> String {
    if count == 1 {
        "1 acceptance check".to_owned()
    } else {
        format!("{count} acceptance checks")
    }
}

/// What a check asks, in one line.
pub(crate) fn describe(spec: &CheckSpec) -> String {
    match spec {
        CheckSpec::Command {
            command, expect, ..
        } => format!("command `{command}` (expect exit {expect})"),
        CheckSpec::Judge { condition, .. } => format!("judge: {condition}"),
        CheckSpec::Until { command, .. } => format!("until `{command}`"),
        CheckSpec::Intent { .. } => {
            "intent: what the user's messages ask for now holds on the final state".to_owned()
        }
    }
}

/// The checks that are not confirmed, each with how it ended.
fn outcome_line(doc: &AcceptanceDoc) -> String {
    let open: Vec<String> = doc
        .checks
        .iter()
        .enumerate()
        .filter_map(|(index, check)| match &check.result {
            Some(result) if result.verdict == CheckVerdict::Confirmed => None,
            Some(result) => Some(format!(
                "check {} {} ({})",
                index + 1,
                result.verdict.slug(),
                result.summary
            )),
            None => Some(format!("check {} not judged", index + 1)),
        })
        .collect();
    if open.is_empty() {
        format!("{} confirmed", count_checks(doc.checks.len()))
    } else {
        open.join("; ")
    }
}

/// The evidence that goes back to the worker after a refuted claim.
fn return_text(doc: &AcceptanceDoc) -> String {
    let mut lines = vec![format!(
        "[acceptance: not verified] The harness checked your claim that the task is done: an acceptance check failed or could not judge the current state (return {} of {}).",
        doc.tries, doc.max_returns
    )];
    for (index, check) in doc.checks.iter().enumerate() {
        let head = format!("{}. {}", index + 1, describe(&check.spec));
        match &check.result {
            Some(result) if result.verdict == CheckVerdict::Confirmed => {
                lines.push(format!("{head}: confirmed"));
            }
            Some(result) => {
                lines.push(format!(
                    "{head}: {}: {}",
                    result.verdict.slug(),
                    result.summary
                ));
                if !result.evidence.is_empty() {
                    lines.push(format!("<evidence>\n{}\n</evidence>", result.evidence));
                }
            }
            None => lines.push(format!("{head}: not judged")),
        }
    }
    lines.push(
        "Fix the work so that every check passes (a check that could not judge, e.g. a timeout, runs again too), then finish again. You cannot change or skip a check: all of them run again on the final state."
            .to_owned(),
    );
    lines.join("\n\n")
}

/// The display row of a verdict: the user sees it; the model does not.
/// `ended` is the label a claim ended with; `None` is a return to the
/// worker. Its details hold the checks with their verdicts and evidence.
fn verdict_row(
    doc: &AcceptanceDoc,
    now: u64,
    ended: Option<AcceptanceLabel>,
) -> SessionResult<EntryDraft> {
    let (outcome, text) = match ended {
        Some(label) => (
            label.slug(),
            format!("Acceptance {}: {}.", label.slug(), outcome_line(doc)),
        ),
        None => (
            "returned",
            format!(
                "Acceptance not verified: {}. Returned to the worker ({} of {}).",
                outcome_line(doc),
                doc.tries,
                doc.max_returns
            ),
        ),
    };
    Ok(custom_entry_draft(
        ACCEPTANCE_CUSTOM_TYPE,
        UserContent::Text(text),
        true,
        Some(json!({
            "outcome": outcome,
            "state": now,
            "revision": doc.revision,
            "tries": doc.tries,
            "maxReturns": doc.max_returns,
            "checks": doc.checks,
        })),
        now_millis(),
    )?)
}
