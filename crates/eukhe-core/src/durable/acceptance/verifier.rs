//! The verifier: at a final answer it judges the claim that the task is
//! done. It gathers the evidence of each acceptance check on the
//! conversation's state now, records each verdict, and lets the compiled
//! core (`eukhe_bend::rules::verify::advance`) decide the step: run the
//! next check, give the evidence back to the worker, or end the claim.
//! A claim whose checks all passed is done only when the checks were shown
//! to catch broken code: the core (`eukhe_bend::rules::strength::settle`)
//! has each gauged check measured on the state now (the breaks of the
//! changed code, in a scratch copy), then names the label (checks passed,
//! unconfined; checks passed, not certified; failed; unverified).
//!
//! - A final answer is a claim, unless the claim it would make was
//!   already judged on this state.
//! - Queued user input, unsettled children and workflow runs, and jobs
//!   whose end wakes the session hold the verdict: the run they start
//!   reaches its own final answer.
//! - Every verdict is committed before the next step, with what the
//!   harness observed; the decision of a final answer is recorded by its
//!   generation task, so a rerun after a crash repeats it and a check
//!   whose verdict was not committed runs again.
//! - A verdict judges the state its check's run left when only the
//!   workspace moved while it ran (the check's own output), else the
//!   state before the run, which then no longer counts.
//! - A state that keeps moving while the checks run ends the runs after
//!   twice as many runs as checks, plus four: each check not judged on
//!   the state then is recorded unjudged, naming the checks whose runs
//!   changed the state, and the claim settles on it (back to the worker,
//!   or ended at the cap). A claim never waits with nothing running.
//! - The worker's next effect clears the recorded end: the result has to
//!   be earned again on the new state. Until then a further final answer
//!   is no new claim: the verdict of that state stands.
//! - A strength mark is committed like a verdict, by the verifier only,
//!   and measures the state it was taken on: a later change measures
//!   again. Breaks run only for a claim whose checks all passed.

use std::collections::BTreeSet;
use std::path::Path;
use std::sync::{Arc, Weak};

use eukhe_bend::rules::strength::{self, Step as StrengthStep, Strength};
use eukhe_bend::rules::verify::{self, Action, Actor, AnswerFacts, Op, Verdict};
use eukhe_chord::context::Context;
use eukhe_durable::harness::define::hook;
use eukhe_durable::harness::types::{
    GenerationHooks, HookApi, HookRegistration, YieldContinuation,
};
use eukhe_durable::harness::{Conversation, GENERATION_TASK};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::{EntryDraft, TaskId};
use eukhe_types::acceptance::{
    AcceptanceCheck, AcceptanceEnd, AcceptanceLabel, CheckResult, CheckSpec, CheckVerdict,
    StrengthBar, StrengthMark,
};
use eukhe_types::input_origin::InputOrigin;
use eukhe_types::pi_ai::UserContent;
use futures::FutureExt;
use serde_json::json;

use super::docs::{mark_of, strength_of, AcceptanceDoc, YieldRecord, ACCEPTANCE_DOC};
use super::evidence::{Gatherer, DEFAULT_CHECK_TIMEOUT_MS};
use super::ops::{core_error, doc_parts, doc_state, label_of};
use super::strength::{Breaker, Pass, Probe};
use super::ACCEPTANCE_CUSTOM_TYPE;
use crate::autonomous::now_millis;
use crate::durable::autonomous::{
    conversation_of, open_doc, read_doc, user_input_queued, write_doc,
};
use crate::durable::children::has_unsettled_children;
use crate::durable::entries::custom_entry_draft;
use crate::durable::pending::{pending_work, PendingWorkError};
use crate::durable::workflow::unsettled_runs;
use crate::durable::{HarnessCell, HostDeps};

/// The verifier of one session.
#[derive(Clone)]
pub(crate) struct Verifier {
    pub(crate) harness: HarnessCell,
    pub(crate) gatherer: Gatherer,
    /// Measures a gauged check's strength: breaks the changed code in a
    /// scratch copy and runs the check on each break.
    pub(crate) breaker: Arc<dyn Breaker>,
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
            on_truncated: None,
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
    /// Every check passed: measure this check's strength on the state
    /// `at`, then record the mark for `revision`.
    Measure {
        revision: u64,
        index: usize,
        probe: Box<Probe>,
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
        // The checks whose run changed the state.
        let mut movers = BTreeSet::new();
        loop {
            let current = read_doc(&harness, &ACCEPTANCE_DOC, conversation_id, cx)
                .await?
                .unwrap_or_default();
            let before = doc_parts(conversation, &current, cx).await?;
            let now = before.state();
            // Each check runs once per state. A state that keeps moving
            // (checks whose runs change it, edits made meanwhile) ends the
            // runs: every check not judged on the state now is recorded
            // unjudged with the reason, and the core settles the claim on
            // it, so no claim waits with nothing running.
            let unsettled = (runs >= current.checks.len().saturating_mul(2).saturating_add(4))
                .then(|| unsettled_reason(&movers));
            let cwd = self.gatherer.cwd.clone();
            let step = conversation
                .commit(
                    move |tx| {
                        let unsettled = unsettled.clone();
                        let cwd = cwd.clone();
                        async move {
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
                        let (mut action, mut next) =
                            verify::advance(now, doc.max_returns, &doc.core())
                                .map_err(core_error)?;
                        if let Some(reason) = &unsettled {
                            while let Action::Run { index } = action {
                                let slot = usize::try_from(index).unwrap_or(usize::MAX);
                                let record = Op::Record {
                                    revision: doc.revision,
                                    index,
                                    verdict: Verdict::Unjudged,
                                    at: now,
                                };
                                let (admitted, recorded) =
                                    verify::act(Actor::Verifier, record, &doc.core())
                                        .map_err(core_error)?;
                                if !admitted {
                                    return Err(eukhe_durable::session::SessionError::error(
                                        format!("the compiled core refused to record acceptance check {slot} unjudged"),
                                    ));
                                }
                                doc.adopt(
                                    &recorded,
                                    Some((
                                        slot,
                                        CheckResult {
                                            verdict: CheckVerdict::Unjudged,
                                            at: now,
                                            summary: reason.clone(),
                                            evidence: String::new(),
                                            judged_at: now_millis(),
                                        },
                                    )),
                                )?;
                                (action, next) = verify::advance(now, doc.max_returns, &doc.core())
                                    .map_err(core_error)?;
                            }
                        }
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
                            Action::End(ended) => {
                                // Every check passed: done only when the
                                // gauged checks were shown to catch broken
                                // code on this state; each one not measured
                                // on it is measured first.
                                let label = match strength::settle(ended, now, &doc.gauges())
                                    .map_err(core_error)?
                                {
                                    StrengthStep::Measure { index } => {
                                        let index = usize::try_from(index).unwrap_or(usize::MAX);
                                        let probe = doc
                                            .checks
                                            .get(index)
                                            .and_then(|check| probe_of(check, &doc, &cwd, now))
                                            .ok_or_else(|| SessionError::error(format!(
                                                "the compiled core asked to measure acceptance check {index}, which the session does not hold as a gauged check"
                                            )))?;
                                        write_doc(&draft, &doc)?;
                                        return Ok(Step::Measure {
                                            revision: doc.revision,
                                            index,
                                            probe: Box::new(probe),
                                        });
                                    }
                                    StrengthStep::End(label) => label_of(label),
                                };
                                doc.adopt(&next, None)?;
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
                                Step::Decided(None)
                            }
                        };
                        write_doc(&draft, &doc)?;
                        Ok(step)
                        }
                    },
                    cx,
                )
                .await?;
            let (revision, index, check, round) = match step {
                Step::Decided(continuation) => return Ok(continuation),
                Step::Measure {
                    revision,
                    index,
                    probe,
                } => {
                    runs += 1;
                    self.measure(conversation, revision, index, *probe, cx)
                        .await?;
                    continue;
                }
                Step::Run {
                    revision,
                    index,
                    check,
                    round,
                } => (revision, index, check, round),
            };
            runs += 1;
            let (verdict, mut result) = self
                .gatherer
                .check(conversation, &check, &round, now, cx)
                .await?;
            // The run itself may have written to the workspace (a build's
            // output, new at every run when a link fails): with no new
            // effect and no new message of the user meanwhile, the verdict
            // judges the state the run left, else that of every next run
            // would be stale on arrival and the claim would wait forever.
            // A new effect or message leaves it on the state before, which
            // no longer counts: the check runs again.
            let after = doc_parts(conversation, &current, cx).await?;
            if after.state() != now {
                movers.insert(index);
            }
            let at = if after.moved_in_workspace_only(&before) {
                after.state()
            } else {
                now
            };
            result.at = at;
            conversation
                .commit(
                    move |tx| async move {
                        let (draft, mut doc) =
                            open_doc(&tx, &ACCEPTANCE_DOC, conversation_id).await?;
                        let record = Op::Record {
                            revision,
                            index: u64::try_from(index).unwrap_or(u64::MAX),
                            verdict,
                            at,
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

    /// Measure the strength of check `index` of `revision` with `probe` and
    /// record the mark: the compiled core admits only the verifier's
    /// record of a check that exists; a change of the checks meanwhile
    /// (another revision) drops it.
    async fn measure(
        &self,
        conversation: &Conversation,
        revision: u64,
        index: usize,
        probe: Probe,
        cx: &Context,
    ) -> SessionResult<()> {
        let at = probe.at;
        let found = self.breaker.measure(probe, cx).await?;
        let mark = StrengthMark {
            caught: found.caught,
            ran: found.ran,
            planned: found.planned,
            at,
            survivors: found.survivors,
            note: found.note,
            measured_at: now_millis(),
        };
        let conversation_id = conversation.id();
        conversation
            .commit(
                move |tx| async move {
                    let (draft, mut doc) = open_doc(&tx, &ACCEPTANCE_DOC, conversation_id).await?;
                    if doc.revision != revision {
                        return Ok(());
                    }
                    let (admitted, next) = strength::record(
                        Actor::Verifier,
                        u64::try_from(index).unwrap_or(u64::MAX),
                        mark_of(&mark),
                        &doc.gauges(),
                    )
                    .map_err(core_error)?;
                    if admitted {
                        doc.adopt_mark(&next, index, mark)?;
                        write_doc(&draft, &doc)?;
                    }
                    Ok(())
                },
                cx,
            )
            .await
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

/// The measurement of `check`'s strength on the state `at` in `doc`'s
/// workspace (`cwd` when the doc names none): its command, what passing
/// means, and the files of every check, which are never broken. `None` for
/// a judge and the intent check.
fn probe_of(check: &AcceptanceCheck, doc: &AcceptanceDoc, cwd: &Path, at: u64) -> Option<Probe> {
    let (command, pass, timeout_ms) = match &check.spec {
        CheckSpec::Command {
            command,
            expect,
            timeout_ms,
            ..
        } => (command, Pass::Exit(*expect), *timeout_ms),
        CheckSpec::Until {
            command,
            timeout_ms,
            ..
        } => (command, Pass::Holds, *timeout_ms),
        CheckSpec::Judge { .. } | CheckSpec::Intent { .. } => return None,
    };
    Some(Probe {
        command: command.clone(),
        pass,
        timeout_ms: timeout_ms.unwrap_or(DEFAULT_CHECK_TIMEOUT_MS),
        protected: doc
            .checks
            .iter()
            .flat_map(|check| check.protected.iter().map(|file| file.path.clone()))
            .collect(),
        workspace: doc.workspace.clone().unwrap_or_else(|| cwd.to_path_buf()),
        baseline: doc.baseline.clone(),
        at,
    })
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

/// What the measurement of `check`'s strength on the state `now` shows;
/// `None` for a judge and the intent check (no code to break for them).
///
/// # Errors
///
/// A compiled-core failure.
pub(crate) fn strength_text(check: &AcceptanceCheck, now: u64) -> SessionResult<Option<String>> {
    let pct = match check.spec.bar() {
        StrengthBar::Exempt => return Ok(None),
        StrengthBar::Waived => return Ok(Some("strength waived by the task's owner".to_owned())),
        StrengthBar::Needs(pct) => pct,
    };
    let mark = check.strength.as_ref().filter(|mark| mark.at == now);
    Ok(Some(match (strength_of(check, now)?, mark) {
        (Strength::Strong, Some(mark)) => format!(
            "caught {} of {} breaks (needs {pct} %)",
            mark.caught, mark.ran
        ),
        (Strength::Weak, Some(mark)) if mark.ran == 0 => format!(
            "weak, {}",
            mark.note.as_deref().unwrap_or("nothing to break")
        ),
        (Strength::Weak, Some(mark)) => {
            let caught = format!(
                "weak, caught {} of {} breaks (needs {pct} %)",
                mark.caught, mark.ran
            );
            if mark.survivors.is_empty() {
                caught
            } else {
                let survived: Vec<String> = mark
                    .survivors
                    .iter()
                    .map(|survivor| {
                        format!("{}:{} {}", survivor.path, survivor.line, survivor.change)
                    })
                    .collect();
                format!("{caught}; survived: {}", survived.join("; "))
            }
        }
        (Strength::Unshown, Some(mark)) => format!(
            "not shown to catch broken code, {} ({} of {} breaks ran)",
            mark.note
                .as_deref()
                .unwrap_or("the measurement was cut short"),
            mark.ran,
            mark.planned
        ),
        (Strength::Strong | Strength::Weak | Strength::Unshown | Strength::Free, _) => {
            format!("not measured on this state (needs {pct} % of the breaks caught)")
        }
    }))
}

/// How a claim whose checks all passed stands on the state `now`: the
/// breaks its strong checks caught when done is certified, else what keeps
/// it from being certified.
fn strength_line(doc: &AcceptanceDoc, now: u64) -> SessionResult<Certification> {
    let (mut caught, mut ran, mut shown) = (0_u64, 0_u64, false);
    let mut blocks = Vec::new();
    for (index, check) in doc.checks.iter().enumerate() {
        match strength_of(check, now)? {
            Strength::Strong => {
                shown = true;
                if let Some(mark) = &check.strength {
                    caught += mark.caught;
                    ran += mark.ran;
                }
            }
            Strength::Weak | Strength::Unshown => {
                if let Some(text) = strength_text(check, now)? {
                    blocks.push(format!("check {}: {text}", index + 1));
                }
            }
            Strength::Free => {}
        }
    }
    Ok(match (blocks.is_empty(), shown) {
        (true, true) => Certification::Shown(format!("caught {caught} of {ran} breaks")),
        (true, false) => Certification::Blocked(
            "no check was shown to catch broken code (a judge or a waived check certifies nothing)"
                .to_owned(),
        ),
        (false, _) => Certification::Blocked(blocks.join("; ")),
    })
}

/// Whether a passed claim's checks were shown to catch broken code, in
/// words.
enum Certification {
    Shown(String),
    Blocked(String),
}

/// The line of a claim that ended with `label` on the state `now`: the
/// checks that did not pass, or for a claim whose checks all passed, how
/// their strength stands.
fn end_line(doc: &AcceptanceDoc, now: u64, label: AcceptanceLabel) -> SessionResult<String> {
    let outcome = outcome_line(doc);
    Ok(match label {
        AcceptanceLabel::Failed | AcceptanceLabel::Unverified => outcome,
        AcceptanceLabel::Verified
        | AcceptanceLabel::ChecksPassedUnconfined
        | AcceptanceLabel::ChecksPassedNotCertified => match strength_line(doc, now)? {
            Certification::Shown(text) => format!("{outcome}, {text}"),
            Certification::Blocked(text) => format!("{outcome}; {text}"),
        },
    })
}

/// Why a check was recorded unjudged at the end of the runs: the state
/// kept moving, and which checks' runs moved it.
fn unsettled_reason(movers: &BTreeSet<usize>) -> String {
    let named: Vec<String> = movers.iter().map(|index| (index + 1).to_string()).collect();
    match named.as_slice() {
        [] => "the state kept changing while the checks ran".to_owned(),
        [one] => format!(
            "the state kept changing while the checks ran: the runs of check {one} changed it"
        ),
        many => format!(
            "the state kept changing while the checks ran: the runs of checks {} changed it",
            many.join(", ")
        ),
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
        "Fix the work so that every check passes (a check that could not judge, e.g. a timeout, runs again too), then finish again. Every check runs again on the final state; only the task's owner sets checks."
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
            format!(
                "Acceptance {}: {}.",
                label.text(),
                end_line(doc, now, label)?
            ),
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
