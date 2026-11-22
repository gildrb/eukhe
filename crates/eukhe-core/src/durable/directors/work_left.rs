//! The work-left Director: a final answer that leaves task work undone
//! continues the run. Nobody watches a run; an answer that asks for leave
//! to do part of the task, offers to do the rest, or asks how to go on
//! would stop it until a person comes back.
//!
//! Its extension installs after the one whose `on_yield` hook runs the
//! Director stack (`durable/registry.rs`): the first continuation wins, so
//! it decides only at a final answer the Director stack, the autonomous
//! run and the loop did not continue. The decision is the compiled core's
//! (`eukhe_bend::rules::work_left`, model `bend/work_left.bend`): this
//! module gathers the facts (a driver, queued input, whether the run
//! acted, the session's budget, the progress check, the Director loop's
//! steps left), asks the final-answer judge when the core asks
//! (`acceptance::read_final_answer`: one request, no tools, the answer
//! alone), and records the decision in `eukhe.directors` keyed by the
//! generation, so a rerun after a crash repeats it.

use std::collections::HashMap;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_bend::rules::work_left::{self, Facts, Progress, Reading, Step};
use eukhe_bend::{expect_core, Entry};
use eukhe_chord::context::Context;
use eukhe_durable::entries::{UserData, USER_ENTRY};
use eukhe_durable::harness::define::{define_extension, hook};
use eukhe_durable::harness::types::{
    Extension, GenerationHooks, HookApi, HookRegistration, YieldContinuation,
};
use eukhe_durable::harness::{
    Conversation, ConversationEntryQuery, Harness, GENERATION_TASK, LIVE_DOC,
};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::{ConversationId, EntryData, EntryId, ScanOrder, SubmissionId, TaskId};
use eukhe_types::input_origin::InputOrigin;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, Message, ToolResultMessage, UserContent,
};
use futures::FutureExt;
use serde::{Deserialize, Serialize};

use super::progress::{compared, stall_check, Last, Stall};
use super::{
    director_state, DirectorLimits, DirectorState, RunLoop, DIRECTORS_DOC,
    DIRECTOR_NOTICE_CUSTOM_TYPE,
};
use crate::autonomous::{no_progress_reason, now_millis, AutonomousStop, SessionBudget};
use crate::durable::acceptance::{read_final_answer, AnswerReading, Judge};
use crate::durable::autonomous::{
    budget_report, conversation_of, open_doc, read_doc, user_input_queued, write_doc,
    AUTONOMOUS_DOC, LOOP_DOC,
};
use crate::durable::budget::BudgetGate;
use crate::durable::children::{has_unsettled_children, WorkLedger};
use crate::durable::entries::custom_entry_draft;
use crate::durable::loop_mode::LOOP_MODE_DOC;
use crate::durable::workflow::unsettled_runs;
use crate::durable::{HarnessCell, HostDeps};

/// The extension's name.
pub const WORK_LEFT_EXTENSION: &str = "eukhe.work_left";

/// How many entries one read of the session's work or of the run's acts
/// takes.
const PAGE: usize = 256;

/// The tools that only read: the documents' read tools and the chat
/// memory's.
const READ_TOOLS: [&str; 5] = ["read", "grep", "glob", "zoom", "date"];

/// The work-left Director's last decision (`eukhe.directors`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct WorkLeftRecord {
    /// The generation whose final answer it decided: a rerun of it repeats
    /// the decision.
    pub task_id: TaskId,
    /// The first input of the run: the progress check compares within one
    /// run.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub input: Option<SubmissionId>,
    /// The session's work at the decision ([`WorkLedger::count`]).
    pub work: u64,
    /// The continuations in a row with no new work, as the progress check
    /// counted them.
    pub stalls: u64,
    pub outcome: WorkLeftOutcome,
    /// What the run last found left of its task, for its report: the items
    /// of its latest reading of work left (an answer of the same run that
    /// stands unread keeps them), or why it stopped for want of progress;
    /// empty when nothing is left.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub left: Vec<String>,
    /// The conversation's newest input entry at the decision: a newer one
    /// starts another run, which `left` does not tell of.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub newest_input: Option<EntryId>,
}

/// What the work-left Director decided.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "camelCase")]
pub enum WorkLeftOutcome {
    /// The run went on with this harness continuation.
    Continue { text: String },
    /// The final answer stood.
    Yield,
}

impl WorkLeftOutcome {
    fn continuation(&self) -> Option<String> {
        match self {
            Self::Continue { text } => Some(text.clone()),
            Self::Yield => None,
        }
    }
}

/// The services of the work-left Director: the session's Harness, budget
/// gate and final-answer judge, the Director stack's limits (read at each
/// step), and the work of each conversation its progress check counts (a
/// cache of what the transcript shows).
#[derive(Clone)]
pub(crate) struct WorkLeftHost {
    pub(crate) harness: HarnessCell,
    pub(crate) budget: Arc<BudgetGate>,
    pub(crate) judge: Arc<dyn Judge>,
    pub(crate) limits: Arc<dyn Fn() -> DirectorLimits + Send + Sync>,
    pub(crate) work: Arc<Mutex<HashMap<ConversationId, WorkLedger>>>,
}

/// The work-left Director's extension of one session: its `on_yield` hook
/// over the session's Harness, budget gate and judge
/// (`acceptance::answer_judge`), with the Director stack's limits from the
/// `directors` settings.
#[must_use]
pub fn extension(deps: &Arc<HostDeps>) -> Arc<Extension> {
    let settings = Arc::clone(&deps.settings);
    let host = WorkLeftHost {
        harness: deps.harness.clone(),
        budget: Arc::clone(&deps.budget),
        judge: crate::durable::acceptance::answer_judge(deps.harness.clone(), deps.models.clone()),
        limits: Arc::new(move || DirectorLimits::of(settings.manager().settings())),
        work: Arc::default(),
    };
    define_extension(Extension {
        name: WORK_LEFT_EXTENSION.to_owned(),
        hooks: vec![work_left_hook(host)],
        ..Extension::default()
    })
}

/// The work-left Director's `on_yield` hook on `pi.generation`. Its
/// extension installs after the one that runs the Director stack: the
/// first continuation wins, so it runs only when the stack's step yields.
pub(crate) fn work_left_hook(host: WorkLeftHost) -> HookRegistration {
    hook(
        &*GENERATION_TASK,
        GenerationHooks {
            on_yield: Some(Arc::new(move |message, api, cx| {
                let (host, message, api, cx) =
                    (host.clone(), message.clone(), api.clone(), cx.clone());
                async move {
                    Ok(host
                        .on_yield(&message, &api, &cx)
                        .await?
                        .map(|text| YieldContinuation {
                            r#continue: UserContent::Text(text),
                            origin: InputOrigin::Director,
                        }))
                }
                .boxed()
            })),
            ..GenerationHooks::default()
        },
    )
}

/// The facts the step reads, with the progress check's count and the
/// work it compared, and the continuations in a row without new work after
/// which the autonomous run stopped at this answer.
#[derive(Debug, Clone, Copy)]
struct Gathered {
    facts: Facts,
    work: u64,
    stalls: u64,
    autonomous_stop: Option<u64>,
}

impl WorkLeftHost {
    /// The work-left step at a final answer; `Some` continues the run with
    /// that harness text.
    #[tracing::instrument(skip_all)]
    pub(super) async fn on_yield(
        &self,
        answer: &AssistantMessage,
        api: &HookApi,
        cx: &Context,
    ) -> SessionResult<Option<String>> {
        let conversation_id = api.conversation_id();
        let task_id = api.task_id();
        let state: DirectorState = read_doc(api, &DIRECTORS_DOC, conversation_id, cx)
            .await?
            .unwrap_or_default();
        if let Some(record) = recorded(&state, task_id) {
            return Ok(record.outcome.continuation());
        }
        let input = read_doc(api, &LIVE_DOC, conversation_id, cx)
            .await?
            .and_then(|live| live.run)
            .and_then(|run| run.inputs.first().copied());
        let conversation = conversation_of(&self.harness.require()?, conversation_id, cx).await?;
        let gathered = self.gather(api, &conversation, &state, input, cx).await?;
        let (step, reading, items) =
            match expect_core(Entry::WorkLeft, work_left::step(gathered.facts)) {
                Step::Ask => {
                    let (reading, items) = match answer_text(answer) {
                        Some(text) => reading_of(
                            read_final_answer(&*self.judge, conversation_id, &text, cx).await,
                        ),
                        None => (Reading::Unjudged, Vec::new()),
                    };
                    let facts = Facts {
                        reading,
                        ..gathered.facts
                    };
                    let step = expect_core(Entry::WorkLeft, work_left::step(facts));
                    (step, reading, items)
                }
                step @ (Step::Continue { .. } | Step::Yield) => (step, Reading::Unread, Vec::new()),
            };
        let left = found_left(state.work_left.as_ref(), input, gathered, reading, &items);
        let newest_input = newest_input(&conversation, cx).await?;
        conversation
            .commit(
                move |tx| async move {
                    let (draft, mut state) = open_doc(&tx, &DIRECTORS_DOC, conversation_id).await?;
                    if let Some(record) = recorded(&state, task_id) {
                        return Ok(record.outcome.continuation());
                    }
                    let outcome = match step {
                        Step::Continue { left } => {
                            state.run = Some(RunLoop {
                                input,
                                left,
                                end: None,
                            });
                            tx.append_entry(conversation_id, notice(&items)?).await?;
                            WorkLeftOutcome::Continue {
                                text: continuation(&items),
                            }
                        }
                        // A reading is given: the core asks no more
                        // (`work_left_asks_iff_unread`); an unread answer
                        // never continues.
                        Step::Yield | Step::Ask => WorkLeftOutcome::Yield,
                    };
                    state.work_left = Some(WorkLeftRecord {
                        task_id,
                        input,
                        work: gathered.work,
                        stalls: gathered.stalls,
                        outcome: outcome.clone(),
                        left,
                        newest_input,
                    });
                    write_doc(&draft, &state)?;
                    Ok(outcome.continuation())
                },
                cx,
            )
            .await
    }

    /// The facts at the final answer of the run whose first input is
    /// `input`; the reading is not read yet.
    async fn gather(
        &self,
        api: &HookApi,
        conversation: &Conversation,
        state: &DirectorState,
        input: Option<SubmissionId>,
        cx: &Context,
    ) -> SessionResult<Gathered> {
        let conversation_id = api.conversation_id();
        let limits = (self.limits)();
        let autonomous = read_doc(api, &AUTONOMOUS_DOC, conversation_id, cx).await?;
        // The autonomous run stopped for want of progress at this answer:
        // its stop and its progress check are of this run.
        let autonomous_stop = match autonomous.as_ref().and_then(|state| state.last_stop) {
            Some(AutonomousStop::NoProgress { stalls }) => {
                read_doc(api, &LOOP_DOC, conversation_id, cx)
                    .await?
                    .and_then(|state| state.progress)
                    .filter(|progress| progress.input == input && progress.stalls == stalls)
                    .map(|_| stalls)
            }
            Some(AutonomousStop::Checks(_) | AutonomousStop::Budget) | None => None,
        };
        let looping = read_doc(api, &LOOP_MODE_DOC, conversation_id, cx)
            .await?
            .is_some_and(|doc| doc.state.phase.is_on());
        let queued = user_input_queued(api, conversation_id, cx).await?
            || has_unsettled_children(api, conversation_id, cx).await?
            || unsettled_runs(api, conversation_id, cx).await?.count > 0;
        let acted = acted_since_user(conversation, cx).await?;
        let funded = match SessionBudget::of(budget_report(&self.budget).await?.as_ref()) {
            SessionBudget::Working => true,
            SessionBudget::Short(_) => false,
        };
        let work = read_work(&self.work, conversation, cx).await?;
        let last = state.work_left.as_ref().map(|record| Last {
            same_run: record.input == input,
            stalls: record.stalls,
            work: record.work,
        });
        let (progress, stalls) = match stall_check(limits.stall_steps, compared(last), work) {
            Stall::Go { stalls } => (Progress::Go { stalls }, stalls),
            // The chain stops at the cap, where the autonomous run is
            // steered: the work-left Director has no other approach to ask.
            Stall::Stop { stalls } | Stall::Steer { stalls } => (Progress::Stop { stalls }, stalls),
        };
        let left = state
            .run
            .as_ref()
            .filter(|run| run.input == input)
            .map_or(limits.max_steps, |run| run.left);
        Ok(Gathered {
            facts: Facts {
                driven: autonomous.is_some_and(|state| state.enabled) || looping,
                queued,
                acted,
                funded,
                progress,
                left,
                reading: Reading::Unread,
            },
            work,
            stalls,
            autonomous_stop,
        })
    }
}

/// The decision recorded for the generation `task_id`.
fn recorded(state: &DirectorState, task_id: TaskId) -> Option<&WorkLeftRecord> {
    state
        .work_left
        .as_ref()
        .filter(|record| record.task_id == task_id)
}

/// What the run has found left of its task once an answer is decided:
/// why it stopped for want of progress (the autonomous run's stop, or the
/// work-left chain's), else the items of the judge's reading of work left.
/// A reading of no work left, or no verdict, clears it; an answer that
/// stands unread keeps what the run's last decision found.
fn found_left(
    last: Option<&WorkLeftRecord>,
    input: Option<SubmissionId>,
    gathered: Gathered,
    reading: Reading,
    items: &[String],
) -> Vec<String> {
    if let Some(stalls) = gathered.autonomous_stop {
        return vec![no_progress_reason(stalls)];
    }
    if let Progress::Stop { stalls } = gathered.facts.progress {
        return vec![format!(
            "no progress: {stalls} continuations in a row made no tool call with a new result"
        )];
    }
    match reading {
        Reading::Left => items.to_vec(),
        Reading::Finished | Reading::Unjudged => Vec::new(),
        Reading::Unread => last
            .filter(|record| record.input == input)
            .map(|record| record.left.clone())
            .unwrap_or_default(),
    }
}

/// The conversation's newest input entry (a user entry, whatever its
/// origin): each run starts with one.
async fn newest_input(conversation: &Conversation, cx: &Context) -> SessionResult<Option<EntryId>> {
    let mut cursor = None;
    loop {
        let page = conversation
            .entries(ConversationEntryQuery::default(), PAGE, cursor, cx)
            .await?;
        if let Some(entry) = page
            .items
            .iter()
            .find(|entry| entry.kind == USER_ENTRY.kind())
        {
            return Ok(Some(entry.id));
        }
        match page.next {
            Some(next) => cursor = Some(next),
            None => return Ok(None),
        }
    }
}

/// What the conversation's last run found left of its task, for its
/// report ([`WorkLeftRecord::left`]): `None` when nothing is left, and once
/// another run started (an input entry newer than the last decision's).
///
/// # Errors
///
/// The conversation's Director state or entries cannot be read.
pub async fn run_left(
    harness: &Harness,
    conversation: &Conversation,
    cx: &Context,
) -> SessionResult<Option<Vec<String>>> {
    let Some(record) = director_state(harness, conversation.id(), cx)
        .await?
        .work_left
        .filter(|record| !record.left.is_empty() && record.newest_input.is_some())
    else {
        return Ok(None);
    };
    Ok((newest_input(conversation, cx).await? == record.newest_input).then_some(record.left))
}

/// The text of a final answer, when it has any.
fn answer_text(answer: &AssistantMessage) -> Option<String> {
    let text = answer
        .content
        .iter()
        .filter_map(|block| match block {
            AssistantContentBlock::Text(text) => Some(text.text.as_str()),
            AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => None,
        })
        .collect::<Vec<_>>()
        .join("\n");
    (!text.trim().is_empty()).then_some(text)
}

/// The rule's reading of the judge's, with the items it listed as left.
fn reading_of(reading: AnswerReading) -> (Reading, Vec<String>) {
    match reading {
        AnswerReading::Done => (Reading::Finished, Vec::new()),
        AnswerReading::Left(items) => (Reading::Left, items),
        AnswerReading::Unjudged(_) => (Reading::Unjudged, Vec::new()),
    }
}

/// The harness continuation of an answer that left the work `items`
/// undone (the judge's words; none when it listed none).
fn continuation(items: &[String]) -> String {
    let left = if items.is_empty() {
        "[director: work left] The final answer leaves task work undone.".to_owned()
    } else {
        let list: Vec<String> = items.iter().map(|item| format!("- {item}")).collect();
        format!(
            "[director: work left] The final answer leaves task work undone:\n{}",
            list.join("\n")
        )
    };
    format!(
        "{left}\n\nNobody is watching this run to answer a question or grant leave. Decide and act: do the remaining work now, then give the final answer. State each assumption made in the final answer. Work that truly cannot be done (a refusal, a missing credential, a check's protected file) goes into the final answer; the rest gets done."
    )
}

/// The display row that tells the user the run went on (the model does not
/// see it).
fn notice(items: &[String]) -> SessionResult<eukhe_durable::types::EntryDraft> {
    let text = if items.is_empty() {
        "The final answer left task work undone; the run went on.".to_owned()
    } else {
        format!(
            "The final answer left task work undone ({}); the run went on.",
            items.join("; ")
        )
    };
    Ok(custom_entry_draft(
        DIRECTOR_NOTICE_CUSTOM_TYPE,
        UserContent::Text(text),
        /*display*/ true,
        Some(serde_json::json!({ "workLeft": items })),
        now_millis(),
    )?)
}

/// The work the session did so far, for a progress check: the cache reads
/// the entries it did not read yet.
pub(crate) async fn read_work(
    cache: &Mutex<HashMap<ConversationId, WorkLedger>>,
    conversation: &Conversation,
    cx: &Context,
) -> SessionResult<u64> {
    let conversation_id = conversation.id();
    let read = cache
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .get(&conversation_id)
        .and_then(WorkLedger::last);
    let mut cursor = None;
    loop {
        let page = conversation
            .entries(
                ConversationEntryQuery {
                    min_entry_id: read,
                    max_entry_id: None,
                    order: Some(ScanOrder::Ascending),
                },
                PAGE,
                cursor,
                cx,
            )
            .await?;
        let mut cache = cache.lock().unwrap_or_else(PoisonError::into_inner);
        let ledger = cache.entry(conversation_id).or_default();
        ledger.read_page(&page.items);
        match page.next {
            Some(next) => cursor = Some(next),
            None => return Ok(ledger.count()),
        }
    }
}

/// Whether the run made a tool call with an effect since the user's last
/// message (the newest user entry of the user's own words).
async fn acted_since_user(conversation: &Conversation, cx: &Context) -> SessionResult<bool> {
    let mut cursor = None;
    loop {
        let page = conversation
            .entries(ConversationEntryQuery::default(), PAGE, cursor, cx)
            .await?;
        for entry in page.items {
            if entry.kind == USER_ENTRY.kind() {
                let origin = UserData::decode(entry.data.as_ref())
                    .map_err(|error| {
                        SessionError::error(format!("a user entry's origin: {error}"))
                    })?
                    .origin;
                if origin == InputOrigin::User {
                    return Ok(false);
                }
            }
            let acted = entry.model.iter().flatten().any(|message| match message {
                Message::ToolResult(result) => tool_acted(result),
                Message::System(_) | Message::User(_) | Message::Assistant(_) => false,
            });
            if acted {
                return Ok(true);
            }
        }
        match page.next {
            Some(next) => cursor = Some(next),
            None => return Ok(false),
        }
    }
}

/// Whether the call behind `result` had an effect: every tool but the
/// read-only ones; a `bash` call when a step has an effect other than
/// reading, or when its steps are not recorded.
#[must_use]
pub fn tool_acted(result: &ToolResultMessage) -> bool {
    match result.tool_name.as_str() {
        name if READ_TOOLS.contains(&name) => false,
        "bash" => result
            .details
            .as_ref()
            .and_then(|details| details.get("steps"))
            .and_then(serde_json::Value::as_array)
            .is_none_or(|steps| {
                steps.iter().any(|step| {
                    step.get("effects")
                        .and_then(serde_json::Value::as_array)
                        .is_none_or(|effects| {
                            effects.iter().any(|effect| effect.as_str() != Some("read"))
                        })
                })
            }),
        _ => true,
    }
}
