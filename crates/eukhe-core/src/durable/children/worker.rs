//! Main's workers (`sessionShape` `main-worker`, docs/usage.md): main talks
//! to the user; a persistent worker child does the work. Main reaches its
//! workers through three tools, and the route of each user message is the
//! model's choice of tool (no code picks it):
//!
//! - `worker_assign {note?, worker?, fresh?}`: a new task. The first one
//!   creates the worker (`worker`, shared workspace, report `inbox`, the
//!   chat view); later ones re-task it ([`super::assign`]) when it is idle.
//!   `fresh` starts another worker (`worker-2`, ...) for unrelated work.
//! - `worker_forward {kind, note?, worker?}`: the user's words for the
//!   running work, as `context` (fold it in) or `redirect` (re-plan), placed
//!   at the worker's next boundary (never inside a tool call). A paused tree
//!   wakes for it. An idle worker gets it as a new task of that kind.
//! - `worker_status {worker?}`: where each worker stands.
//!
//! No tool takes the user's words from the model: the host attaches every
//! user message main received since its last hand-over, byte for byte, in
//! order, once (`forward_pick`, the compiled core's `worker` entry; laws
//! `forward_*`). The model may add a `note`, sent apart and labeled
//! `[note from main]`. The hand-over cursor (`eukhe.workers`) moves in the
//! commit that admits the task, or right after a forward is admitted.

use std::sync::Arc;

use eukhe_ai::typebox::Type;
use eukhe_bend::rules::worker::forward_pick;
use eukhe_chord::context::{await_with_context, Context};
use eukhe_chord::json::{from_json, to_json, JsonValue};
use eukhe_durable::documents::{ConversationDoc, DocDefinition};
use eukhe_durable::entries::{UserData, USER_ENTRY};
use eukhe_durable::harness::define::define_tool;
use eukhe_durable::harness::types::{
    ToolExecutionApi, ToolExecutionApiExt, ToolExecutionResult, ToolRegistration,
};
use eukhe_durable::harness::{ConversationEntryQuery, Harness};
use eukhe_durable::session::{CommitListener, SessionError, SessionResult, Tx, Unsubscribe};
use eukhe_durable::types::{
    CommitChange, CommitPublication, ConversationId, DocumentCommitChange, DocumentIdentity,
    DocumentReader, DocumentReaderExt, EntryData, EntryId, LatestFork, ScanOrder,
};
use eukhe_types::daemon::{SessionWorker, WorkerRunState};
use eukhe_types::input_origin::InputOrigin;
use eukhe_types::pi_ai::{Message, TextContent, UserContentBlock};
use serde::{Deserialize, Serialize};
use serde_json::{json, Map, Value};
use tokio::sync::mpsc;
use tokio::task::JoinHandle;

use super::assign::{assign, child_busy, Assignment};
use super::host::{
    ChildMessageKind, PauseAction, RlmChildPauseRequest, RlmChildPromptRequest, RlmSubagentHost,
};
use super::pause::RunPause;
use super::registry::{read_children, ChildRow, ChildStatus, CHILDREN_DOC};
use super::requests::{admit_spawns, SpawnKwargs, SpawnSpec};
use super::task::ReportMode;
use super::Children;
use crate::child_workspace::WorkspaceMode;
use crate::durable::deps::HostCall;
use crate::durable::optchat::user_text;
use crate::durable::tool_contract;

/// `worker_assign`: a new task for a worker.
pub const WORKER_ASSIGN: &str = "worker_assign";
/// `worker_forward`: the user's words for the running work.
pub const WORKER_FORWARD: &str = "worker_forward";
/// `worker_status`: where each worker stands.
pub const WORKER_STATUS: &str = "worker_status";

/// The first worker's name.
const DEFAULT_WORKER: &str = "worker";
/// The durable identities of the tools' contracts.
const ASSIGN_VERSION: &str = "worker_assign@1";
const FORWARD_VERSION: &str = "worker_forward@1";
const STATUS_VERSION: &str = "worker_status@1";
/// A page of main's transcript read for the user's messages.
const MESSAGES_PAGE: usize = 64;

const ASSIGN_DESCRIPTION: &str = "Hand work to your worker as a new task. The user's \
messages since your last hand-over go to the worker word for word (you do not repeat \
them); `note` adds your own words, labeled as yours. The first call creates the worker; \
a busy worker refuses (forward context or a redirect instead, or pass `fresh: true` to \
start another worker for unrelated work).";
const FORWARD_DESCRIPTION: &str = "Send the user's latest messages, word for word, to \
the worker's running task, placed between its tool calls (never interrupting one). \
`kind`: `context` (information or an idea to fold in; the worker keeps its course) or \
`redirect` (a change of course; the worker re-plans). `note` adds your own words, \
labeled as yours. A paused worker wakes for it.";
const STATUS_DESCRIPTION: &str = "Where each worker stands: running, paused, idle or \
stopped, its task, and its last answer. Read the worker's whole chat with \
`zoom(\"worker\")`.";

/// Main's hand-over state (`eukhe.workers` on the calling conversation).
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct WorkersState {
    /// The newest user message (its entry id) handed to a worker.
    #[serde(default)]
    pub(crate) cursor: u64,
    /// The user paused the worker tree (`pause_workers`); a resume or a
    /// forward clears it.
    #[serde(default)]
    pub(crate) paused: bool,
}

pub(crate) static WORKERS_DOC: ConversationDoc<WorkersState> = match ConversationDoc::define(
    DocDefinition {
        kind: "eukhe.workers",
        version: 1,
        initial: WorkersState::default,
        migrate: None,
        checkpoint_when: None,
    },
    // A fork's messages were handed over by the conversation it forked.
    LatestFork::Current,
) {
    Ok(token) => token,
    Err(_) => panic!("eukhe.workers has a valid version"),
};

async fn read_state(
    reader: &(impl DocumentReader + ?Sized),
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<WorkersState> {
    match reader.snapshot(&WORKERS_DOC, conversation_id, cx).await? {
        None => Ok(WorkersState::default()),
        Some(value) => Ok(from_json(&JsonValue::Object(value))?),
    }
}

/// Inside a commit: the user's messages through entry `cursor` are handed
/// over.
pub(super) async fn tx_hand_over(
    tx: &Tx,
    conversation_id: ConversationId,
    cursor: u64,
) -> SessionResult<()> {
    tx.doc(&WORKERS_DOC, conversation_id)
        .await?
        .set("cursor", to_json(&cursor)?)?;
    Ok(())
}

async fn set_paused(
    harness: &Harness,
    conversation_id: ConversationId,
    paused: bool,
    cx: &Context,
) -> SessionResult<()> {
    let conversation = harness
        .conversation(conversation_id, cx)
        .await?
        .ok_or_else(|| {
            SessionError::error(format!("Conversation {conversation_id} does not exist"))
        })?;
    conversation
        .commit(
            move |tx| async move {
                tx.doc(&WORKERS_DOC, conversation_id)
                    .await?
                    .set("paused", to_json(&paused)?)?;
                Ok(())
            },
            cx,
        )
        .await
}

/// The user's own messages after entry `cursor` of `conversation_id`, in
/// transcript order: (entry id, text as the user wrote it).
async fn user_messages(
    harness: &Harness,
    conversation_id: ConversationId,
    cursor: u64,
    cx: &Context,
) -> SessionResult<Vec<(u64, String)>> {
    let conversation = harness
        .conversation(conversation_id, cx)
        .await?
        .ok_or_else(|| {
            SessionError::error(format!("Conversation {conversation_id} does not exist"))
        })?;
    let mut messages = Vec::new();
    let mut page_cursor = None;
    loop {
        let page = conversation
            .entries(
                ConversationEntryQuery {
                    min_entry_id: Some(EntryId::from_number(cursor.saturating_add(1))),
                    max_entry_id: None,
                    order: Some(ScanOrder::Ascending),
                },
                MESSAGES_PAGE,
                page_cursor,
                cx,
            )
            .await?;
        for entry in &page.items {
            if entry.kind != USER_ENTRY.kind() {
                continue;
            }
            if UserData::decode(entry.data.as_ref())?.origin != InputOrigin::User {
                continue;
            }
            for message in entry.model.as_deref().unwrap_or_default() {
                if let Message::User(user) = message {
                    messages.push((entry.id.get(), user_text(&user.content)));
                }
            }
        }
        match page.next {
            Some(next) => page_cursor = Some(next),
            None => break,
        }
    }
    Ok(messages)
}

/// What one hand-over carries: the body the worker reads, the user's
/// messages it holds (verbatim, in order), main's note, and the cursor
/// after it.
struct HandOver {
    body: String,
    messages: Vec<String>,
    note: Option<String>,
    cursor: u64,
}

impl HandOver {
    /// The row details the worker's message carries, and main's tool row
    /// shows: exactly what went.
    fn details(&self, kind: ChildMessageKind, worker: &str) -> Map<String, Value> {
        let mut details = Map::new();
        details.insert("deliveryKind".to_owned(), json!(kind.as_str()));
        details.insert("userMessages".to_owned(), json!(self.messages));
        if let Some(note) = &self.note {
            details.insert("note".to_owned(), json!(note));
        }
        details.insert("worker".to_owned(), json!(worker));
        details
    }
}

/// The user's messages since the last hand-over, picked by the compiled
/// core (`forward_pick`): refuses when there is neither a new message nor
/// a note.
async fn hand_over(
    harness: &Harness,
    api: &dyn ToolExecutionApi,
    note: Option<String>,
    cx: &Context,
) -> SessionResult<HandOver> {
    let conversation_id = api.conversation_id();
    let state = read_state(api, conversation_id, cx).await?;
    let messages = user_messages(harness, conversation_id, state.cursor, cx).await?;
    let pairs: Vec<(u64, &str)> = messages
        .iter()
        .map(|(id, text)| (*id, text.as_str()))
        .collect();
    let pick = forward_pick(state.cursor, &pairs, note.as_deref())
        .map_err(|error| SessionError::error(format!("{error:#}")))?;
    if pick.picked.is_empty() && note.is_none() {
        return Err(SessionError::error(
            "No new message from the user since the last hand-over, and no note: there is nothing to send",
        ));
    }
    let picked: Vec<String> = messages
        .into_iter()
        .filter(|(id, _)| pick.picked.contains(id))
        .map(|(_, text)| text)
        .collect();
    Ok(HandOver {
        body: pick.body,
        messages: picked,
        note,
        cursor: pick.cursor,
    })
}

/// The live worker rows of `conversation_id`, in creation order.
async fn worker_rows(
    reader: &(impl DocumentReader + ?Sized),
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<Vec<ChildRow>> {
    Ok(read_children(reader, conversation_id, cx)
        .await?
        .children
        .into_values()
        .filter(|row| row.worker && !row.is_deleted())
        .collect())
}

/// Where a worker row stands, `paused` when main paused the tree.
fn run_state(row: &ChildRow, paused: bool) -> WorkerRunState {
    if row.is_deleted() {
        return WorkerRunState::Stopped;
    }
    match row.status {
        ChildStatus::Spawning | ChildStatus::Running if paused => WorkerRunState::Paused,
        ChildStatus::Spawning | ChildStatus::Running => WorkerRunState::Running,
        ChildStatus::Done | ChildStatus::Error | ChildStatus::Cancelled if !row.settled => {
            WorkerRunState::Running
        }
        ChildStatus::Done | ChildStatus::Error | ChildStatus::Cancelled => WorkerRunState::Idle,
    }
}

/// The wire row of one worker.
fn session_worker(row: &ChildRow, paused: bool) -> SessionWorker {
    SessionWorker {
        active_session_id: row
            .active_session_id
            .clone()
            .unwrap_or_else(|| row.session_id.clone()),
        session_id: row.session_id.clone(),
        name: row.session_name.clone(),
        state: run_state(row, paused),
    }
}

/// The workers of `conversation_id` (main's summary `workers`), in
/// creation order.
///
/// # Errors
///
/// Document read failures.
pub async fn list_workers(
    reader: &(impl DocumentReader + ?Sized),
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<Vec<SessionWorker>> {
    let paused = read_state(reader, conversation_id, cx).await?.paused;
    Ok(worker_rows(reader, conversation_id, cx)
        .await?
        .iter()
        .map(|row| session_worker(row, paused))
        .collect())
}

/// A live stream of main's workers (its summary `workers`): the current
/// rows first, then the rows after every commit that changed its children
/// registry or its hand-over state, when they changed. Dropping it stops
/// the subscription.
pub struct WorkerUpdates {
    receiver: mpsc::UnboundedReceiver<Vec<SessionWorker>>,
    unsubscribe: Unsubscribe,
    task: JoinHandle<()>,
}

impl WorkerUpdates {
    /// The next changed rows; `None` once the Harness closed or a read
    /// failed.
    pub async fn next(&mut self) -> Option<Vec<SessionWorker>> {
        self.receiver.recv().await
    }
}

impl Drop for WorkerUpdates {
    fn drop(&mut self) {
        self.unsubscribe.unsubscribe();
        self.task.abort();
    }
}

/// Whether `publication` changed a document of `conversation_id` that
/// main's worker rows read.
fn changes_workers(publication: &CommitPublication, conversation_id: ConversationId) -> bool {
    let read = |kind: &str| {
        kind == CHILDREN_DOC.definition().kind || kind == WORKERS_DOC.definition().kind
    };
    publication.changes.iter().any(|change| match change {
        CommitChange::Document(DocumentCommitChange::Document {
            record,
            conversation_id: owner,
            ..
        }) => read(record.kind()) && *owner == Some(conversation_id),
        CommitChange::Document(DocumentCommitChange::Copy {
            record,
            conversation_id: owner,
            ..
        }) => read(record.kind()) && *owner == conversation_id,
        CommitChange::Conversation(_)
        | CommitChange::Entry(_)
        | CommitChange::Task(_)
        | CommitChange::Submission(_) => false,
    })
}

/// Watch the workers of `conversation_id`: the current rows first, then
/// every change (running, paused, idle, stopped). Cancelling `cx` ends the
/// stream.
///
/// # Errors
///
/// The Session is closed.
pub fn watch_workers(
    harness: &Harness,
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<WorkerUpdates> {
    let (ticks, mut ticked) = mpsc::unbounded_channel::<()>();
    let listener: CommitListener = Arc::new(move |publication, _| {
        if changes_workers(publication, conversation_id) {
            // A closed receiver means the stream ended; nothing to notify.
            let _ = ticks.send(());
        }
    });
    let unsubscribe = harness.subscribe_commits(listener)?;
    let (sender, receiver) = mpsc::unbounded_channel();
    let reader = harness.clone();
    let cx = cx.clone();
    let task = tokio::spawn(async move {
        let mut last: Option<Vec<SessionWorker>> = None;
        loop {
            let Ok(workers) = list_workers(&reader, conversation_id, &cx).await else {
                return;
            };
            if last.as_ref() != Some(&workers) {
                last = Some(workers.clone());
                if sender.send(workers).is_err() {
                    return;
                }
            }
            match await_with_context(ticked.recv(), &cx).await {
                Ok(Some(())) => {}
                Ok(None) | Err(_) => return,
            }
            // Coalesce a burst of commits into one read.
            while ticked.try_recv().is_ok() {}
        }
    });
    Ok(WorkerUpdates {
        receiver,
        unsubscribe,
        task,
    })
}

/// Pause or resume the worker tree of `conversation_id` (`pause_workers`,
/// `resume_workers` on main): each worker's own run and its descendants.
/// A pause cancels nothing; a worker with no work in flight is left alone
/// (its next task would wake it anyway). Answers the workers after it.
///
/// # Errors
///
/// A document read or commit failure, or a worker the host cannot reach.
pub async fn pause_workers(
    harness: &Harness,
    host: &dyn RlmSubagentHost,
    conversation_id: ConversationId,
    action: PauseAction,
    cx: &Context,
) -> anyhow::Result<Vec<SessionWorker>> {
    let rows = worker_rows(harness, conversation_id, cx).await?;
    set_paused(harness, conversation_id, action == PauseAction::Pause, cx).await?;
    pause_rows(host, rows.iter().filter(|row| !row.settled), action).await?;
    Ok(list_workers(harness, conversation_id, cx).await?)
}

/// Pause or resume this session's own run and its whole tree
/// (`pause_workers` / `resume_workers` with `ownRun`, a parent's call on
/// its worker): the run pause first, then each child of `conversation_id`
/// with work in flight.
///
/// # Errors
///
/// A document read or commit failure, or a child the host cannot reach.
pub async fn pause_own_tree(
    harness: &Harness,
    host: &dyn RlmSubagentHost,
    pause: &RunPause,
    conversation_id: ConversationId,
    action: PauseAction,
    cx: &Context,
) -> anyhow::Result<()> {
    pause.set(action, cx).await?;
    let rows = read_children(harness, conversation_id, cx).await?.children;
    pause_rows(
        host,
        rows.values()
            .filter(|row| !row.is_deleted() && !row.settled),
        action,
    )
    .await
}

/// Pause or resume the tree of each child of `rows`.
async fn pause_rows(
    host: &dyn RlmSubagentHost,
    rows: impl Iterator<Item = &ChildRow>,
    action: PauseAction,
) -> anyhow::Result<()> {
    for row in rows {
        host.pause(RlmChildPauseRequest {
            session_id: row.session_id.clone(),
            action,
        })
        .await?;
    }
    Ok(())
}

fn optional_text(params: &Value, key: &str) -> SessionResult<Option<String>> {
    match params.get(key) {
        None | Some(Value::Null) => Ok(None),
        Some(Value::String(text)) => Ok(Some(text.clone())),
        Some(_) => Err(SessionError::type_error(format!(
            "`{key}` must be a string"
        ))),
    }
}

/// The text result of a worker tool with its `details`.
fn result(text: String, mut details: Map<String, Value>, version: &str) -> ToolExecutionResult {
    details.insert("version".to_owned(), json!(version));
    ToolExecutionResult {
        output: Some(vec![UserContentBlock::Text(TextContent::new(text))]),
        details: Some(Value::Object(details).into()),
        ..ToolExecutionResult::default()
    }
}

/// The next free worker name: `worker`, then `worker-2`, `worker-3`, ...
fn fresh_name(rows: &[ChildRow]) -> String {
    let taken = |name: &str| rows.iter().any(|row| row.session_name == name);
    if !taken(DEFAULT_WORKER) {
        return DEFAULT_WORKER.to_owned();
    }
    // Among rows.len() + 1 names one is free.
    let last = u32::try_from(rows.len())
        .unwrap_or(u32::MAX)
        .saturating_add(2);
    (2..=last)
        .map(|n| format!("{DEFAULT_WORKER}-{n}"))
        .find(|name| !taken(name))
        .unwrap_or_else(|| DEFAULT_WORKER.to_owned())
}

async fn assign_call(
    children: Arc<Children>,
    params: Value,
    api: Arc<dyn ToolExecutionApi>,
    cx: Context,
) -> SessionResult<ToolExecutionResult> {
    let note = optional_text(&params, "note")?;
    let fresh = params
        .get("fresh")
        .and_then(Value::as_bool)
        .unwrap_or(false);
    let harness = children.harness.require()?;
    let conversation_id = api.conversation_id();
    let rows = worker_rows(&*api, conversation_id, &cx).await?;
    let name = match (optional_text(&params, "worker")?, fresh) {
        (Some(name), _) => name,
        (None, true) => fresh_name(&rows),
        (None, false) => DEFAULT_WORKER.to_owned(),
    };
    let handed = hand_over(&harness, &*api, note, &cx).await?;
    let details = handed.details(ChildMessageKind::Task, &name);
    let row = rows.iter().find(|row| row.session_name == name);
    let task = match row {
        None => {
            let spec = SpawnSpec {
                prompt: handed.body.clone(),
                kwargs: SpawnKwargs {
                    name: Some(name.clone()),
                    model: children.services.settings.manager().get_worker_model(),
                    thinking: None,
                    workspace: Some(WorkspaceMode::Shared),
                    label: None,
                    phase: None,
                    report: ReportMode::Inbox,
                },
                details: Some(details.clone()),
                worker: true,
            };
            let call = HostCall {
                data: Value::Null,
                cell_source_code: None,
                call: Some(Arc::clone(&api)),
            };
            admit_spawns(&children, &call, vec![spec], Some(handed.cursor))
                .await
                .map_err(|error| SessionError::error(format!("{error:#}")))?;
            "created it"
        }
        Some(row) if row.settled && row.status.is_terminal() => {
            assign(
                &children,
                &api,
                row.session_id.clone(),
                Assignment {
                    prompt: handed.body.clone(),
                    kind: ChildMessageKind::Task,
                    details: Some(details.clone()),
                },
                Some(handed.cursor),
            )
            .await?;
            "re-tasked it"
        }
        Some(row) => return Err(SessionError::error(child_busy(&row.session_name))),
    };
    Ok(result(
        format!(
            "Handed {} user message(s) to {name} as a new task ({task}); its report comes back as a message.",
            handed.messages.len()
        ),
        details,
        ASSIGN_VERSION,
    ))
}

async fn forward_call(
    children: Arc<Children>,
    params: Value,
    api: Arc<dyn ToolExecutionApi>,
    cx: Context,
) -> SessionResult<ToolExecutionResult> {
    let kind = match params.get("kind").and_then(Value::as_str) {
        Some("context") => ChildMessageKind::Context,
        Some("redirect") => ChildMessageKind::Redirect,
        _ => {
            return Err(SessionError::type_error(
                "`kind` must be \"context\" or \"redirect\"",
            ))
        }
    };
    let note = optional_text(&params, "note")?;
    let name = optional_text(&params, "worker")?.unwrap_or_else(|| DEFAULT_WORKER.to_owned());
    let harness = children.harness.require()?;
    let conversation_id = api.conversation_id();
    let rows = worker_rows(&*api, conversation_id, &cx).await?;
    let Some(row) = rows.iter().find(|row| row.session_name == name) else {
        return Err(SessionError::error(format!(
            "No worker named \"{name}\" yet: hand work over with {WORKER_ASSIGN}"
        )));
    };
    let handed = hand_over(&harness, &*api, note, &cx).await?;
    let details = handed.details(kind, &name);
    if row.settled && row.status.is_terminal() {
        // No running work to join: the words start a new watched task.
        assign(
            &children,
            &api,
            row.session_id.clone(),
            Assignment {
                prompt: handed.body.clone(),
                kind,
                details: Some(details.clone()),
            },
            Some(handed.cursor),
        )
        .await?;
    } else {
        let call_id = api.call_id().to_owned();
        children
            .services
            .host
            .prompt(RlmChildPromptRequest {
                idempotency_key: format!("rlm:forward:{call_id}"),
                session_id: row.session_id.clone(),
                rlm_child_id: row.rlm_child_id.clone(),
                prompt: handed.body.clone(),
                kind,
                row_id: format!("forward:{call_id}"),
                details: Some(details.clone()),
            })
            .await
            .map_err(|error| SessionError::error(format!("{error:#}")))?;
        let cursor = handed.cursor;
        api.commit(
            move |tx| async move { tx_hand_over(&tx, conversation_id, cursor).await },
            &cx,
        )
        .await?;
        // A paused tree wakes for the user's words, after they are queued:
        // the parked run places them at the boundary it resumes from.
        if read_state(&*api, conversation_id, &cx).await?.paused {
            pause_workers(
                &harness,
                children.services.host.as_ref(),
                conversation_id,
                PauseAction::Resume,
                &cx,
            )
            .await
            .map_err(|error| SessionError::error(format!("{error:#}")))?;
        }
    }
    Ok(result(
        format!(
            "Sent {} user message(s) to {name} as {}.",
            handed.messages.len(),
            kind.as_str()
        ),
        details,
        FORWARD_VERSION,
    ))
}

async fn status_call(
    params: Value,
    api: Arc<dyn ToolExecutionApi>,
    cx: Context,
) -> SessionResult<ToolExecutionResult> {
    let only = optional_text(&params, "worker")?;
    let conversation_id = api.conversation_id();
    let paused = read_state(&*api, conversation_id, &cx).await?.paused;
    let rows = worker_rows(&*api, conversation_id, &cx).await?;
    let workers: Vec<Value> = rows
        .iter()
        .filter(|row| only.as_deref().is_none_or(|name| row.session_name == name))
        .map(|row| {
            json!({
                "name": row.session_name,
                "state": run_state(row, paused),
                "task": row.label,
                "lastAnswer": row.answer_preview,
                "error": row.error,
            })
        })
        .collect();
    let text = if workers.is_empty() {
        format!("No worker yet: {WORKER_ASSIGN} creates one.")
    } else {
        serde_json::to_string_pretty(&workers)
            .map_err(|error| SessionError::error(format!("{error}")))?
    };
    let mut details = Map::new();
    details.insert("workers".to_owned(), Value::Array(workers));
    Ok(result(text, details, STATUS_VERSION))
}

/// The three worker tools over `children`.
pub(super) fn worker_tools(children: &Arc<Children>) -> Vec<Arc<ToolRegistration>> {
    let assign_children = Arc::clone(children);
    let forward_children = Arc::clone(children);
    let note = || Type::optional(Type::string());
    let worker = || Type::optional(Type::string());
    vec![
        define_tool(ToolRegistration::new(
            WORKER_ASSIGN,
            ASSIGN_DESCRIPTION,
            tool_contract::parameters(
                1,
                [
                    ("note", note()),
                    ("worker", worker()),
                    ("fresh", Type::optional(Type::boolean())),
                ],
            ),
            move |params, api, cx| assign_call(Arc::clone(&assign_children), params, api, cx),
        )),
        define_tool(ToolRegistration::new(
            WORKER_FORWARD,
            FORWARD_DESCRIPTION,
            tool_contract::parameters(
                1,
                [
                    (
                        "kind",
                        Type::union([Type::literal("context"), Type::literal("redirect")]),
                    ),
                    ("note", note()),
                    ("worker", worker()),
                ],
            ),
            move |params, api, cx| forward_call(Arc::clone(&forward_children), params, api, cx),
        )),
        define_tool(ToolRegistration::new(
            WORKER_STATUS,
            STATUS_DESCRIPTION,
            tool_contract::parameters(1, [("worker", worker())]),
            status_call,
        )),
    ]
}
