//! Session-tree navigation commands: the worker-side handlers for
//! `get_session_tree`, `get_user_messages_for_forking`,
//! `set_session_entry_label`, `navigate_tree`, `fork`, and
//! `abort_branch_summary` over the durable session.
//!
//! The tree is the session's user-facing conversations ([`tree`]). Moving
//! the leaf (`navigate_tree`) makes another conversation the main one: the
//! conversation that already ends at the new leaf, else a fork of the
//! target's conversation at it (`fork_main_conversation`). `fork` always
//! forks. Either way the moved-to conversation is shown on the wire
//! (`Worker::show_conversation`); the storage, the session id, and the
//! kernels of other conversations stay. Branch summaries are
//! `eukhe.branch-summary` entries written into the moved-to conversation
//! ([`summary`]); labels live in the `eukhe.daemon.labels` document
//! ([`labels`]).

mod labels;
mod summary;
#[cfg(test)]
mod tests;
mod tree;

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, PoisonError};

use eukhe_chord::context::{AbortController, Context, BACKGROUND_CONTEXT};
use eukhe_core::durable::{fork_main_conversation, ForkPoint};
use eukhe_core::session_engine::branch_summarization::collect_entries_for_branch_summary;
use eukhe_durable::harness::types::{ConversationAbortOptions, InputSubmissionDraft, WhenBusy};
use eukhe_durable::harness::{Conversation, ConversationEntryQuery, Harness};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::{ConversationId, EntryId, EntryRecord};
use serde_json::{json, Value};

use crate::protocol::{response_failure, response_success, DaemonResponse};
use crate::worker::durable_host::bridge::{QueuedInput, QueuedMode};
use crate::worker::{HostedSession, SessionSlot, Worker};
use summary::{SummaryOutcome, SummaryRequest};
use tree::{custom_entry_text, is_custom_entry, user_entry_text, SessionTree};

/// The tree surface the dispatch table reaches directly: the getters, the
/// label write, and the branch-summary abort slot.
pub(crate) struct TreeNavigation {
    session: SessionSlot,
    /// The live branch-summary run: each run replaces it (TS
    /// `_branchSummaryAbortController`), numbered so a finished run clears
    /// only its own slot.
    abort: Mutex<Option<(u64, AbortController)>>,
    runs: AtomicU64,
}

impl TreeNavigation {
    pub(crate) fn new(session: SessionSlot) -> Self {
        TreeNavigation {
            session,
            abort: Mutex::new(None),
            runs: AtomicU64::new(0),
        }
    }

    /// `abort_branch_summary`: abort the live run; the TS handler always
    /// replies success.
    pub(crate) fn abort(&self) {
        if let Some((_, controller)) = self
            .abort
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .as_ref()
        {
            controller.abort(None);
        }
    }

    fn begin_summary(&self) -> (u64, AbortController) {
        let run = self.runs.fetch_add(1, Ordering::Relaxed) + 1;
        let controller = AbortController::new();
        *self.abort.lock().unwrap_or_else(PoisonError::into_inner) =
            Some((run, controller.clone()));
        (run, controller)
    }

    fn end_summary(&self, run: u64) {
        let mut slot = self.abort.lock().unwrap_or_else(PoisonError::into_inner);
        if slot.as_ref().is_some_and(|(live, _)| *live == run) {
            *slot = None;
        }
    }

    /// The hosted session and its tree, or the failure `command` answers.
    #[allow(clippy::result_large_err)] // the error is the wire response itself
    async fn load(
        &self,
        command: &str,
    ) -> Result<(std::sync::Arc<HostedSession>, SessionTree), DaemonResponse> {
        let Some(hosted) = self.session.get() else {
            return Err(response_failure(
                None,
                command,
                "Session is still initializing",
                None,
            ));
        };
        let fail = |error: SessionError| response_failure(None, command, &error.to_string(), None);
        let main = hosted.main().map_err(fail)?;
        let tree = SessionTree::load(hosted.harness(), main.id(), &BACKGROUND_CONTEXT)
            .await
            .map_err(fail)?;
        Ok((hosted, tree))
    }

    /// `get_session_tree`: every shown entry with its label plus the
    /// current leaf id (TS `getFlatTree` + `getLeafId`).
    pub(crate) async fn get_session_tree(&self) -> DaemonResponse {
        const COMMAND: &str = "get_session_tree";
        let (hosted, tree) = match self.load(COMMAND).await {
            Ok(loaded) => loaded,
            Err(response) => return response,
        };
        let labels = match labels::read_labels(hosted.harness(), &BACKGROUND_CONTEXT).await {
            Ok(labels) => labels,
            Err(error) => return response_failure(None, COMMAND, &error.to_string(), None),
        };
        response_success(
            None,
            COMMAND,
            Some(json!({
                "flatNodes": tree.flat_nodes(|id| labels.get(id)),
                "leafId": tree.leaf().map(|id| id.to_string()),
            })),
        )
    }

    /// `get_user_messages_for_forking`: the user messages with text (TS
    /// `getUserMessagesForForking`).
    pub(crate) async fn get_user_messages_for_forking(&self) -> DaemonResponse {
        const COMMAND: &str = "get_user_messages_for_forking";
        match self.load(COMMAND).await {
            Ok((_, tree)) => response_success(
                None,
                COMMAND,
                Some(json!({ "messages": tree.user_messages_for_forking() })),
            ),
            Err(response) => response,
        }
    }

    /// `set_session_entry_label`: set or clear (`label` absent or null) an
    /// entry's label (TS `appendLabelChange`; a missing target errors like
    /// the TS throw).
    pub(crate) async fn set_session_entry_label(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "set_session_entry_label";
        let entry_id = payload
            .get("entryId")
            .and_then(Value::as_str)
            .unwrap_or_default();
        let label = payload
            .get("label")
            .and_then(Value::as_str)
            .map(str::to_owned);
        let (hosted, tree) = match self.load(COMMAND).await {
            Ok(loaded) => loaded,
            Err(response) => return response,
        };
        if parse_entry_id(entry_id)
            .and_then(|id| tree.entry(id))
            .is_none()
        {
            return response_failure(None, COMMAND, &format!("Entry {entry_id} not found"), None);
        }
        match labels::set_label(
            hosted.harness(),
            entry_id.to_owned(),
            label,
            &BACKGROUND_CONTEXT,
        )
        .await
        {
            Ok(()) => response_success(None, COMMAND, None),
            Err(error) => response_failure(None, COMMAND, &error.to_string(), None),
        }
    }
}

/// A wire entry id (the decimal durable id).
fn parse_entry_id(id: &str) -> Option<EntryId> {
    id.parse().ok().map(EntryId::from_number)
}

/// Where the main conversation moves: the history of `source` through
/// `point` (`None`: before its first entry).
#[derive(Clone, Copy, Debug)]
struct MovePoint {
    source: ConversationId,
    point: Option<EntryId>,
}

impl MovePoint {
    /// At `record` itself.
    fn at(record: &EntryRecord) -> Self {
        Self {
            source: record.conversation_id,
            point: Some(record.id),
        }
    }

    /// Just before `record` in its conversation (TS: the leaf moves to the
    /// target's parent).
    async fn before(harness: &Harness, record: &EntryRecord, cx: &Context) -> SessionResult<Self> {
        let conversation = conversation(harness, record.conversation_id, cx).await?;
        let point = match record.id.get().checked_sub(1).filter(|id| *id > 0) {
            Some(max) => conversation
                .entries(
                    ConversationEntryQuery {
                        min_entry_id: None,
                        max_entry_id: Some(EntryId::from_number(max)),
                    },
                    1,
                    None,
                    cx,
                )
                .await?
                .items
                .first()
                .map(|entry| entry.id),
            None => None,
        };
        Ok(Self {
            source: record.conversation_id,
            point,
        })
    }

    fn fork_point(self) -> ForkPoint {
        self.point.map_or(ForkPoint::Start, ForkPoint::Entry)
    }

    /// TS `branchWithSummary`'s `fromId`: the new leaf, `"root"` before the
    /// first entry.
    fn summary_from_id(self) -> String {
        self.point
            .map_or_else(|| "root".to_owned(), |point| point.to_string())
    }
}

async fn conversation(
    harness: &Harness,
    id: ConversationId,
    cx: &Context,
) -> SessionResult<Conversation> {
    harness
        .conversation(id, cx)
        .await?
        .ok_or_else(|| SessionError::error(format!("Conversation {id} does not exist")))
}

/// Fork `target.source` at `target.point` and make the fork the main
/// conversation.
async fn fork_main(
    hosted: &HostedSession,
    target: MovePoint,
    cx: &Context,
) -> SessionResult<Conversation> {
    let source = conversation(hosted.harness(), target.source, cx).await?;
    let forked =
        fork_main_conversation(hosted.harness(), &source, target.fork_point(), None, cx).await?;
    hosted.session()?.reload_main(cx).await?;
    Ok(forked)
}

/// Make the history through `target` the main conversation: a
/// conversation that already ends there (a branch the user left), else a
/// fork.
async fn move_main(
    hosted: &HostedSession,
    tree: &SessionTree,
    main: ConversationId,
    target: MovePoint,
    cx: &Context,
) -> SessionResult<Conversation> {
    let existing = target.point.and_then(|point| {
        tree.conversations()
            .iter()
            .find(|tip| tip.id != main && tip.tip == Some(point))
    });
    match existing {
        Some(tip) => {
            let moved = conversation(hosted.harness(), tip.id, cx).await?;
            let session = hosted.session()?;
            session.set_main(&moved, cx).await?;
            session.reload_main(cx).await?;
            Ok(moved)
        }
        None => fork_main(hosted, target, cx).await,
    }
}

/// Submit `inputs` on `conversation`, in order, in their lanes.
async fn resubmit(
    conversation: &Conversation,
    inputs: Vec<QueuedInput>,
    cx: &Context,
) -> SessionResult<()> {
    for input in inputs {
        conversation
            .submit(
                InputSubmissionDraft {
                    request_id: None,
                    content: input.content,
                    when_busy: Some(match input.mode {
                        QueuedMode::Steer => WhenBusy::Steer,
                        QueuedMode::FollowUp => WhenBusy::FollowUp,
                    }),
                },
                cx,
            )
            .await?;
    }
    Ok(())
}

/// The parsed `navigate_tree` payload.
struct NavigateRequest {
    target_id: String,
    summarize: bool,
    custom_instructions: Option<String>,
    replace_instructions: bool,
    label: Option<String>,
}

impl NavigateRequest {
    fn parse(payload: &Value) -> Self {
        let text = |key: &str| payload.get(key).and_then(Value::as_str).map(str::to_owned);
        let flag = |key: &str| payload.get(key).and_then(Value::as_bool) == Some(true);
        Self {
            target_id: text("targetId").unwrap_or_default(),
            summarize: flag("summarize"),
            custom_instructions: text("customInstructions"),
            replace_instructions: flag("replaceInstructions"),
            label: text("label"),
        }
    }
}

impl Worker {
    /// Abort the main conversation's run when it is busy (TS
    /// `acquireQueuedWorkPause` + `waitForIdle`), answering the queued
    /// inputs the abort withdrew.
    async fn interrupt_main(
        &self,
        main: &Conversation,
        cx: &Context,
    ) -> SessionResult<Vec<QueuedInput>> {
        let (busy, inbox) = {
            let core = self.core.lock().unwrap_or_else(PoisonError::into_inner);
            let inbox = core
                .view
                .as_ref()
                .map(|view| view.inbox.clone())
                .unwrap_or_default();
            (core.is_busy(), inbox)
        };
        if !busy && inbox.is_empty() {
            return Ok(Vec::new());
        }
        main.abort(ConversationAbortOptions::default(), cx).await?;
        Ok(inbox)
    }

    /// `navigate_tree` (TS `AgentSession.navigateTree`): move the leaf onto
    /// a tree node, optionally summarizing the abandoned branch first. The
    /// response carries `editorText` when the target was a user message or
    /// custom message (the text re-enters the input bar) and the
    /// `summaryEntry` a summary wrote.
    pub(crate) async fn handle_navigate_tree(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "navigate_tree";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let _replacement_gate = self.replacement_gate.lock().await;
        let request = NavigateRequest::parse(payload);
        match self.navigate(&hosted, &request, &BACKGROUND_CONTEXT).await {
            Ok(data) => response_success(None, COMMAND, Some(data)),
            Err(error) => response_failure(None, COMMAND, &error, None),
        }
    }

    async fn navigate(
        &self,
        hosted: &HostedSession,
        request: &NavigateRequest,
        cx: &Context,
    ) -> Result<Value, String> {
        let text = text_of;
        let harness = hosted.harness();
        let main = hosted.main().map_err(text)?;
        let tree = SessionTree::load(harness, main.id(), cx)
            .await
            .map_err(text)?;
        let target_id = request.target_id.as_str();
        let Some(target) = parse_entry_id(target_id).and_then(|id| tree.entry(id)) else {
            return Err(format!("Entry {target_id} not found"));
        };
        let target = target.record.clone();
        // No-op when already at the target.
        if tree.leaf() == Some(target.id) {
            return Ok(json!({ "cancelled": false }));
        }
        let (point, editor_text) = if let Some(user_text) = user_entry_text(&target) {
            (
                MovePoint::before(harness, &target, cx)
                    .await
                    .map_err(text)?,
                Some(user_text),
            )
        } else if is_custom_entry(&target) {
            (
                MovePoint::before(harness, &target, cx)
                    .await
                    .map_err(text)?,
                custom_entry_text(&target),
            )
        } else {
            (MovePoint::at(&target), None)
        };
        let withdrawn = self.interrupt_main(&main, cx).await.map_err(text)?;

        // The abandoned-branch summary (TS `generateBranchSummary` over
        // `collectEntriesForBranchSummary`).
        let mut branch_summary = None;
        if request.summarize {
            let old_leaf = tree.leaf().map(|id| id.to_string());
            let collected = collect_entries_for_branch_summary(
                &tree.file_entries(),
                old_leaf.as_deref(),
                target_id,
            );
            if !collected.entries.is_empty() {
                let (run, controller) = self.tree_navigation.begin_summary();
                let outcome = summary::generate(
                    hosted.deps(),
                    &main,
                    SummaryRequest {
                        entries: &collected.entries,
                        custom_instructions: request.custom_instructions.as_deref(),
                        replace_instructions: request.replace_instructions,
                    },
                    controller.signal(),
                    cx,
                )
                .await;
                self.tree_navigation.end_summary(run);
                match outcome {
                    SummaryOutcome::Complete(summary) => branch_summary = Some(*summary),
                    SummaryOutcome::Aborted => {
                        resubmit(&main, withdrawn, cx).await.map_err(text)?;
                        return Ok(json!({ "cancelled": true, "aborted": true }));
                    }
                    SummaryOutcome::Failed(error) => {
                        resubmit(&main, withdrawn, cx).await.map_err(text)?;
                        return Err(error);
                    }
                }
            }
        }

        let moved = move_main(hosted, &tree, main.id(), point, cx)
            .await
            .map_err(text)?;
        let summary_entry = match branch_summary {
            Some(branch_summary) => Some(
                summary::write_summary(&moved, point.summary_from_id(), branch_summary, cx)
                    .await
                    .map_err(text)?,
            ),
            None => None,
        };
        // A created summary takes the label; a plain move labels the target.
        if let Some(label) = &request.label {
            let labeled = summary_entry.unwrap_or(target.id).to_string();
            labels::set_label(harness, labeled, Some(label.clone()), cx)
                .await
                .map_err(text)?;
        }
        self.show_conversation(hosted, &moved).await.map_err(text)?;
        resubmit(&moved, withdrawn, cx).await.map_err(text)?;
        self.push_roster_delta();
        let mut data = json!({ "cancelled": false });
        if let Some(editor_text) = editor_text {
            data["editorText"] = json!(editor_text);
        }
        if let Some(summary_entry) = summary_entry {
            let tree = SessionTree::load(harness, moved.id(), cx)
                .await
                .map_err(text)?;
            if let Some(entry) = tree.entry_json(summary_entry) {
                data["summaryEntry"] = entry;
            }
        }
        Ok(data)
    }

    /// `fork` (TS `AgentSessionRuntime.fork`): fork the conversation at an
    /// entry and continue on the fork. `position: "before"` (default)
    /// forks before a user message with its text returned as
    /// `selectedText`; `"at"` keeps the history through the entry. The
    /// running turn is aborted and its queued inputs dropped (TS disposes
    /// the replaced runtime's queue); a bad entry fails before anything
    /// moves.
    pub(crate) async fn handle_fork(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "fork";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let _replacement_gate = self.replacement_gate.lock().await;
        match self.fork(&hosted, payload, &BACKGROUND_CONTEXT).await {
            Ok(selected_text) => {
                let mut data = json!({ "cancelled": false });
                if let Some(selected_text) = selected_text {
                    data["selectedText"] = json!(selected_text);
                }
                response_success(None, COMMAND, Some(data))
            }
            Err(error) => response_failure(None, COMMAND, &error, None),
        }
    }

    async fn fork(
        &self,
        hosted: &HostedSession,
        payload: &Value,
        cx: &Context,
    ) -> Result<Option<String>, String> {
        const INVALID: &str = "Invalid entry ID for forking";
        let entry_id = payload
            .get("entryId")
            .and_then(Value::as_str)
            .unwrap_or_default();
        let at = payload.get("position").and_then(Value::as_str) == Some("at");
        let harness = hosted.harness();
        let main = hosted.main().map_err(text_of)?;
        let tree = SessionTree::load(harness, main.id(), cx)
            .await
            .map_err(text_of)?;
        let Some(target) = parse_entry_id(entry_id).and_then(|id| tree.entry(id)) else {
            return Err(INVALID.to_owned());
        };
        let (point, selected_text) = if at {
            (MovePoint::at(&target.record), None)
        } else {
            let text = user_entry_text(&target.record).ok_or_else(|| INVALID.to_owned())?;
            (
                MovePoint::before(harness, &target.record, cx)
                    .await
                    .map_err(text_of)?,
                Some(text),
            )
        };
        self.interrupt_main(&main, cx).await.map_err(text_of)?;
        let forked = fork_main(hosted, point, cx).await.map_err(text_of)?;
        self.show_conversation(hosted, &forked)
            .await
            .map_err(text_of)?;
        self.push_roster_delta();
        Ok(selected_text)
    }
}

// A `map_err` adapter: the error is consumed by the conversion.
#[allow(clippy::needless_pass_by_value)]
fn text_of(error: SessionError) -> String {
    error.to_string()
}
