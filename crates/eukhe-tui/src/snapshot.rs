//! Attach/snapshot reconstruction: wire data from the daemon (slim attach
//! results, streamed session events) folded into UI transcript items.

use crate::chat::{AssistantMessage, ChatEntry, MessageBlock, ToolCallCard, ToolResultView};
use eukhe_types::daemon::{
    DaemonEventCursor, DaemonReplayInfo, DaemonSessionSnapshot, SessionActionSnapshot,
};
use eukhe_types::session::AgentMessage;
use serde::Deserialize;
use serde_json::Value;
use std::collections::HashMap;

/// The slim attach result: the `data` object of a successful `attach`
/// response (`createAttachResult` wire shape).
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AttachData {
    pub active_session_id: String,
    /// Slim attach carries summary/state/messages inside the snapshot.
    pub snapshot: DaemonSessionSnapshot,
    #[serde(default)]
    pub replay: Option<DaemonReplayInfo>,
    #[serde(default)]
    pub last_event_sequence: Option<u64>,
    #[serde(default)]
    pub last_event_cursor: Option<DaemonEventCursor>,
    #[serde(default)]
    pub client: Option<AttachClient>,
}

/// Client block echoed back by attach.
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AttachClient {
    pub id: String,
    #[serde(default)]
    pub capabilities: Vec<String>,
}

/// A reconstructed attach: view-ready chat entries plus identity labels.
#[derive(Debug, Clone, Default)]
pub struct Reconstructed {
    pub chat: Vec<ChatEntry>,
    /// Current model id (`state.model.id`), when the session reports one.
    pub model_id: Option<String>,
    /// The current model's provider (`state.model.provider`), when the
    /// session reports one: the picker resolves the current-model catalog
    /// entry by provider plus id, so a same-id entry under another
    /// provider never wins (older daemons report no provider).
    pub model_provider: Option<String>,
    /// The tray effort suffix for that model (TS `getModelContextLabel`),
    /// when the state's model carries its reasoning level.
    pub thinking_suffix: Option<String>,
    /// The tray's context usage (`state.contextUsage`): the snapshot
    /// feeds the first frame's tray row without a stats round-trip.
    /// `None` clears the tray display.
    pub context_usage: Option<crate::chrome::ContextUsage>,
    /// Session display name.
    pub session_name: Option<String>,
    /// Session id of the persisted session file.
    pub session_id: String,
    /// The worker generation of the attach's event cursor (the resume
    /// protocol's generation): disambiguates event-sequence values
    /// across worker restarts for the cross-view layout handoff's key
    /// (`view::handoff`) -- a restarted worker's sequence restarts, so the
    /// generation must match too.
    pub event_generation: String,
    /// The session's goal state (`state.goal`), when the snapshot reports
    /// one (TS `snapshot.ts: goal: session.goalState`).
    pub goal: Option<eukhe_types::goal::GoalState>,
    pub last_event_sequence: u64,
    /// Whether the attach supplied the resume cursor (the event
    /// sequence AND the generation): the reconstruction collapses an
    /// absent cursor to default key values, and the layout handoff
    /// refuses to key on those (`view::handoff`).
    pub cursor_present: bool,
    /// The queued input parked behind the run (`state.sessionActions`) so an
    /// attach re-syncs the queue strip (TS re-reads the queue after
    /// subscribe because a `session_action_update` in the gap is lost).
    pub queued: crate::queued::QueuedMessages,
    /// The LAST HUMAN PROMPT's wall-clock time (unix ms): the newest
    /// user message's `timestamp` in fold order. The rebuilt loader
    /// anchors its elapsed clock here (the operator's 2026-09-28
    /// rule: the waiting/executing timer counts since the last human
    /// prompt and never resets on a view transition -- an agents-view
    /// round trip re-attaches mid-turn and the clock keeps its
    /// anchor). `None` when no user message carries a timestamp (an
    /// old snapshot or a seeded replay) -- the loader then keeps its
    /// re-attach-instant anchor.
    pub last_user_prompt_ms: Option<u64>,
    /// The session's effective service tier (`state.serviceTier`), the
    /// `/fast` toggle's baseline.
    pub service_tier: Option<String>,
}

impl Reconstructed {
    /// Fold one raw message into the chat entries. A `toolResult` message
    /// does not add a row WHEN it completes the pending tool card its
    /// `toolCallId` refers to (the TS transcript replay updates the
    /// pending tool component instead of rendering a new row); a result
    /// that matches no pending card keeps its standalone card exactly
    /// like the live `AgentView::push` path (the orphan never
    /// disappears from the rebuilt transcript).
    pub fn push_message(&mut self, message: &AgentMessage) {
        if let Some(result) = tool_result_message_view(message) {
            if let Some(view) = apply_tool_result(&mut self.chat, result) {
                self.chat
                    .push(ChatEntry::Tool(Box::new(crate::chat::ToolCallCard {
                        id: view.id,
                        name: view.name,
                        args: serde_json::Value::Null,
                        started: true,
                        result: Some(view.view),
                        ..Default::default()
                    })));
            }
            return;
        }
        self.chat.extend(message_value_to_entries(message));
    }
}

/// A decoded `toolResult` transcript message: the id of the tool call it
/// completes plus the result view rendered on the matching card.
struct ToolResultReplay {
    tool_call_id: String,
    /// The wire `toolName` (the orphan card's own name when no pending
    /// card matches).
    tool_name: String,
    view: crate::chat::ToolResultView,
}

/// Decode a `role: "toolResult"` message into its replay view; `None` for
/// any other message.
fn tool_result_message_view(message: &AgentMessage) -> Option<ToolResultReplay> {
    let AgentMessage::ToolResult(result) = message else {
        return None;
    };
    Some(ToolResultReplay {
        tool_call_id: result.tool_call_id.clone(),
        tool_name: result.tool_name.clone(),
        view: crate::chat::ToolResultView {
            content: result
                .content
                .iter()
                .map(crate::tool_card::content_block_value)
                .collect(),
            details: result.details.clone().unwrap_or(Value::Null),
            is_error: result.is_error,
        },
    })
}

/// Complete the first pending tool card matching `result`'s tool call
/// id (the TS `renderedPendingTools` replay: results land on the card,
/// never as a new transcript row). A result that matches no pending
/// card comes back whole: the caller keeps its standalone orphan card
/// (the live `AgentView::push` path's twin).
fn apply_tool_result(chat: &mut [ChatEntry], result: ToolResultReplay) -> Option<OrphanResult> {
    let ToolResultReplay {
        tool_call_id,
        tool_name,
        view,
    } = result;
    for entry in chat.iter_mut() {
        if let ChatEntry::Tool(card) = entry {
            if card.id == tool_call_id && card.result.is_none() {
                card.started = true;
                // Replayed cards never saw the live execution: the timing
                // collapses to the rebuild instant, so the bash `Took` row
                // renders the same `0.0s` the TS component does on replay.
                let now = std::time::Instant::now();
                card.started_at = Some(now);
                card.ended_at = Some(now);
                card.result = Some(view);
                card.result_partial = false;
                return None;
            }
        }
    }
    Some(OrphanResult {
        id: tool_call_id,
        name: tool_name,
        view,
    })
}

/// An unmatched replay result: keeps its standalone card.
struct OrphanResult {
    id: String,
    name: String,
    view: crate::chat::ToolResultView,
}

/// Replay a whole transcript: map every message to its rows, then fold
/// `toolResult` messages onto the pending tool cards their ids refer to.
/// Card ids are unique, so one id-to-index map replaces the per-result
/// card scan (a replay-scale fold stays linear).
/// TS `orderMessagesForTranscript`: the wire context is summary-first for
/// the model, but the transcript presents the compaction summary at its
/// chronological boundary -- after the retained messages
/// (`retainedMessageCount`), before anything appended after the
/// compaction. A missing count falls back to the timestamp split (TS
/// compatibility for pre-count summaries).
fn order_messages_for_transcript(messages: &[AgentMessage]) -> Vec<&AgentMessage> {
    let Some((summary_index, summary)) =
        messages
            .iter()
            .enumerate()
            .find_map(|(index, message)| match message {
                AgentMessage::CompactionSummary(summary) => Some((index, summary)),
                AgentMessage::User(_)
                | AgentMessage::Assistant(_)
                | AgentMessage::ToolResult(_)
                | AgentMessage::BashExecution(_)
                | AgentMessage::Custom(_)
                | AgentMessage::BranchSummary(_) => None,
            })
    else {
        return messages.iter().collect();
    };
    let mut rest: Vec<&AgentMessage> = messages
        .iter()
        .enumerate()
        .filter(|(index, _)| *index != summary_index)
        .map(|(_, message)| message)
        .collect();
    let boundary = match summary.retained_message_count {
        Some(retained) => usize::try_from(retained).unwrap_or(usize::MAX),
        None => rest
            .iter()
            .filter(|message| message.timestamp() < summary.timestamp)
            .count(),
    }
    .min(rest.len());
    rest.insert(boundary, &messages[summary_index]);
    rest
}

pub fn transcript_to_entries(messages: &[AgentMessage]) -> Vec<ChatEntry> {
    let ordered = order_messages_for_transcript(messages);
    let mut chat: Vec<ChatEntry> = Vec::new();
    let mut card_index: HashMap<String, Vec<usize>> = HashMap::new();
    for message in ordered {
        if let Some(result) = tool_result_message_view(message) {
            let tool_call_id = result.tool_call_id.clone();
            if let Some(result) = settle_last_pending(
                &mut chat,
                card_index.get(&tool_call_id).map(Vec::as_slice),
                result,
            ) {
                // No pending card took the result (a true orphan, or a
                // leftover settle): it keeps its standalone card AT ITS
                // OWN WIRE POSITION - exactly the live push path's
                // semantics (the result never crosses a later reused
                // invocation, and condensation never spans it).
                chat.push(orphan_card(result));
            }
            continue;
        }
        // The retry-episode collapse (SANCTIONED DIVERGENCE, operator
        // ruling 2026-09-23): a `provider_retry_outcome` row replaces the
        // failed attempts its episode superseded, so the rebuilt chat
        // shows ONE line per episode instead of the per-attempt error
        // rows TS renders. The superseded rows sit at the tail (attempts
        // are appended in order), and the collapse never touches tool
        // cards (their failures ride the cards, not error-only rows).
        if matches!(message, AgentMessage::Custom(custom)
            if eukhe_types::custom_type::CustomType::parse(&custom.custom_type)
                == eukhe_types::custom_type::CustomType::ProviderRetryOutcome)
        {
            while chat.last().is_some_and(is_superseded_attempt_row) {
                chat.pop();
            }
        }
        let first_new = chat.len();
        chat.extend(message_value_to_entries(message));
        for (offset, entry) in chat[first_new..].iter().enumerate() {
            if let ChatEntry::Tool(card) = entry {
                card_index
                    .entry(card.id.clone())
                    .or_default()
                    .push(first_new + offset);
            }
        }
    }
    chat
}

/// Settle one result onto the LAST pending card among `indices` (the
/// live `rposition` semantics). `Some(result)` hands the result back
/// whole for the caller's deferral or orphan handling; `None` settled
/// it.
fn settle_last_pending(
    chat: &mut [ChatEntry],
    indices: Option<&[usize]>,
    result: ToolResultReplay,
) -> Option<ToolResultReplay> {
    let Some(indices) = indices else {
        return Some(result);
    };
    let pending = indices.iter().rev().copied().find(
        |&index| matches!(chat.get(index), Some(ChatEntry::Tool(card)) if card.result.is_none()),
    );
    let Some(index) = pending else {
        return Some(result);
    };
    let ToolResultReplay {
        tool_call_id: _,
        tool_name: _,
        view,
    } = result;
    if let Some(ChatEntry::Tool(card)) = chat.get_mut(index) {
        card.started = true;
        // Replayed cards never saw the live execution: the timing
        // collapses to the rebuild instant, so the bash `Took` row
        // renders the same `0.0s` the TS component does on replay.
        let now = std::time::Instant::now();
        card.started_at = Some(now);
        card.ended_at = Some(now);
        card.result = Some(view);
        card.result_partial = false;
    }
    None
}

/// The standalone card a true orphan result keeps (the live push
/// path's twin).
fn orphan_card(result: ToolResultReplay) -> ChatEntry {
    let ToolResultReplay {
        tool_call_id,
        tool_name,
        view,
    } = result;
    ChatEntry::Tool(Box::new(crate::chat::ToolCallCard {
        id: tool_call_id,
        name: tool_name,
        args: serde_json::Value::Null,
        started: true,
        result: Some(view),
        ..Default::default()
    }))
}

/// The durable session id in an attach snapshot's `state` (its
/// `sessionId`, empty when the state has none).
pub(crate) fn state_session_id(state: &Value) -> &str {
    state
        .get("sessionId")
        .and_then(Value::as_str)
        .unwrap_or_default()
}

/// Reconstruct the view state from slim attach data.
///
/// # Errors
///
/// The state's `sessionActions` does not decode.
pub fn reconstruct(attach: &AttachData) -> Result<Reconstructed, serde_json::Error> {
    let snapshot = &attach.snapshot;
    let messages = transcript_to_entries(&snapshot.messages);
    let state = Some(&snapshot.state);
    let (model_id, model_provider) = state
        .and_then(|state| state.get("model"))
        .and_then(model_identity_value)
        .map_or((None, None), |(id, provider)| (Some(id), provider));
    let thinking_suffix = state.and_then(crate::chrome::tray_thinking_suffix);
    let context_usage = state
        .and_then(|state| state.get("contextUsage"))
        .and_then(crate::chrome::ContextUsage::from_wire);
    let session_name = state
        .and_then(|state| state.get("sessionName"))
        .and_then(Value::as_str)
        .map(str::to_string);
    let session_id = state_session_id(&snapshot.state).to_string();
    let last_event_sequence = snapshot.last_event_sequence;
    let event_generation = attach
        .last_event_cursor
        .as_ref()
        .or(snapshot.last_event_cursor.as_ref())
        .map(|cursor| cursor.generation.clone())
        .unwrap_or_default();
    // The cursor-presence gate (`view::handoff`): the handoff refuses to
    // key on a collapsed identity (an empty generation or session).
    let cursor_present = !event_generation.is_empty() && !session_id.is_empty();
    let goal = state
        .and_then(|state| state.get("goal"))
        .and_then(|goal| serde_json::from_value::<eukhe_types::goal::GoalState>(goal.clone()).ok());
    let queued = match state.and_then(|state| state.get("sessionActions")) {
        Some(actions) => decoder::queued_messages(&SessionActionSnapshot::deserialize(actions)?),
        None => crate::queued::QueuedMessages::default(),
    };

    let service_tier = state
        .and_then(|state| state.get("serviceTier"))
        .and_then(Value::as_str)
        .map(str::to_string);
    let last_user_prompt_ms = snapshot
        .messages
        .iter()
        .rev()
        .find_map(|message| match message {
            AgentMessage::User(user) => Some(user.timestamp),
            AgentMessage::Assistant(_)
            | AgentMessage::ToolResult(_)
            | AgentMessage::BashExecution(_)
            | AgentMessage::Custom(_)
            | AgentMessage::BranchSummary(_)
            | AgentMessage::CompactionSummary(_) => None,
        });
    Ok(Reconstructed {
        chat: messages,
        model_id,
        model_provider,
        thinking_suffix,
        context_usage,
        session_name,
        session_id,
        event_generation,
        goal,
        last_event_sequence,
        cursor_present,
        queued,
        service_tier,
        last_user_prompt_ms,
    })
}

/// The model id and provider from a `state.model` wire value
/// (`{id, provider}` or a display string): the provider is `None` for the
/// display-string form and the object form that omits it (older daemons),
/// and the whole identity is `None` when no id parses -- a provider
/// without an id matches nothing in the catalog.
fn model_identity_value(model: &Value) -> Option<(String, Option<String>)> {
    match model {
        Value::String(label) => Some((label.clone(), None)),
        Value::Object(map) => {
            let id = map.get("id").and_then(Value::as_str)?;
            let provider = map
                .get("provider")
                .and_then(Value::as_str)
                .map(str::to_string);
            Some((id.to_string(), provider))
        }
        _ => None,
    }
}

/// Parse attach data out of a successful attach/create response payload.
///
/// # Errors
///
/// Returns `Err` when the payload does not decode into `AttachData`
/// (an unrecognizable daemon attach result).
pub fn attach_data_from_response(data: Value) -> anyhow::Result<AttachData> {
    serde_json::from_value(data).map_err(|error| {
        anyhow::anyhow!("the daemon returned an unrecognizable attach result: {error}")
    })
}

pub use decoder::{
    content_text, event_to_update, message_value_to_entries, queued_messages, user_display_text,
    working_message_from_update, RetryStartReason, TurnUpdate,
};
mod decoder;

pub use tool_fold::{
    apply_streamed_tool_card, apply_tool_execution_start, assistant_error_row,
    assistant_message_parts, assistant_value_to_entries, is_superseded_attempt_row,
    settle_pending_tool_cards, AssistantErrorRow,
};
mod tool_fold;

#[cfg(test)]
mod tests;
