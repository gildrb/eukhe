//! The request of a call (§6-§8). A root conversation's call is its run:
//! on the run's first request the call takes the chat's root-turn lease,
//! waits until everything before the run is in the chat log, renders the
//! settled view, and pins it in `eukhe.optchat.call`; every request of the
//! run then sends the pinned view, so the prompt-cache prefix holds across
//! tool rounds and across a crash. A subagent pins one view for its whole
//! conversation and logs nothing.

use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_durable::harness::types::{HookApi, HookResult, RequestMessages};
use eukhe_durable::harness::{Harness, LiveRun, LiveState, LIVE_DOC};
use eukhe_durable::session::SessionResult;
use eukhe_durable::types::{ConversationId, EntryId};
use eukhe_pi_ai::utils::transcript::get_current_system_message;
use eukhe_types::pi_ai::{
    CacheBreakpoint, Message, TextContent, UserContent, UserContentBlock, UserMessage,
};

use super::docs::{decode, write, CallState, CALL_DOC};
use super::lines::{lead_of, Lead};
use super::tools::memory_error;
use super::OptChat;
use crate::memory::MemoryRole;

/// The `before_request` transform of one request.
pub(super) async fn transform(
    chat: Arc<OptChat>,
    request: RequestMessages,
    api: HookApi,
    cx: Context,
) -> HookResult<RequestMessages> {
    let harness = chat.harness.require()?;
    let conversation = api.conversation_id();
    let (call, start) = match chat.role {
        MemoryRole::Root => {
            if !is_root_conversation(&harness, conversation, &cx).await? {
                return Ok(None);
            }
            let Some(run) = live_run(&harness, conversation, &cx).await? else {
                return Ok(None);
            };
            let key = run_key(&run);
            chat.turn
                .claim(&chat.memory, chat.turn_wait.as_ref())
                .await
                .map_err(|error| memory_error(&error))?;
            let call = match call_state(&harness, conversation, &cx).await? {
                Some(call) if call.run_key.as_deref() == Some(key.as_str()) => call,
                Some(_) | None => {
                    // Everything before the run is in the log before the
                    // view renders: the view covers it, the request drops it.
                    chat.flush().await?;
                    let call = pin(&chat, &harness, conversation, Some(key), &cx).await?;
                    chat.wake();
                    call
                }
            };
            (call, run_start(&harness, &run, &cx).await?)
        }
        MemoryRole::Subagent => {
            let call = match call_state(&harness, conversation, &cx).await? {
                Some(call) => call,
                None => pin(&chat, &harness, conversation, None, &cx).await?,
            };
            (call, None)
        }
    };
    let Some(handle) = harness.conversation(conversation, &cx).await? else {
        return Ok(None);
    };
    let view = handle.context(&cx).await?;
    let mut start_message = None;
    let mut state_rows: Vec<Message> = Vec::new();
    for (entry, contributed) in view.entries.iter().zip(&view.contributions) {
        if Some(entry.id) == start {
            start_message = contributed.first().cloned();
        }
        if lead_of(entry) == Lead::State {
            state_rows.extend(contributed.iter().cloned());
        }
    }
    let messages = request.messages;
    let start_at = start_message
        .and_then(|first| messages.iter().rposition(|message| *message == first))
        .unwrap_or(0);
    Ok(Some(RequestMessages {
        messages: request_messages(&call, messages, start_at, |message| {
            state_rows.contains(message)
        }),
    }))
}

/// Whether `conversation` is a root conversation of the session (no task
/// owns it): only those start from the view and are logged.
pub(super) async fn is_root_conversation(
    harness: &Harness,
    conversation: ConversationId,
    cx: &Context,
) -> SessionResult<bool> {
    let storage = Arc::clone(harness.storage());
    let line_cx = cx.clone();
    let record = harness
        .read_on_line(async move { Ok(storage.conversation(conversation, &line_cx).await?) })
        .await?;
    Ok(record.is_some_and(|record| record.owner.is_none()))
}

/// The conversation's live run, when busy.
pub(super) async fn live_run(
    harness: &Harness,
    conversation: ConversationId,
    cx: &Context,
) -> SessionResult<Option<LiveRun>> {
    match harness.snapshot(&LIVE_DOC, conversation, cx).await? {
        Some(value) => Ok(decode::<LiveState>(&value)?.run),
        None => Ok(None),
    }
}

/// The pinned call of `conversation`, if any.
pub(super) async fn call_state(
    harness: &Harness,
    conversation: ConversationId,
    cx: &Context,
) -> SessionResult<Option<CallState>> {
    match harness.snapshot(&CALL_DOC, conversation, cx).await? {
        Some(value) => Ok(Some(decode(&value)?)),
        None => Ok(None),
    }
}

/// A run's key: its first input (`pi.live.run.inputs[0]`), or its task for
/// a run without input.
pub(super) fn run_key(run: &LiveRun) -> String {
    match run.inputs.first() {
        Some(input) => format!("input:{input}"),
        None => format!("task:{}", run.task_id),
    }
}

/// The entry that starts a run: the placed entry of its first input.
pub(super) async fn run_start(
    harness: &Harness,
    run: &LiveRun,
    cx: &Context,
) -> SessionResult<Option<EntryId>> {
    let Some(&input) = run.inputs.first() else {
        return Ok(None);
    };
    let storage = Arc::clone(harness.storage());
    let line_cx = cx.clone();
    let record = harness
        .read_on_line(async move { Ok(storage.submission(input, &line_cx).await?) })
        .await?;
    Ok(record.and_then(|record| record.state.entry()))
}

/// Render the settled view (§6) and pin it as the call of `conversation`.
async fn pin(
    chat: &OptChat,
    harness: &Harness,
    conversation: ConversationId,
    run_key: Option<String>,
    cx: &Context,
) -> SessionResult<CallState> {
    let rendered = chat
        .memory
        .settled_render()
        .await
        .map_err(|error| memory_error(&error))?;
    let call = CallState {
        run_key,
        pieces: rendered.pieces(),
        through: rendered.messages,
        timestamp: now_millis(),
    };
    let pinned = call.clone();
    harness
        .commit(
            move |tx| async move {
                let draft = tx.doc(&CALL_DOC, conversation).await?;
                write(&draft, &pinned, &["runKey"])
            },
            cx,
        )
        .await?;
    Ok(call)
}

/// The request of a call (§7, §8): the system messages before the call's
/// leading user rows replayed into ONE system message; then ONE user
/// message holding the view pieces and ONE text block with the call's
/// leading user texts (the user's words, reports, nudges) joined by a
/// blank line, their images after it; then any harness state among those
/// leading rows; then the rest of the call. Messages before `start` (the
/// call's first message) are in the chat log and dropped.
pub(crate) fn request_messages(
    call: &CallState,
    mut messages: Vec<Message>,
    start: usize,
    is_state: impl Fn(&Message) -> bool,
) -> Vec<Message> {
    let mut run = messages.split_off(start.min(messages.len()));
    let mut systems: Vec<Message> = messages
        .into_iter()
        .filter(|message| matches!(message, Message::System(_)))
        .collect();
    let lead = run
        .iter()
        .take_while(|message| matches!(message, Message::User(_) | Message::System(_)))
        .count();
    let rest = run.split_off(lead);
    let mut texts: Vec<String> = Vec::new();
    let mut images: Vec<UserContentBlock> = Vec::new();
    let mut state_rows: Vec<Message> = Vec::new();
    for message in run {
        if matches!(message, Message::System(_)) {
            systems.push(message);
            continue;
        }
        if is_state(&message) {
            state_rows.push(message);
            continue;
        }
        let Message::User(user) = message else {
            continue;
        };
        match user.content {
            UserContent::Text(text) => texts.push(text),
            UserContent::Blocks(blocks) => {
                let mut text = String::new();
                for block in blocks {
                    match block {
                        UserContentBlock::Text(block) => {
                            if !text.is_empty() {
                                text.push('\n');
                            }
                            text.push_str(&block.text);
                        }
                        image @ UserContentBlock::Image(_) => images.push(image),
                    }
                }
                texts.push(text);
            }
        }
    }
    let marked = call.pieces.len().saturating_sub(1);
    let mut parts: Vec<UserContentBlock> = call
        .pieces
        .iter()
        .enumerate()
        .map(|(at, text)| {
            UserContentBlock::Text(TextContent {
                text: text.clone(),
                text_signature: None,
                cache_breakpoint: (at < marked).then_some(CacheBreakpoint::Ephemeral),
            })
        })
        .collect();
    texts.retain(|text| !text.is_empty());
    if !texts.is_empty() {
        parts.push(UserContentBlock::Text(TextContent::new(texts.join("\n\n"))));
    }
    parts.extend(images);
    let system = get_current_system_message(&systems);
    let mut out = Vec::with_capacity(2 + state_rows.len() + rest.len());
    out.extend(system.map(Message::System));
    out.push(Message::User(UserMessage {
        content: UserContent::Blocks(parts),
        timestamp: call.timestamp,
    }));
    out.extend(state_rows);
    out.extend(rest);
    out
}

fn now_millis() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |elapsed| {
            u64::try_from(elapsed.as_millis()).unwrap_or(u64::MAX)
        })
}
