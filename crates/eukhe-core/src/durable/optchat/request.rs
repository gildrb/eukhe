//! The request of a call (§3.3, §6). Each session is its own thread: a
//! root conversation's request is its own transcript, verbatim (the
//! assistant's text, tool calls, tool results, images), compacted by the
//! session's compaction only when its context fills. On a run's first
//! request the call takes the chat's root-turn lease, waits until
//! everything before the run is in the session's chat log, renders the
//! settled view, keeps only its lines of the history that scrolled out of
//! the transcript, and pins them in `eukhe.optchat.call`; every request of
//! the run then sends the pinned lines ahead of the transcript, so the
//! prompt-cache prefix holds across tool rounds and across a crash. A
//! newly pinned root call also hands its system prompt and tools to the
//! compactor, which reuses them (§4). A subagent pins one view for its
//! whole conversation and logs nothing.

use std::sync::Arc;

use eukhe_ai::utils::text::get_system_message_text;
use eukhe_ai::utils::transcript::{get_current_system_message, get_current_tools};
use eukhe_chord::context::Context;
use eukhe_durable::harness::types::{HookApi, HookResult, RequestMessages};
use eukhe_durable::harness::{Harness, LiveRun, LiveState, LIVE_DOC};
use eukhe_durable::session::SessionResult;
use eukhe_durable::types::{ConversationId, EntryId, EntryRecord};
use eukhe_types::pi_ai::{
    CacheBreakpoint, Message, TextContent, UserContent, UserContentBlock, UserMessage,
};

use super::docs::{decode, write, CallState, CALL_DOC};
use super::lines::{entry_lines, lead_of, Lead};
use super::tools::memory_error;
use super::OptChat;
use crate::memory::{CompactionPrompt, MemoryRole};

/// The `before_request` transform of one request.
pub(super) async fn transform(
    chat: Arc<OptChat>,
    request: RequestMessages,
    api: HookApi,
    cx: Context,
) -> HookResult<RequestMessages> {
    let harness = chat.harness.require()?;
    let conversation = api.conversation_id();
    let root = match chat.role {
        MemoryRole::Root => {
            if !is_root_conversation(&harness, conversation, &cx).await? {
                return Ok(None);
            }
            let Some(run) = live_run(&harness, conversation, &cx).await? else {
                return Ok(None);
            };
            Some(run)
        }
        MemoryRole::Subagent => None,
    };
    let Some(handle) = harness.conversation(conversation, &cx).await? else {
        return Ok(None);
    };
    let view = handle
        .context(
            &cx,
            eukhe_durable::harness::types::ContextOptions::default(),
        )
        .await?;
    let Some(run) = root else {
        let call = match call_state(&harness, conversation, &cx).await? {
            Some(call) => call,
            None => pin(&chat, &harness, conversation, None, None, &cx).await?,
        };
        let mut state_rows: Vec<Message> = Vec::new();
        for (entry, contributed) in view.entries.iter().zip(&view.contributions) {
            if lead_of(entry) == Lead::State {
                state_rows.extend(contributed.iter().cloned());
            }
        }
        let messages = request_messages(&call, request.messages, 0, |message| {
            state_rows.contains(message)
        });
        return Ok(Some(RequestMessages {
            messages,
            force_tool: request.force_tool,
        }));
    };
    let key = run_key(&run);
    let (call, pinned) = match call_state(&harness, conversation, &cx).await? {
        Some(call) if call.run_key.as_deref() == Some(key.as_str()) => (call, false),
        Some(_) | None => {
            // Everything before the run is in the log before the view
            // renders; the view keeps only what the transcript no longer
            // holds verbatim.
            chat.flush().await?;
            let start = run_start(&harness, &run, &cx).await?;
            let verbatim = verbatim_lines(&view.entries, start)?;
            let call = pin(
                &chat,
                &harness,
                conversation,
                Some(key),
                Some(verbatim),
                &cx,
            )
            .await?;
            chat.wake();
            (call, true)
        }
    };
    let messages = root_request(&call, request.messages);
    if pinned {
        chat.memory
            .set_compaction_prompt(compaction_prompt(&messages))
            .await
            .map_err(|error| memory_error(&error))?;
    }
    Ok(Some(RequestMessages {
        messages,
        force_tool: request.force_tool,
    }))
}

/// The chat log lines the transcript still holds verbatim before the run:
/// those of its context entries before the run's start (all of them for a
/// run without input). The view keeps only the lines before these.
fn verbatim_lines(entries: &[EntryRecord], start: Option<EntryId>) -> SessionResult<u64> {
    let mut lines = 0u64;
    for entry in entries {
        if start.is_some_and(|start| entry.id >= start) {
            break;
        }
        lines += entry_lines(entry)?.len() as u64;
    }
    Ok(lines)
}

/// The system prompt and tools a request sends, as compactions reuse them.
fn compaction_prompt(messages: &[Message]) -> CompactionPrompt {
    CompactionPrompt {
        system: get_current_system_message(messages)
            .map(|system| get_system_message_text(&system))
            .unwrap_or_default(),
        tools: get_current_tools(messages),
    }
}

/// Whether `conversation` is a root conversation of the session (no task
/// owns it): only those start from the view and are logged.
pub(crate) async fn is_root_conversation(
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
/// A root call (`verbatim` set) keeps only the lines of the history that
/// scrolled out of its transcript: the lines before the last `verbatim`
/// messages of the log.
async fn pin(
    chat: &OptChat,
    harness: &Harness,
    conversation: ConversationId,
    run_key: Option<String>,
    verbatim: Option<u64>,
    cx: &Context,
) -> SessionResult<CallState> {
    let within = chat.settings.manager().get_memory_settle_timeout();
    let mut rendered = chat
        .memory
        .settled_render(within)
        .await
        .map_err(|error| memory_error(&error))?;
    if let Some(verbatim) = verbatim {
        rendered = rendered.history(verbatim);
    }
    let pieces = if rendered.text.is_empty() {
        Vec::new()
    } else {
        rendered.pieces()
    };
    let call = CallState {
        run_key,
        pieces,
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

/// A root call's request: the session's own transcript as the harness
/// built it (every turn verbatim, its images too, after the session's
/// compaction when one ran), with the pinned view of the older history
/// leading its first user message, marked at its end. Without such
/// history the transcript goes unchanged.
pub(crate) fn root_request(call: &CallState, mut messages: Vec<Message>) -> Vec<Message> {
    if call.pieces.is_empty() {
        return messages;
    }
    let last = call.pieces.len() - 1;
    let mut view: Vec<UserContentBlock> = call
        .pieces
        .iter()
        .enumerate()
        .map(|(at, text)| {
            UserContentBlock::Text(TextContent {
                text: text.clone(),
                text_signature: None,
                cache_breakpoint: (at == last).then_some(CacheBreakpoint::Ephemeral),
            })
        })
        .collect();
    let first_user = messages
        .iter()
        .position(|message| matches!(message, Message::User(_)));
    if let Some(Message::User(user)) = first_user.map(|at| &mut messages[at]) {
        let content = std::mem::replace(&mut user.content, UserContent::Text(String::new()));
        match content {
            UserContent::Text(text) => {
                view.push(UserContentBlock::Text(TextContent::new(text)));
            }
            UserContent::Blocks(blocks) => view.extend(blocks),
        }
        user.content = UserContent::Blocks(view);
    } else {
        let at = messages
            .iter()
            .take_while(|message| matches!(message, Message::System(_)))
            .count();
        messages.insert(
            at,
            Message::User(UserMessage {
                content: UserContent::Blocks(view),
                timestamp: call.timestamp,
            }),
        );
    }
    messages
}

/// A subagent's request (§6): the system messages before its leading user
/// rows replayed into ONE system message; then ONE user message holding the
/// view pieces (the first marked at the view's last whole block) and ONE
/// text block with its leading user texts (its task, reports) joined by a
/// blank line, their images after it, its last text block marked as the
/// request's end; then any harness state among those leading rows; then
/// the rest of the conversation. Messages before `start` are dropped.
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
    let joined = texts.join("\n\n");
    let text = joined;
    if !text.is_empty() {
        parts.push(UserContentBlock::Text(TextContent::new(text)));
    }
    parts.extend(images);
    if let Some(UserContentBlock::Text(end)) = parts
        .iter_mut()
        .rev()
        .find(|part| matches!(part, UserContentBlock::Text(_)))
    {
        end.cache_breakpoint = Some(CacheBreakpoint::Ephemeral);
    }
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
