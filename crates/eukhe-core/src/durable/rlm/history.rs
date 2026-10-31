//! The conversation as kernel data (Recursive Language Models: the context
//! lives in the REPL and the model reads it with code). Two read-only host
//! requests per memory kind, each answered for the calling cell's
//! conversation, each refused in the other kind with the reads that fit:
//!
//! - `history.entries` / `history.entry`: a session without chat memory
//!   reads its durable transcript, fork-aware and whole: what a compaction
//!   summarized away stays readable, and the compaction entries carry
//!   their summaries.
//! - `chat.view` / `chat.zoom`: a chat-memory session reads its memory as
//!   the `zoom` tool does (the view's lines, a line's two halves, a message
//!   whole). There is no search: the chat memory is read by zoom only.
//!
//! Every answer is a value for the cell; nothing enters the transcript.

use std::sync::{Arc, Weak};

use anyhow::{anyhow, bail};
use eukhe_durable::entries::{
    ASSISTANT_ENTRY, COMPACTION_ENTRY, RESET_ENTRY, SYSTEM_ENTRY, TOOL_RESULT_ENTRY, USER_ENTRY,
};
use eukhe_durable::harness::ConversationEntryQuery;
use eukhe_durable::types::{EntryData, EntryId, EntryRecord, ScanOrder};
use eukhe_types::pi_ai::{AssistantContentBlock, Message, UserContent, UserContentBlock};
use futures::future::BoxFuture;
use futures::FutureExt;
use serde_json::{json, Map, Value};

use super::super::entries::{
    BashEntryData, CustomEntryData, BASH_ENTRY, BRANCH_SUMMARY_ENTRY, COMPACTION_SUMMARY_ENTRY,
    CUSTOM_ENTRY, CUSTOM_STATE_ENTRY,
};
use super::super::{HostCall, HostCallHandler};
use super::{background, RlmRuntime};
use crate::memory::Memory;

/// The refusal of `chat.*` in a session without chat memory.
const NO_CHAT_MEMORY: &str = "this session has no chat memory: read its history with history.entries(), history.entry(id) and history.compactions()";
/// The refusal of `history.*` in a chat-memory session.
const CHAT_MEMORY_ONLY: &str = "this session's memory is the chat: read it with chat.view(), chat.zoom(id, n) and chat.message(id)";
/// The largest page of `history.entries`.
const MAX_PAGE: u64 = 512;

pub(super) fn register(runtime: &Arc<RlmRuntime>) {
    let requests = &runtime.deps.host_requests;
    requests.register(
        "history.entries",
        serve(runtime, |runtime, call| {
            async move { entries(&runtime, &call).await }.boxed()
        }),
    );
    requests.register(
        "history.entry",
        serve(runtime, |runtime, call| {
            async move { entry(&runtime, &call).await }.boxed()
        }),
    );
    requests.register(
        "chat.view",
        serve(runtime, |runtime, _call| {
            async move { view(chat_memory(&runtime)?).await }.boxed()
        }),
    );
    requests.register(
        "chat.zoom",
        serve(runtime, |runtime, call| {
            async move { zoom(chat_memory(&runtime)?, &call.data).await }.boxed()
        }),
    );
}

/// A handler served by `answer` while the session lives (held weakly: the
/// registry lives in the deps the runtime holds).
pub(super) fn serve<F>(runtime: &Arc<RlmRuntime>, answer: F) -> HostCallHandler
where
    F: Fn(Arc<RlmRuntime>, HostCall) -> BoxFuture<'static, anyhow::Result<Value>>
        + Send
        + Sync
        + 'static,
{
    let weak: Weak<RlmRuntime> = Arc::downgrade(runtime);
    let answer = Arc::new(answer);
    Arc::new(move |call: HostCall| {
        let weak = weak.clone();
        let answer = Arc::clone(&answer);
        async move {
            let runtime = weak
                .upgrade()
                .ok_or_else(|| anyhow!("the session ended before the request could be served"))?;
            answer(runtime, call).await
        }
        .boxed()
    })
}

fn chat_memory(runtime: &RlmRuntime) -> anyhow::Result<&Memory> {
    runtime
        .deps
        .memory
        .as_ref()
        .ok_or_else(|| anyhow!(NO_CHAT_MEMORY))
}

fn whole_number(data: &Value, name: &str, request: &str) -> anyhow::Result<Option<u64>> {
    match data.get(name) {
        None | Some(Value::Null) => Ok(None),
        Some(value) => value
            .as_u64()
            .map(Some)
            .ok_or_else(|| anyhow!("{request} {name} must be a non-negative integer")),
    }
}

/// The calling cell's conversation in the open Harness.
async fn conversation(
    runtime: &RlmRuntime,
    call: &HostCall,
) -> anyhow::Result<eukhe_durable::harness::Conversation> {
    if runtime.deps.memory.is_some() {
        bail!(CHAT_MEMORY_ONLY);
    }
    let cx = background();
    let (id, _) = runtime.target(call.call.as_ref(), &cx).await?;
    runtime
        .deps
        .harness
        .require()?
        .conversation(id, &cx)
        .await?
        .ok_or_else(|| anyhow!("conversation {id} does not exist"))
}

/// `history.entries {after?, limit, kind?}`: up to `limit` entries after
/// `after`, oldest first, those of `kind` only when given; `next` names the
/// last entry read when more may follow.
async fn entries(runtime: &RlmRuntime, call: &HostCall) -> anyhow::Result<Value> {
    const REQUEST: &str = "history.entries";
    let after = whole_number(&call.data, "after", REQUEST)?;
    let limit = whole_number(&call.data, "limit", REQUEST)?.unwrap_or(MAX_PAGE);
    if !(1..=MAX_PAGE).contains(&limit) {
        bail!("{REQUEST} limit must be an integer from 1 to {MAX_PAGE}");
    }
    let kind = match call.data.get("kind") {
        None | Some(Value::Null) => None,
        Some(Value::String(kind)) => Some(kind.as_str()),
        Some(_) => bail!("{REQUEST} kind must be a string"),
    };
    let conversation = conversation(runtime, call).await?;
    let page = conversation
        .entries(
            ConversationEntryQuery {
                min_entry_id: after.map(|after| EntryId::from_number(after + 1)),
                max_entry_id: None,
                order: Some(ScanOrder::Ascending),
            },
            usize::try_from(limit)?,
            None,
            &background(),
        )
        .await?;
    let next = match page.next {
        Some(_) => page.items.last().map(|entry| entry.id.get()),
        None => None,
    };
    let mut projected = Vec::new();
    for entry in &page.items {
        if kind.is_none_or(|kind| kind == kind_name(&entry.kind)) {
            projected.push(project(entry)?);
        }
    }
    Ok(json!({ "entries": projected, "next": next }))
}

/// `history.entry {id}`: one entry of the calling cell's conversation.
async fn entry(runtime: &RlmRuntime, call: &HostCall) -> anyhow::Result<Value> {
    const REQUEST: &str = "history.entry";
    let Some(id) = whole_number(&call.data, "id", REQUEST)? else {
        bail!("{REQUEST} id must be a non-negative integer");
    };
    let conversation = conversation(runtime, call).await?;
    let page = conversation
        .entries(
            ConversationEntryQuery {
                min_entry_id: Some(EntryId::from_number(id)),
                max_entry_id: Some(EntryId::from_number(id)),
                order: Some(ScanOrder::Ascending),
            },
            1,
            None,
            &background(),
        )
        .await?;
    let Some(found) = page.items.first() else {
        bail!("no entry {id} in this conversation's history");
    };
    Ok(json!({ "entry": project(found)? }))
}

/// The kind a durable entry kind reads as in the kernel.
fn kind_name(kind: &str) -> &str {
    [
        (USER_ENTRY.kind(), "user"),
        (ASSISTANT_ENTRY.kind(), "assistant"),
        (TOOL_RESULT_ENTRY.kind(), "tool_result"),
        (COMPACTION_ENTRY.kind(), "compaction"),
        (RESET_ENTRY.kind(), "reset"),
        (SYSTEM_ENTRY.kind(), "system"),
        (CUSTOM_ENTRY.kind(), "custom"),
        (BASH_ENTRY.kind(), "bash"),
        (BRANCH_SUMMARY_ENTRY.kind(), "branch_summary"),
        (COMPACTION_SUMMARY_ENTRY.kind(), "compaction_summary"),
        (CUSTOM_STATE_ENTRY.kind(), "custom_state"),
    ]
    .into_iter()
    .find_map(|(durable, name)| (durable == kind).then_some(name))
    .unwrap_or(kind)
}

fn user_text(content: &UserContent, out: &mut Vec<String>) {
    match content {
        UserContent::Text(text) => out.push(text.clone()),
        UserContent::Blocks(blocks) => blocks_text(blocks, out),
    }
}

fn blocks_text(blocks: &[UserContentBlock], out: &mut Vec<String>) {
    for block in blocks {
        match block {
            UserContentBlock::Text(text) => out.push(text.text.clone()),
            UserContentBlock::Image(image) => out.push(format!("[image: {}]", image.mime_type)),
        }
    }
}

/// One entry as the kernel's `HistoryEntry` reads it: its kind, what it
/// said, its tool calls or tool result, and where a compaction or reset
/// kept the context from.
fn project(entry: &EntryRecord) -> anyhow::Result<Value> {
    let mut texts = Vec::new();
    let mut tool_calls = Vec::new();
    let mut fields = Map::new();
    let mut timestamp = None;
    for message in entry.model.as_deref().unwrap_or_default() {
        timestamp.get_or_insert(message.timestamp());
        match message {
            Message::System(_) => {}
            Message::User(user) => user_text(&user.content, &mut texts),
            Message::Assistant(assistant) => {
                for block in &assistant.content {
                    match block {
                        AssistantContentBlock::Text(text) => texts.push(text.text.clone()),
                        AssistantContentBlock::Thinking(_) => {}
                        AssistantContentBlock::ToolCall(tool_call) => tool_calls.push(json!({
                            "id": tool_call.id,
                            "name": tool_call.name,
                            "arguments": tool_call.arguments,
                        })),
                    }
                }
            }
            Message::ToolResult(result) => {
                blocks_text(&result.content, &mut texts);
                fields.insert("tool_call_id".into(), json!(result.tool_call_id));
                fields.insert("tool_name".into(), json!(result.tool_name));
                fields.insert("is_error".into(), json!(result.is_error));
            }
        }
    }
    if entry.kind == CUSTOM_ENTRY.kind() {
        let data = CustomEntryData::decode(entry.data.as_ref())?;
        if texts.is_empty() {
            if let Some(content) = &data.content {
                user_text(content, &mut texts);
            }
        }
        fields.insert("custom_type".into(), json!(data.custom_type));
    }
    if entry.kind == BASH_ENTRY.kind() && texts.is_empty() {
        let data = BashEntryData::decode(entry.data.as_ref())?;
        texts.push(format!("$ {}\n{}", data.command, data.output));
    }
    if entry.kind == COMPACTION_ENTRY.kind() || entry.kind == RESET_ENTRY.kind() {
        fields.insert("first_kept_id".into(), json!(entry.head.map(EntryId::get)));
    }
    fields.insert("id".into(), json!(entry.id.get()));
    fields.insert("kind".into(), json!(kind_name(&entry.kind)));
    fields.insert("text".into(), json!(texts.join("\n")));
    fields.insert("tool_calls".into(), Value::Array(tool_calls));
    fields.insert("timestamp".into(), json!(timestamp));
    Ok(Value::Object(fields))
}

/// `id+n|text` as a kernel line.
fn line(text: &str) -> anyhow::Result<Value> {
    let parsed = text.split_once('|').and_then(|(name, text)| {
        let (id, count) = name.split_once('+')?;
        Some((id.parse::<u64>().ok()?, count.parse::<u64>().ok()?, text))
    });
    let Some((id, count, text)) = parsed else {
        bail!("the chat memory gave a line that is not id+n|text: {text:?}");
    };
    Ok(json!({ "id": id, "n": count, "text": text }))
}

fn lines(text: &str) -> anyhow::Result<Vec<Value>> {
    text.lines()
        .filter(|row| !row.is_empty())
        .map(line)
        .collect()
}

/// `chat.view`: the view the model sees, one line per part.
async fn view(memory: &Memory) -> anyhow::Result<Value> {
    let rendered = memory.render().await?;
    let body = rendered
        .text
        .strip_prefix("<chat>\n")
        .and_then(|rest| rest.strip_suffix("</chat>"))
        .ok_or_else(|| anyhow!("the chat memory gave a view outside <chat> tags"))?;
    Ok(json!({ "lines": lines(body)?, "messages": rendered.messages }))
}

/// `chat.zoom {id, n}`: message `id` whole for `n = 1`, else the two lines
/// line `id+n` was built from.
async fn zoom(memory: &Memory, data: &Value) -> anyhow::Result<Value> {
    const REQUEST: &str = "chat.zoom";
    let (Some(id), Some(count)) = (
        whole_number(data, "id", REQUEST)?,
        whole_number(data, "n", REQUEST)?,
    ) else {
        bail!("{REQUEST} needs an id and an n");
    };
    let zoomed = memory.zoom(id, count).await?;
    if zoomed.text == format!("No line {id}+{count}.") {
        bail!("no chat line {id}+{count}");
    }
    if count == 1 {
        let prefix = format!("{id}+0|");
        let text = zoomed.text.strip_prefix(&prefix).ok_or_else(|| {
            anyhow!("the chat memory gave message {id} without its {prefix} prefix")
        })?;
        return Ok(json!({ "text": text }));
    }
    Ok(json!({ "lines": lines(&zoomed.text)? }))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn view_lines_become_values() {
        assert_eq!(
            lines("0+4|user: m0 user: m1\n4+1|eukhe: hi | there\n").unwrap(),
            vec![
                json!({ "id": 0, "n": 4, "text": "user: m0 user: m1" }),
                json!({ "id": 4, "n": 1, "text": "eukhe: hi | there" }),
            ]
        );
        assert_eq!(
            line("x|y").unwrap_err().to_string(),
            "the chat memory gave a line that is not id+n|text: \"x|y\""
        );
    }
}
