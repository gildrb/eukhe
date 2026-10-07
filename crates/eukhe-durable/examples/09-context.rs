//! Transcript history and model context.
//! Run from the workspace:
//!   cargo run -p eukhe-durable --example 09-context
use std::io::Write;
use std::sync::Arc;

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::{ConversationCreateOptions, HarnessOptions};
use eukhe_durable::harness::{Conversation, ConversationEntryQuery, Harness};
use eukhe_durable::session::SessionResult;
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::types::{
    ContextEdit, ContextEditAction, ConversationOwnership, EntryDraft, EntryHead, EntryRecord,
};
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, IndexMap, JsonObject, Message, StopReason,
    SystemContent, SystemMessage, TextContent, ToolCall, ToolResultMessage, Usage, UserContent,
    UserContentBlock, UserMessage,
};
use futures::future::BoxFuture;

type BoxError = Box<dyn std::error::Error + Send + Sync>;

#[tokio::main]
async fn main() -> Result<(), BoxError> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let key = std::env::var("OPENAI_API_KEY").ok();
    run(&mut std::io::stdout(), &args, key.as_deref()).await
}

// Entries are immutable. `model` holds the messages an entry contributes to
// the next model request; `data` is for the app only. context() turns the
// stored transcript into those request messages:
//   - an entry with `head` starts a new context; older entries stay stored,
//   - `edits` replace or omit what an earlier entry contributes,
//   - aborted, error, and deferred assistant messages are not sent,
//   - tool results are sent right after their call, in call order,
//   - a call without a result gets a synthesized error result.

fn user_message(text: &str, timestamp: u64) -> Message {
    Message::User(UserMessage {
        content: UserContent::Text(text.to_owned()),
        timestamp,
    })
}

fn assistant_message(text: &str, calls: &[&str], stop_reason: Option<StopReason>) -> Message {
    let mut content = vec![AssistantContentBlock::Text(TextContent::new(text))];
    content.extend(calls.iter().map(|id| {
        AssistantContentBlock::ToolCall(ToolCall {
            id: (*id).to_owned(),
            name: "read".to_owned(),
            arguments: JsonObject::new(),
            thought_signature: None,
            namespace: None,
        })
    }));
    Message::Assistant(AssistantMessage {
        content,
        api: "example".to_owned(),
        provider: "example".to_owned(),
        model: "example".to_owned(),
        response_model: None,
        response_id: None,
        provider_thinking_level: None,
        thinking_level: None,
        diagnostics: None,
        usage: Usage::default(),
        stop_reason: stop_reason.unwrap_or(if calls.is_empty() {
            StopReason::Stop
        } else {
            StopReason::ToolUse
        }),
        deferred: None,
        error_message: None,
        raw_stop_reason: None,
        end_turn: None,
        timestamp: 2,
    })
}

fn tool_result_message(id: &str) -> Message {
    Message::ToolResult(ToolResultMessage {
        tool_call_id: id.to_owned(),
        tool_name: "read".to_owned(),
        content: vec![UserContentBlock::Text(TextContent::new(format!(
            "file {id}"
        )))],
        details: None,
        usage: None,
        nested_calls: None,
        is_error: false,
        timestamp: 3,
    })
}

fn show(message: &Message) -> Result<String, BoxError> {
    Ok(match message {
        Message::User(message) => match &message.content {
            UserContent::Text(text) => format!("user: {text}"),
            // TS `message.content as string` of an array: its `String()`.
            UserContent::Blocks(_) => "user: [object Object]".to_owned(),
        },
        Message::System(message) => match &message.sections {
            Some(sections) => format!("system: {}", serde_json::to_string(sections)?),
            None => "system: undefined".to_owned(),
        },
        Message::Assistant(message) => {
            let parts: Vec<String> = message
                .content
                .iter()
                .map(|part| match part {
                    AssistantContentBlock::Text(text) => text.text.clone(),
                    AssistantContentBlock::ToolCall(call) => format!("call({})", call.id),
                    AssistantContentBlock::Thinking(_) => String::new(),
                })
                .collect();
            format!("assistant: {}", parts.join(" "))
        }
        Message::ToolResult(message) => format!(
            "result({}){}",
            message.tool_call_id,
            if message.is_error { " error" } else { "" }
        ),
    })
}

fn show_all(messages: &[Message]) -> Result<String, BoxError> {
    let shown = messages.iter().map(show).collect::<Result<Vec<_>, _>>()?;
    Ok(serde_json::to_string(&shown)?)
}

fn kinds(entries: &[EntryRecord]) -> Result<String, BoxError> {
    let kinds: Vec<&str> = entries.iter().map(|entry| entry.kind.as_str()).collect();
    Ok(serde_json::to_string(&kinds)?)
}

/// TS `say(kind, ...model)`: append one entry with these messages.
fn say(
    transcript: &Conversation,
    kind: &str,
    model: Vec<Message>,
    context: &Context,
) -> BoxFuture<'static, SessionResult<EntryRecord>> {
    let id = transcript.id();
    let draft = EntryDraft {
        model: Some(model),
        ..EntryDraft::new(kind)
    };
    transcript.commit(
        move |tx| async move { tx.append_entry(id, draft).await },
        context,
    )
}

/// Runs the example, writing what the TS example prints to `out`.
///
/// # Errors
///
/// The first step that fails.
#[expect(
    clippy::too_many_lines,
    reason = "the TS example's steps, in order, in one function"
)]
pub async fn run(
    out: &mut (dyn Write + Send),
    _args: &[String],
    _openai_api_key: Option<&str>,
) -> Result<(), BoxError> {
    let context = &*BACKGROUND_CONTEXT;
    let harness = Harness::open(
        Arc::new(MemoryStorage::new()),
        HarnessOptions::new(
            create_models(CreateModelsOptions::default()),
            Arc::new(create_registry()),
        ),
        context,
    )
    .await?;

    let transcript = harness
        .create_conversation(
            ConversationCreateOptions::new(ConversationOwnership::Ownerless),
            context,
        )
        .await?;
    let id = transcript.id();

    let question = say(
        &transcript,
        "message",
        vec![user_message("read a and b", 1)],
        context,
    )
    .await?;
    // Stored, never sent.
    say(
        &transcript,
        "message",
        vec![assistant_message(
            "I crashed",
            &[],
            Some(StopReason::Aborted),
        )],
        context,
    )
    .await?;
    let calls = say(
        &transcript,
        "message",
        vec![assistant_message("reading", &["a", "b"], None)],
        context,
    )
    .await?;
    // Results finish out of order.
    say(
        &transcript,
        "message",
        vec![tool_result_message("b")],
        context,
    )
    .await?;
    let mut sections = IndexMap::new();
    sections.insert("cwd".to_owned(), Some("<cwd>/repo</cwd>".to_owned()));
    say(
        &transcript,
        "pi.system",
        vec![Message::System(SystemMessage {
            content: SystemContent::from(""),
            sections: Some(sections),
            tools_added: None,
            tools_removed: None,
            timestamp: 4,
        })],
        context,
    )
    .await?;
    say(
        &transcript,
        "message",
        vec![tool_result_message("a")],
        context,
    )
    .await?;
    say(
        &transcript,
        "message",
        vec![assistant_message("a and b look fine", &[], None)],
        context,
    )
    .await?;
    let target = question.id;
    transcript
        .commit(
            move |tx| async move {
                tx.append_entry(
                    id,
                    EntryDraft {
                        data: Some("user fixed a typo".into()),
                        edits: Some(vec![ContextEdit {
                            target,
                            action: ContextEditAction::Replace {
                                messages: vec![user_message("read files a and b", 1)],
                            },
                        }]),
                        ..EntryDraft::new("edit")
                    },
                )
                .await
            },
            context,
        )
        .await?;
    transcript
        .commit(
            move |tx| async move {
                tx.append_entry(
                    id,
                    EntryDraft {
                        data: Some("display only".into()),
                        ..EntryDraft::new("note")
                    },
                )
                .await
            },
            context,
        )
        .await?;

    let view = transcript.context(context).await?;
    writeln!(out, "raw active entries: {}", kinds(&view.entries)?)?;
    writeln!(out, "request messages: {}", show_all(&view.messages)?)?;

    // A fork at the tool call has no results yet; context() fills them in.
    let cut = transcript
        .fork(
            calls.id,
            ConversationCreateOptions::new(ConversationOwnership::Ownerless),
            context,
        )
        .await?;
    writeln!(
        out,
        "fork messages: {}",
        show_all(&cut.context(context).await?.messages)?
    )?;

    // A headed summary replaces everything before the entry it points at.
    // `EntryHead::SelfEntry` ("self") points the head at the summary entry
    // itself.
    transcript
        .commit(
            move |tx| async move {
                tx.append_entry(
                    id,
                    EntryDraft {
                        head: Some(EntryHead::SelfEntry),
                        model: Some(vec![user_message("Summary: a and b are fine.", 5)]),
                        ..EntryDraft::new("summary")
                    },
                )
                .await
            },
            context,
        )
        .await?;
    let view = transcript.context(context).await?;
    writeln!(
        out,
        "after summary: {} {}",
        view.head
            .as_ref()
            .map_or("undefined", |head| head.kind.as_str()),
        show_all(&view.messages)?
    )?;

    // entries() pages the stored transcript, newest first, including
    // inherited parent entries. Nothing is ever deleted by heads or edits.
    let history = transcript
        .entries(ConversationEntryQuery::default(), 3, None, context)
        .await?;
    writeln!(
        out,
        "newest stored entries: {} more: {}",
        kinds(&history.items)?,
        history.next.is_some()
    )?;

    harness.close(context).await?;
    Ok(())
}
