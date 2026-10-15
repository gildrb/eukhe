//! The `zoom` and `date` tools (§5, §6) over the chat memory: `zoom(id, n)`
//! opens a line, `zoom(id, 1)` gives a message whole with its images, and
//! `zoom("Name")` gives an agent's whole chat (its own log, out of the
//! chat).

use std::sync::Arc;

use eukhe_ai::typebox::{Options, Type};
use eukhe_chord::context::Context;
use eukhe_durable::harness::define::define_tool;
use eukhe_durable::harness::types::{ToolExecutionResult, ToolRegistration};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::{ConversationId, DocumentReader};
use eukhe_types::pi_ai::{TextContent, UserContentBlock};

use super::lines::chat_text;
use crate::durable::children::find_child;
use crate::durable::tool_contract;
use crate::durable::{read_main_transcript, SessionLocation};
use crate::memory::{Memory, Zoomed, DATE_TOOL_DESCRIPTION, ZOOM_TOOL_DESCRIPTION};

/// The durable identities of the tools' contracts. `zoom@2` takes an
/// agent's name as `id` and returns a message's images.
const ZOOM_VERSION: &str = "zoom@2";
const DATE_VERSION: &str = "date@1";

/// The prefix a subagent's name carries in its `[Name]` reports.
const CHILD_PREFIX: &str = "child:";

/// What a `zoom` call names.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Target {
    /// The line `id+n`, or message `id` whole when `n = 1`.
    Line { id: u64, count: u64 },
    /// An agent's whole chat, by name.
    Agent(String),
}

impl Target {
    fn parse(params: &serde_json::Value) -> SessionResult<Target> {
        match params.get("id") {
            Some(serde_json::Value::String(name)) => Ok(Target::Agent(name.clone())),
            Some(_) | None => Ok(Target::Line {
                id: integer_argument(params, "id")?,
                count: integer_argument(params, "n")?,
            }),
        }
    }
}

/// `zoom(id, n)`, `zoom("Name")` and `date(id)`.
pub(crate) fn memory_tools(memory: &Memory) -> Vec<Arc<ToolRegistration>> {
    let zoom_memory = memory.clone();
    let zoom = ToolRegistration::new(
        "zoom",
        ZOOM_TOOL_DESCRIPTION,
        tool_contract::parameters([
            (
                "id",
                Type::union([
                    Type::integer_with(Options::new().set("minimum", 0)),
                    Type::string(),
                ]),
            ),
            (
                "n",
                Type::optional(Type::integer_with(Options::new().set("minimum", 1))),
            ),
        ]),
        move |params, api, cx| {
            let memory = zoom_memory.clone();
            async move {
                let zoomed = match Target::parse(&params)? {
                    Target::Line { id, count } => memory
                        .zoom(id, count)
                        .await
                        .map_err(|error| memory_error(&error))?,
                    Target::Agent(name) => Zoomed {
                        text: agent_chat(&*api, api.conversation_id(), &name, &cx).await?,
                        images: Vec::new(),
                    },
                };
                Ok(zoom_result(zoomed))
            }
        },
    );
    let date_memory = memory.clone();
    let date = ToolRegistration::new(
        "date",
        DATE_TOOL_DESCRIPTION,
        tool_contract::parameters([("id", Type::integer_with(Options::new().set("minimum", 0)))]),
        move |params, _api, _cx| {
            let memory = date_memory.clone();
            async move {
                let id = integer_argument(&params, "id")?;
                let text = memory
                    .date(id)
                    .await
                    .map_err(|error| memory_error(&error))?;
                Ok(ToolExecutionResult {
                    output: Some(vec![UserContentBlock::Text(TextContent::new(text))]),
                    details: Some(serde_json::json!({ "version": DATE_VERSION }).into()),
                    ..ToolExecutionResult::default()
                })
            }
        },
    );
    vec![define_tool(zoom), define_tool(date)]
}

/// `zoom("Name")`: the whole chat of the subagent `name` (with or without
/// the `child:` of its `[Name]` reports) that `conversation` spawned, as
/// `kind: text` lines; its own steps stay in its own log (§6).
///
/// # Errors
///
/// The name is ambiguous, or the registry or the agent's log cannot be
/// read.
#[tracing::instrument(name = "optchat.agent_chat", skip(reader, cx))]
pub(super) async fn agent_chat(
    reader: &(impl DocumentReader + ?Sized),
    conversation: ConversationId,
    name: &str,
    cx: &Context,
) -> SessionResult<String> {
    let selector = name.strip_prefix(CHILD_PREFIX).unwrap_or(name);
    let child = find_child(reader, conversation, selector, cx)
        .await
        .map_err(|error| memory_error(&error))?;
    let Some(child) = child else {
        return Ok(format!("No agent {name}."));
    };
    if child.entry.session_dir.is_empty() {
        return Ok(format!("Agent {name} has no chat yet."));
    }
    let location = SessionLocation::Durable(child.entry.session_dir.into());
    let transcript = read_main_transcript(&location, cx)
        .await
        .map_err(SessionError::other)?;
    chat_text(&transcript.entries)
}

fn integer_argument(params: &serde_json::Value, name: &str) -> SessionResult<u64> {
    params
        .get(name)
        .and_then(serde_json::Value::as_u64)
        .ok_or_else(|| SessionError::error(format!("`{name}` must be a non-negative integer")))
}

/// The zoomed text, then the images of a message zoomed whole.
fn zoom_result(zoomed: Zoomed) -> ToolExecutionResult {
    let mut output = vec![UserContentBlock::Text(TextContent::new(zoomed.text))];
    output.extend(zoomed.images.into_iter().map(UserContentBlock::Image));
    ToolExecutionResult {
        output: Some(output),
        details: Some(serde_json::json!({ "version": ZOOM_VERSION }).into()),
        ..ToolExecutionResult::default()
    }
}

/// A chat memory failure as the harness reports it.
pub(crate) fn memory_error(error: &anyhow::Error) -> SessionError {
    SessionError::error(format!("{error:#}"))
}
