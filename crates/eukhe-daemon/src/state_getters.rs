//! The read-only state getters: the worker arms for the daemon `get_*`
//! commands (TS daemon-mode `case "get_connection_state"` ... `case
//! "get_tool_definition"`). Each handler answers the exact TS wire shape;
//! the data comes from the shown conversation's event mirror on the core,
//! the hosted session (its main conversation's agent and context, its
//! loaded resources, chat memory, and model collection), and the
//! context-tree cache.

use std::sync::Arc;

use eukhe_ai::auth::AuthOperationOptions;
use eukhe_ai::utils::transcript::get_current_system_message;
use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_core::models::ModelRegistry;
use eukhe_durable::harness::compaction::estimate_context;
use eukhe_durable::harness::types::{ContextOptions, ContextView, PromptInput};
use eukhe_durable::harness::{derive_view, Conversation};
use eukhe_durable::types::EntryRecord;
use eukhe_types::daemon::{
    MemoryReply, MemorySnapshot, MemoryStatusSnapshot, MemoryTree, MemoryTreeReply, MemoryZoom,
};
use eukhe_types::pi_ai::IndexMap;
use serde_json::{json, Value};

use crate::context_tree_cache::WalkRequest;
use crate::protocol::{response_failure, response_success, DaemonResponse};
use crate::worker::durable_host::wire_messages::{
    assistant_context_tokens, entry_wire_message_with, transcript_messages, transcript_messages_of,
};
use crate::worker::{model_metadata, HostedSession, Worker};

impl Worker {
    /// `get_connection_state`: the connection state block (the same shape
    /// the attach snapshot carries) with the TS `createConnectionState`
    /// `heartbeat` overlay (this worker owns no cron store, so the
    /// overlay is the TS null).
    pub(crate) fn handle_get_connection_state(&self) -> DaemonResponse {
        if let Err(response) = self.require_created("get_connection_state") {
            return response;
        }
        let state = {
            let core = self
                .core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            self.connection_state_locked(&core)
        };
        let mut value = serde_json::to_value(&state).unwrap_or(Value::Null);
        value["heartbeat"] = Value::Null;
        response_success(None, "get_connection_state", Some(value))
    }

    /// `get_context_tree` (TS `session.getContextTree`): the root node is
    /// the session itself — label, model, context usage, and the main
    /// conversation's own spend (`pi.usage`, with the per-model breakdown)
    /// plus its children's totals — and the children are the live RLM
    /// roster plus every persisted child session under the session's
    /// artifact tree. The disk walk is the background refresh of the
    /// context-tree cache (`context_tree_cache`), never this request path:
    /// the response serves the cached walk with the fresh live identity
    /// overlaid.
    pub(crate) async fn handle_get_context_tree(&self) -> DaemonResponse {
        const COMMAND: &str = "get_context_tree";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let (label, ledger, model, session_id, parent_id) = {
            let core = self
                .core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            (
                core.session_name
                    .clone()
                    .unwrap_or_else(|| "main agent".to_string()),
                core.view
                    .as_ref()
                    .map(|view| view.translator.mirror().usage.clone())
                    .unwrap_or_default(),
                model_metadata(&core, &self.session),
                (!core.session_id.is_empty()).then(|| core.session_id.clone()),
                core.rlm_child_id.clone(),
            )
        };
        let context_window = model_context_window(model.as_ref());
        let main = match hosted.main() {
            Ok(main) => main,
            Err(error) => return response_failure(None, COMMAND, &error.to_string(), None),
        };
        let context_usage = match context_window {
            Some(window) => match main
                .context(&BACKGROUND_CONTEXT, ContextOptions::default())
                .await
            {
                Ok(view) => Some(context_usage(&view, window)),
                Err(error) => return response_failure(None, COMMAND, &error.to_string(), None),
            },
            None => None,
        };
        let snapshots =
            match crate::rlm_surface::rlm_child_snapshots(&hosted, parent_id.as_deref()).await {
                Ok(snapshots) => snapshots,
                Err(error) => {
                    return response_failure(None, COMMAND, &format!("{error:#}"), None);
                }
            };
        // The children come from the cache instantly (fresh live-roster
        // identity and status over the cached bodies).
        let children = self
            .context_tree
            .serve_children(session_id.as_deref(), &snapshots);
        // Re-arm the background refresh for the next read.
        self.poke_context_tree_refresh();
        let (own_usage, own_usage_by_model) = ledger_usage(&ledger);
        // The total is the session's own spend plus each child's total
        // (the children's spend lives in their own sessions).
        let mut total_usage = own_usage.clone();
        for child_total in children.iter().filter_map(|child| child.get("totalUsage")) {
            usage::add_usage(&mut total_usage, child_total);
        }
        let mut tree = json!({
            "id": "root",
            "label": label,
            "status": "active",
            "ownUsage": own_usage,
            "totalUsage": total_usage,
            "children": children,
        });
        if let Some(model) = model.as_ref().and_then(|model| {
            Some(json!({ "provider": model.get("provider")?, "id": model.get("id")? }))
        }) {
            tree["model"] = model;
        }
        if let Some(usage) = context_usage {
            tree["contextUsage"] = usage;
        }
        if let Some(by_model) = own_usage_by_model {
            tree["ownUsageByModel"] = json!(by_model);
        }
        response_success(None, COMMAND, Some(tree))
    }

    /// Arm the background context-tree walk (`context_tree_cache`) for
    /// this session: the durable session id (the artifact tree), the
    /// storage path (the ledger's tombstone record), and the hosted
    /// session whose live roster overlays the walk, so a replaced session
    /// never walks the previous tree. Called by `get_context_tree` (re-arm
    /// on every read older than the TTL) and as the warm at session open
    /// (create/attach).
    pub(crate) fn poke_context_tree_refresh(&self) {
        let request = self.session.get().and_then(|hosted| {
            let core = self
                .core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            (!core.session_id.is_empty()).then(|| WalkRequest {
                session_id: core.session_id.clone(),
                session_file: core.session_file().map(std::path::PathBuf::from),
                hosted,
                parent_id: core.rlm_child_id.clone(),
            })
        });
        self.context_tree
            .poke_refresh(self.config.agent_dir.clone(), request);
    }

    /// `get_commands` (TS `createAgentConnectionCommands`): prompt
    /// templates, then skills, from the session's loaded resources.
    pub(crate) fn handle_get_commands(&self) -> DaemonResponse {
        let hosted = match self.hosted("get_commands") {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let commands = resources::connection_commands(&hosted.deps().resources);
        response_success(None, "get_commands", Some(json!({ "commands": commands })))
    }

    /// `get_resource_snapshot` (TS
    /// `createAgentConnectionResourceSnapshot`) over the session's loaded
    /// resources.
    pub(crate) fn handle_get_resource_snapshot(&self) -> DaemonResponse {
        let hosted = match self.hosted("get_resource_snapshot") {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let deps = hosted.deps();
        let snapshot =
            resources::resource_snapshot(&deps.resources, hosted.session_id(), &deps.cwd);
        response_success(None, "get_resource_snapshot", Some(snapshot))
    }

    /// `get_session_context` (TS `session.buildSessionContext`): the main
    /// conversation's active context — its messages (wire `AgentMessage`
    /// rows from the context head on), the effective thinking level, the
    /// service-tier preference, and the model selector.
    pub(crate) async fn handle_get_session_context(&self) -> DaemonResponse {
        const COMMAND: &str = "get_session_context";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let cx = &BACKGROUND_CONTEXT;
        let read = async {
            let main = hosted.main().map_err(|error| error.to_string())?;
            let messages = context_messages(&main, cx).await?;
            let agent = main.agent(cx).await.map_err(|error| error.to_string())?;
            Ok::<_, String>((messages, agent))
        };
        let (messages, agent) = match read.await {
            Ok(read) => read,
            Err(error) => return response_failure(None, COMMAND, &error, None),
        };
        let service_tier = self
            .core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .service_tier;
        response_success(
            None,
            COMMAND,
            Some(json!({
                "context": {
                    "messages": messages,
                    "thinkingLevel": agent.thinking_level.as_str(),
                    "serviceTier": service_tier,
                    "model": agent.model.map(|model| json!({
                        "provider": model.provider,
                        "modelId": model.model_id,
                    })),
                }
            })),
        )
    }

    /// `get_system_prompt` (TS `{ systemPrompt }`): the main conversation's
    /// system prompt as its next request renders it.
    pub(crate) async fn handle_get_system_prompt(&self) -> DaemonResponse {
        const COMMAND: &str = "get_system_prompt";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        match render_system_prompt(&hosted, &BACKGROUND_CONTEXT).await {
            Ok(prompt) => response_success(None, COMMAND, Some(json!({ "systemPrompt": prompt }))),
            Err(error) => response_failure(None, COMMAND, &error, None),
        }
    }

    /// `get_chat_view` (Rust-native, advertised by the `chat_view`
    /// capability): the chat memory's current view for the interactive
    /// client's startup block, `{ "view": null }` when the session keeps
    /// no chat memory (a subagent, or a scripted session).
    pub(crate) async fn handle_get_chat_view(&self) -> DaemonResponse {
        const COMMAND: &str = "get_chat_view";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let view = match hosted.deps().memory.as_ref() {
            Some(memory) => match memory.render().await {
                Ok(view) => Some(eukhe_types::daemon::ChatViewSnapshot {
                    // Every line but the `<chat>`/`</chat>` frame is one part.
                    lines: u64::try_from(view.text.lines().count().saturating_sub(2))
                        .unwrap_or(u64::MAX),
                    bytes: u64::try_from(view.text.len()).unwrap_or(u64::MAX),
                    messages: view.messages,
                    text: view.text,
                }),
                Err(error) => return response_failure(None, COMMAND, &format!("{error:#}"), None),
            },
            None => None,
        };
        match serde_json::to_value(eukhe_types::daemon::ChatViewReply { view }) {
            Ok(data) => response_success(None, COMMAND, Some(data)),
            Err(error) => response_failure(None, COMMAND, &error.to_string(), None),
        }
    }

    /// `get_memory { zoom? }` (Rust-native, advertised by the `memory`
    /// capability): the chat memory's status with its view (one `id+n|text`
    /// line per node, without the `<chat>` frame) or, with a zoom, the zoom
    /// tool's answer, for `/memory` and the status gauge; `{ "memory": null }`
    /// when the session keeps no chat memory (a subagent, or a scripted
    /// session).
    pub(crate) async fn handle_get_memory(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "get_memory";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let zoom = match payload.get("zoom") {
            None | Some(Value::Null) => None,
            Some(zoom) => match serde_json::from_value::<MemoryZoom>(zoom.clone()) {
                Ok(zoom) => Some(zoom),
                Err(error) => {
                    return response_failure(None, COMMAND, &format!("invalid zoom: {error}"), None)
                }
            },
        };
        let memory = match hosted.deps().memory.as_ref() {
            Some(memory) => match memory_snapshot(memory, zoom, &self.config.agent_dir).await {
                Ok(snapshot) => Some(snapshot),
                Err(error) => return response_failure(None, COMMAND, &format!("{error:#}"), None),
            },
            None => None,
        };
        match serde_json::to_value(MemoryReply { memory }) {
            Ok(data) => response_success(None, COMMAND, Some(data)),
            Err(error) => response_failure(None, COMMAND, &error.to_string(), None),
        }
    }

    /// `get_memory_tree { node? }` (Rust-native, advertised by the
    /// `memory_tree` capability): one level of the chat memory's tree --
    /// the view's lines, or what line `node` opens into -- with the
    /// memory's status, for the `/memory` tree and the dashboard;
    /// `{ "tree": null }` when the session keeps no chat memory.
    pub(crate) async fn handle_get_memory_tree(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "get_memory_tree";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let node = match payload.get("node") {
            None | Some(Value::Null) => None,
            Some(node) => match serde_json::from_value::<MemoryZoom>(node.clone()) {
                Ok(node) => Some(node),
                Err(error) => {
                    return response_failure(None, COMMAND, &format!("invalid node: {error}"), None)
                }
            },
        };
        let tree = match hosted.deps().memory.as_ref() {
            Some(memory) => match memory_tree(memory, node, &self.config.agent_dir).await {
                Ok(tree) => Some(tree),
                Err(error) => return response_failure(None, COMMAND, &format!("{error:#}"), None),
            },
            None => None,
        };
        match serde_json::to_value(MemoryTreeReply { tree }) {
            Ok(data) => response_success(None, COMMAND, Some(data)),
            Err(error) => response_failure(None, COMMAND, &error.to_string(), None),
        }
    }

    /// `get_tool_definition { name }` (TS
    /// `createAgentConnectionToolDefinition`): the definition of one tool
    /// the main conversation's next request offers; an unknown name
    /// answers success with the key omitted, exactly like the TS
    /// `undefined` field.
    pub(crate) async fn handle_get_tool_definition(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "get_tool_definition";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let Some(name) = payload.get("name").and_then(Value::as_str) else {
            return response_failure(None, COMMAND, "get_tool_definition requires a name", None);
        };
        let agent = match hosted.main() {
            Ok(main) => main.agent(&BACKGROUND_CONTEXT).await,
            Err(error) => Err(error),
        };
        let agent = match agent {
            Ok(agent) => agent,
            Err(error) => return response_failure(None, COMMAND, &error.to_string(), None),
        };
        let mut data = serde_json::Map::new();
        if let Some(tool) = agent.tools.iter().find(|tool| tool.name == name) {
            data.insert(
                "toolDefinition".to_string(),
                json!({
                    "name": tool.name,
                    // Durable tool registrations carry no display label;
                    // the TS label defaults to the name.
                    "label": tool.name,
                    "description": tool.description,
                    "parameters": serde_json::to_value(&tool.parameters).unwrap_or(Value::Null),
                }),
            );
        }
        response_success(None, COMMAND, Some(Value::Object(data)))
    }

    /// `get_available_models` (TS `refreshAvailableModels`): the session's
    /// models whose providers have credentials.
    pub(crate) async fn handle_get_available_models(&self) -> DaemonResponse {
        const COMMAND: &str = "get_available_models";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        match hosted
            .deps()
            .models
            .get_available(None, AuthOperationOptions::default())
            .await
        {
            Ok(models) => response_success(None, COMMAND, Some(json!({ "models": models }))),
            Err(error) => response_failure(None, COMMAND, &error.to_string(), None),
        }
    }
}

/// The active context of `conversation` as wire `AgentMessage` rows (TS
/// `session.state.messages`).
async fn context_messages(conversation: &Conversation, cx: &Context) -> Result<Vec<Value>, String> {
    let view = conversation
        .context(cx, ContextOptions::default())
        .await
        .map_err(|error| error.to_string())?;
    Ok(transcript_messages(&view.entries))
}

/// The positive `contextWindow` of a wire model (`model_metadata`), or
/// None when the model or its window is unknown.
pub(crate) fn model_context_window(model: Option<&Value>) -> Option<u64> {
    model
        .and_then(|model| model.get("contextWindow"))
        .and_then(Value::as_u64)
        .filter(|window| *window > 0)
}

/// The tray's context usage off the shown conversation's event mirror (the
/// attach snapshot's `state.contextUsage` and `get_session_stats`): the
/// [`context_usage`] of the view the mirror's entries derive
/// ([`derive_view`]), the one `get_context_tree` reads through the
/// Harness, so the attach can fill it under the core lock it already holds.
pub(crate) fn mirror_context_usage(entries: &[EntryRecord], context_window: u64) -> Value {
    context_usage(&derive_view(entries), context_window)
}

/// The active context off the event mirror as wire `AgentMessage` rows (TS
/// `session.state.messages`): the newest head marker (the compaction
/// summary), then the visible non-head entries from its head on -- the
/// entries the Harness derives -- without a Harness read. The summary's
/// `tokensBefore` is the context the last answer before it measured.
pub(crate) fn mirror_context_messages(entries: &[EntryRecord]) -> Vec<Value> {
    let Some(position) = entries.iter().rposition(|entry| entry.head.is_some()) else {
        return transcript_messages_of(entries);
    };
    let marker = &entries[position];
    let tokens_before = entries[..position]
        .iter()
        .rev()
        .find_map(assistant_context_tokens)
        .unwrap_or(0);
    let start = marker.head;
    let kept = entries
        .iter()
        .filter(|entry| entry.head.is_none() && start.is_none_or(|start| entry.id >= start));
    entry_wire_message_with(marker, tokens_before)
        .into_iter()
        .chain(transcript_messages_of(kept))
        .collect()
}

/// The context usage the clients show (`contextUsage`) of `view` against
/// `context_window`: the estimate the compaction threshold reads
/// ([`estimate_context`], spec §8.3), so the percent the user sees is the
/// percent that starts a compaction. The threshold also counts the system
/// entries the next request plans; the shown view holds the committed ones.
pub(crate) fn context_usage(view: &ContextView, context_window: u64) -> Value {
    let tokens = estimate_context(view, &[]);
    #[expect(
        clippy::cast_precision_loss,
        reason = "TS computes the percentage over JS doubles"
    )]
    let percent = tokens as f64 / context_window as f64 * 100.0;
    json!({ "tokens": tokens, "contextWindow": context_window, "percent": percent })
}

/// The chat memory as `get_memory` answers it: its status (the compactor
/// model as the agent dir's settings configure it) with the zoom tool's
/// answer when `zoom` asks one, else the view without its frame.
async fn memory_snapshot(
    memory: &eukhe_core::memory::Memory,
    zoom: Option<MemoryZoom>,
    agent_dir: &std::path::Path,
) -> anyhow::Result<MemorySnapshot> {
    let text = match zoom {
        Some(MemoryZoom { id, count }) => memory.zoom(id, count).await?.text,
        None => unframed_view(&memory.render().await?.text).to_string(),
    };
    Ok(MemorySnapshot {
        status: memory_status(memory, agent_dir).await?,
        text,
    })
}

/// The memory's status as `get_memory` and `get_memory_tree` answer it
/// (the compactor model as the agent dir's settings configure it).
async fn memory_status(
    memory: &eukhe_core::memory::Memory,
    agent_dir: &std::path::Path,
) -> anyhow::Result<MemoryStatusSnapshot> {
    let status = memory.status().await?;
    Ok(MemoryStatusSnapshot {
        messages: status.messages,
        lines: status.view_lines,
        view_bytes: status.view_bytes,
        unsummarized: status.unsummarized,
        running: status.running,
        model: eukhe_core::memory::configured_memory_model(agent_dir),
        last_error: status.last_error,
    })
}

/// One level of the memory tree as `get_memory_tree` answers it.
async fn memory_tree(
    memory: &eukhe_core::memory::Memory,
    node: Option<MemoryZoom>,
    agent_dir: &std::path::Path,
) -> anyhow::Result<MemoryTree> {
    Ok(MemoryTree {
        status: memory_status(memory, agent_dir).await?,
        node,
        level: memory.tree(node).await?,
    })
}

/// The rendered view's `id+n|text` lines without the `<chat>` and `</chat>`
/// frame lines (empty for an empty view).
fn unframed_view(text: &str) -> &str {
    let body = text.strip_prefix("<chat>\n").unwrap_or(text);
    let body = body.strip_suffix("</chat>").unwrap_or(body);
    body.strip_suffix('\n').unwrap_or(body)
}

/// Render the main conversation's system prompt the way its next request
/// prepares it: every section of the resolved agent rendered in order over
/// the sections the transcript already shows (untagged sections as is,
/// tagged ones as `<key>\n...\n</key>`), joined like the provider prompt
/// (non-empty parts separated by a blank line). A section that fails keeps
/// the text the transcript shows for it, as the request preparation does.
/// Sections render without an execution environment (the eukhe prompt
/// reads none).
async fn render_system_prompt(hosted: &HostedSession, cx: &Context) -> Result<String, String> {
    let main = hosted.main().map_err(|error| error.to_string())?;
    let agent = Arc::new(main.agent(cx).await.map_err(|error| error.to_string())?);
    let view = main
        .context(cx, eukhe_durable::harness::types::ContextOptions::default())
        .await
        .map_err(|error| error.to_string())?;
    let shown: IndexMap<String, String> = get_current_system_message(&view.messages)
        .and_then(|message| message.sections)
        .map(|sections| {
            sections
                .into_iter()
                .filter_map(|(key, value)| value.map(|value| (key, value)))
                .collect()
        })
        .unwrap_or_default();
    let input = PromptInput {
        conversation_id: main.id(),
        agent: Arc::clone(&agent),
        env: None,
        shown: shown.clone(),
        read: Arc::new(hosted.harness().clone()),
    };
    let mut parts = Vec::with_capacity(agent.sections.len());
    for section in &agent.sections {
        let text = match (section.render)(&input, cx).await {
            Ok(Some(text)) => {
                if section.tag == Some(false) {
                    text
                } else {
                    let key = &section.key;
                    format!("<{key}>\n{text}\n</{key}>")
                }
            }
            Ok(None) => continue,
            Err(error) => {
                if cx.aborted() {
                    return Err(error.to_string());
                }
                match shown.get(&section.key) {
                    Some(kept) => kept.clone(),
                    None => continue,
                }
            }
        };
        if !text.is_empty() {
            parts.push(text);
        }
    }
    Ok(parts.join("\n\n"))
}

// The usage math (the model registry resolution the create path shares,
// the TS `Usage` wire shape, the folds, the durable ledger's own spend, and
// the legacy-file own/total + by-model computations the child walk reads)
// lives in the child module.
mod usage;

pub(crate) use usage::{
    compute_own_and_total_usage, compute_own_usage_by_model, empty_usage, ledger_usage,
    worker_model_registry,
};

mod resources;

#[cfg(test)]
mod state_getters_tests;
