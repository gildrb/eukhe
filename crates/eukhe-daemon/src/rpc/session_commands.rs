//! The RPC command surface, part four: session-level commands (switch,
//! fork, clone, fork messages, name, export, stats, commands listing)
//! over the durable session, the scheduling and agent-messaging surfaces
//! with their TS in-process semantics, and the gap-set commands whose
//! backends the in-process transport does not host (TS `rpc-mode.ts`
//! cases; the daemon-attached transport serves them for real).

use std::path::Path;
use std::sync::Arc;

use eukhe_core::durable::{fork_main_conversation, fork_session, ForkPoint, SessionLocation};
use eukhe_durable::entries::USER_ENTRY;
use eukhe_durable::types::{EntryId, EntryRecord};
use eukhe_types::pi_ai::{Message, UserContent, UserContentBlock};
use eukhe_types::usage::{calculate_context_tokens, estimate_tokens, valid_assistant_usage};
use serde_json::{json, Value};

use super::commands::RpcState;
use super::protocol::ResponseData;
use super::reads::{
    agent_model, context_messages, history_entries, last_assistant_text, main_agent, rpc_context,
};
use super::session::RpcEngineRequest;
use crate::session_export::durable::export_html as export_session_html;
use crate::worker::durable_host::meta::set_session_name as persist_session_name;

/// The TS in-process error texts for the daemon-mode surfaces
/// (`InProcessAgentConnection`'s throws, verbatim).
const CRON_REQUIRES_DAEMON: &str = "Cron jobs require daemon mode";
const HEARTBEATS_REQUIRE_DAEMON: &str = "Heartbeats require daemon mode";
const AGENT_MESSAGING_REQUIRES_DAEMON: &str = "Agent messaging requires daemon mode";
/// The in-process bash executor is not ported to the Rust session engine
/// yet (TS `AgentSession.executeBash`); the daemon-attached transport
/// serves the command over the worker's bash slot.
const BASH_BACKEND_GAP: &str = "Bash execution requires the session bash executor, which is not linked into the in-process RPC transport yet; the daemon-attached RPC transport serves it";
/// The fork refusal for an entry that is not a user message of the
/// session (TS `runtimeHost.fork`).
const INVALID_FORK_ENTRY: &str = "Invalid entry ID for forking";

/// Handle one session-level command.
///
/// # Errors
///
/// Returns the TS in-process error text for the daemon-mode surfaces and
/// the session-level handlers' own errors.
pub async fn handle(
    state: &Arc<RpcState>,
    name: &str,
    payload: &Value,
) -> Result<ResponseData, String> {
    match name {
        "switch_session" => switch_session(state, payload).await,
        "fork" => fork(state, payload).await,
        "clone" => clone(state).await,
        "get_fork_messages" => get_fork_messages(state).await,
        "get_last_assistant_text" => get_last_assistant_text(state).await,
        "set_session_name" => set_session_name(state, payload).await,
        "get_messages" => get_messages(state).await,
        "export_html" => export_html(state, payload).await,
        "get_session_stats" => get_session_stats(state).await,
        "get_commands" => get_commands(state).await,
        // The TS in-process scheduling surface: the list/get commands
        // answer empty (no scheduler lives in-process); the mutating
        // commands answer their daemon-mode errors.
        "list_schedules" => Ok(ResponseData::Present(json!({ "jobs": [] }))),
        "list_heartbeats" => Ok(ResponseData::Present(json!({ "heartbeats": [] }))),
        "get_heartbeat" => Ok(ResponseData::Present(json!({ "heartbeat": Value::Null }))),
        "add_schedule" | "cancel_schedule" => Err(CRON_REQUIRES_DAEMON.to_string()),
        "set_heartbeat" | "update_heartbeat" | "manage_heartbeat" => {
            Err(HEARTBEATS_REQUIRE_DAEMON.to_string())
        }
        "send_message"
        | "agent_messages_status"
        | "agent_messages_pause"
        | "agent_messages_resume"
        | "agent_messages_clear" => Err(AGENT_MESSAGING_REQUIRES_DAEMON.to_string()),
        // The in-process session hosts no family, so no active session
        // is observable: the TS `watchSession` miss for an unknown child
        // id is the exact answer here.
        "observe" => {
            let id = payload
                .get("activeSessionId")
                .and_then(Value::as_str)
                .unwrap_or_default();
            Err(format!("Unknown active session: {id}"))
        }
        // TS `stopObservation` of a session this connection never
        // observed: a no-op success; `abort_bash` aborts nothing
        // in-process (no bash slot exists) and answers the same.
        "unobserve" | "abort_bash" => Ok(ResponseData::Absent),
        "bash" => Err(BASH_BACKEND_GAP.to_string()),
        unknown => Err(format!("Unknown command: {unknown}")),
    }
}

/// `switch_session` (TS `runtimeHost.switchSession`): open the session (a
/// durable storage directory or a legacy file) as the connection's
/// replacement session.
async fn switch_session(state: &Arc<RpcState>, payload: &Value) -> Result<ResponseData, String> {
    let session_path = payload
        .get("sessionPath")
        .and_then(Value::as_str)
        .ok_or_else(|| "switch_session requires a sessionPath".to_string())?;
    state
        .session
        .replace(RpcEngineRequest::Open {
            session_path: std::path::PathBuf::from(session_path),
            reuse_lease: false,
        })
        .await?;
    Ok(ResponseData::Present(json!({ "cancelled": false })))
}

/// The entry id of a fork command: the string form `get_fork_messages`
/// answers, or a bare number.
fn parse_entry_id(value: &Value) -> Option<EntryId> {
    match value {
        Value::String(text) => text.parse::<u64>().ok().map(EntryId::from_number),
        Value::Number(number) => number.as_u64().map(EntryId::from_number),
        _ => None,
    }
}

/// The text of a user entry (its user message's text blocks, joined).
fn user_entry_text(entry: &EntryRecord) -> Option<String> {
    if !USER_ENTRY.is(Some(entry)) {
        return None;
    }
    entry
        .model
        .as_ref()?
        .iter()
        .find_map(|message| match message {
            Message::User(user) => Some(match &user.content {
                UserContent::Text(text) => text.clone(),
                UserContent::Blocks(blocks) => blocks
                    .iter()
                    .filter_map(|block| match block {
                        UserContentBlock::Text(text) => Some(text.text.as_str()),
                        UserContentBlock::Image(_) => None,
                    })
                    .collect(),
            }),
            _ => None,
        })
}

/// `fork` (TS `runtimeHost.fork(entryId)`, position "before" the user
/// entry): fork the main conversation just before the user entry (at its
/// predecessor, or empty when it is the first entry) and move the
/// connection onto the fork; the selected text rides the response.
async fn fork(state: &Arc<RpcState>, payload: &Value) -> Result<ResponseData, String> {
    let entry_id = payload
        .get("entryId")
        .and_then(parse_entry_id)
        .ok_or_else(|| "fork requires an entryId".to_string())?;
    // One replacement lease across the history read AND the fork: a
    // switch_session or new_session landing between them would fork the
    // retired session at the entry validated on the live one.
    let lease = state.session.replacement_lease().await;
    let history = history_entries(&state.session.session().await.main(), &rpc_context()).await?;
    let index = history
        .iter()
        .position(|entry| entry.id == entry_id)
        .ok_or_else(|| INVALID_FORK_ENTRY.to_string())?;
    let text = user_entry_text(&history[index]).ok_or_else(|| INVALID_FORK_ENTRY.to_string())?;
    let point = match index.checked_sub(1) {
        Some(previous) => ForkPoint::Entry(history[previous].id),
        None => ForkPoint::Start,
    };
    fork_at(state, point).await?;
    drop(lease);
    Ok(ResponseData::Present(
        json!({ "cancelled": false, "text": text }),
    ))
}

/// `clone` (TS `connection.clone` -> `fork(leafId, { position: "at" })`):
/// fork at the latest entry; a session without entries answers the TS
/// error.
async fn clone(state: &Arc<RpcState>) -> Result<ResponseData, String> {
    let lease = state.session.replacement_lease().await;
    let history = history_entries(&state.session.session().await.main(), &rpc_context()).await?;
    if history.is_empty() {
        return Err("Cannot clone session: no current entry selected".to_string());
    }
    fork_at(state, ForkPoint::Latest).await?;
    drop(lease);
    Ok(ResponseData::Present(json!({ "cancelled": false })))
}

/// The shared fork tail (the caller holds the replacement lease): settle
/// the running turn, then a persisted session forks into a new storage
/// directory the connection switches onto (TS forks into a new session
/// file); an in-memory session forks its main conversation in place and
/// the pump follows the new main.
async fn fork_at(state: &Arc<RpcState>, point: ForkPoint) -> Result<(), String> {
    let cx = rpc_context();
    let session = state.session.session().await;
    let main = session.main();
    main.wait_for_idle(&cx)
        .await
        .map_err(|error| error.to_string())?;
    let Some(storage_dir) = session.deps().storage_dir.clone() else {
        let _ops = state.session_ops.lock().await;
        fork_main_conversation(session.harness(), &main, point, None, &cx)
            .await
            .map_err(|error| error.to_string())?;
        session
            .reload_main(&cx)
            .await
            .map_err(|error| error.to_string())?;
        return state.session.reattach_pump(&session).await;
    };
    let sessions_dir = storage_dir
        .parent()
        .ok_or_else(|| format!("Session storage {} has no parent", storage_dir.display()))?;
    let forked_dir = sessions_dir.join(uuid::Uuid::now_v7().to_string());
    fork_session(
        &SessionLocation::Durable(storage_dir.clone()),
        point,
        None,
        &forked_dir,
        &cx,
    )
    .await
    .map_err(|error| error.to_string())?;
    drop(session);
    state
        .session
        .replace_locked(RpcEngineRequest::Open {
            session_path: forked_dir,
            reuse_lease: false,
        })
        .await
}

/// `get_fork_messages` (TS `getUserMessagesForForking`): the user
/// messages with text, oldest first.
async fn get_fork_messages(state: &Arc<RpcState>) -> Result<ResponseData, String> {
    let history = history_entries(&state.session.session().await.main(), &rpc_context()).await?;
    let messages: Vec<Value> = history
        .iter()
        .filter_map(|entry| {
            let text = user_entry_text(entry).filter(|text| !text.is_empty())?;
            Some(json!({ "entryId": entry.id.to_string(), "text": text }))
        })
        .collect();
    Ok(ResponseData::Present(json!({ "messages": messages })))
}

/// `get_last_assistant_text` (TS `getLastAssistantText`): the last
/// assistant message's concatenated text.
async fn get_last_assistant_text(state: &Arc<RpcState>) -> Result<ResponseData, String> {
    let messages = context_messages(&state.session.session().await.main(), &rpc_context()).await?;
    Ok(ResponseData::Present(
        json!({ "text": last_assistant_text(&messages) }),
    ))
}

/// `set_session_name` (TS `session.setSessionName`): the durable session
/// name plus the `session_info_changed` event.
async fn set_session_name(state: &Arc<RpcState>, payload: &Value) -> Result<ResponseData, String> {
    let name = payload
        .get("name")
        .and_then(Value::as_str)
        .map(str::trim)
        .ok_or_else(|| "set_session_name requires a name".to_string())?;
    if name.is_empty() {
        return Err("Session name cannot be empty".to_string());
    }
    // Serialize the rename with any whole-session replacement: a switch
    // between the write and the event would publish the retired
    // session's name as the live session's.
    let _lease = state.session.replacement_lease().await;
    let session = state.session.session().await;
    persist_session_name(session.harness(), Some(name.to_string()), &rpc_context())
        .await
        .map_err(|error| error.to_string())?;
    state
        .session
        .outputs()
        .write(json!({ "type": "session_info_changed", "name": name }));
    Ok(ResponseData::Absent)
}

/// `get_messages` (TS `session.state.messages`): the main conversation's
/// active context.
async fn get_messages(state: &Arc<RpcState>) -> Result<ResponseData, String> {
    let messages = context_messages(&state.session.session().await.main(), &rpc_context()).await?;
    Ok(ResponseData::Present(json!({ "messages": messages })))
}

/// `export_html` (TS `session.exportToHtml`): the standalone viewer file
/// over the main conversation; the response carries the written path. A
/// relative output path lands under the SESSION's project.
async fn export_html(state: &Arc<RpcState>, payload: &Value) -> Result<ResponseData, String> {
    let output_path = payload.get("outputPath").and_then(Value::as_str);
    let handle = state.session.handle().await;
    let session = &handle.session;
    let deps = session.deps();
    if deps.storage_dir.is_none() {
        return Err("Cannot export an in-memory session".to_string());
    }
    let output_path = output_path.map(|path| {
        let path = Path::new(path);
        if path.is_absolute() {
            path.display().to_string()
        } else {
            deps.cwd.join(path).display().to_string()
        }
    });
    let path = export_session_html(
        deps,
        &session.main(),
        output_path.as_deref(),
        &rpc_context(),
    )
    .await
    .map_err(|error| format!("{error:#}"))?;
    Ok(ResponseData::Present(json!({ "path": path })))
}

/// The per-role counts and token totals of `messages` (TS
/// `getSessionStats`).
fn message_stats(messages: &[Value]) -> Value {
    let mut user_messages = 0u64;
    let mut assistant_messages = 0u64;
    let mut tool_calls = 0u64;
    let mut tool_results = 0u64;
    let mut input = 0u64;
    let mut output = 0u64;
    let mut cache_read = 0u64;
    let mut cache_write = 0u64;
    let mut cost = 0.0;
    let usage_field = |usage: &Value, key: &str| usage.get(key).and_then(Value::as_u64);
    for message in messages {
        match message.get("role").and_then(Value::as_str) {
            Some("user") => user_messages += 1,
            Some("assistant") => {
                assistant_messages += 1;
                if let Some(blocks) = message.get("content").and_then(Value::as_array) {
                    tool_calls += blocks
                        .iter()
                        .filter(|block| {
                            block.get("type").and_then(Value::as_str) == Some("toolCall")
                        })
                        .map(|_| 1)
                        .sum::<u64>();
                }
                if let Some(usage) = message.get("usage") {
                    input += usage_field(usage, "input").unwrap_or_default();
                    output += usage_field(usage, "output").unwrap_or_default();
                    cache_read += usage_field(usage, "cacheRead").unwrap_or_default();
                    cache_write += usage_field(usage, "cacheWrite").unwrap_or_default();
                    cost += usage
                        .get("cost")
                        .and_then(|cost| cost.get("total"))
                        .and_then(Value::as_f64)
                        .unwrap_or_default();
                }
            }
            Some("toolResult") => tool_results += 1,
            _ => {}
        }
    }
    json!({
        "userMessages": user_messages,
        "assistantMessages": assistant_messages,
        "toolCalls": tool_calls,
        "toolResults": tool_results,
        // TS `SessionStats.totalMessages` counts the role rows (user +
        // assistant); custom rows must not inflate it.
        "totalMessages": user_messages + assistant_messages,
        "tokens": {
            "input": input,
            "output": output,
            "cacheRead": cache_read,
            "cacheWrite": cache_write,
            "total": input + output + cache_read + cache_write,
        },
        "cost": cost,
    })
}

/// TS `estimateContextTokens`: the last valid assistant usage anchors the
/// estimate; messages after it add their char/4 estimates, and no anchor
/// estimates every message.
fn context_tokens(messages: &[Value]) -> u64 {
    let anchor = messages
        .iter()
        .enumerate()
        .rev()
        .find_map(|(index, message)| valid_assistant_usage(message).map(|usage| (index, usage)));
    match anchor {
        Some((index, usage)) => {
            calculate_context_tokens(&usage)
                + messages[index + 1..]
                    .iter()
                    .map(estimate_tokens)
                    .sum::<u64>()
        }
        None => messages.iter().map(estimate_tokens).sum(),
    }
}

/// `get_session_stats` (TS `getSessionStats` over `state.messages`).
async fn get_session_stats(state: &Arc<RpcState>) -> Result<ResponseData, String> {
    let handle = state.session.handle().await;
    let session = &handle.session;
    let deps = session.deps();
    let cx = rpc_context();
    let messages = context_messages(&session.main(), &cx).await?;
    let agent = main_agent(session, &cx).await?;
    let mut session_stats = json!({
        "sessionFile": deps
            .storage_dir
            .as_ref()
            .map(|dir| dir.display().to_string()),
        "sessionId": deps.session_id,
    });
    if let (Value::Object(object), Value::Object(counts)) =
        (&mut session_stats, message_stats(&messages))
    {
        object.extend(counts);
    }
    let context_window = agent_model(session, &agent).map_or(0, |model| model.context_window);
    if context_window > 0 {
        let tokens = context_tokens(&messages);
        #[expect(
            clippy::cast_precision_loss,
            reason = "TS computes the percentage over JS doubles"
        )]
        let percent = tokens as f64 / context_window as f64 * 100.0;
        session_stats["contextUsage"] = json!({
            "tokens": tokens,
            "contextWindow": context_window,
            "percent": percent,
        });
    }
    Ok(ResponseData::Present(session_stats))
}

/// `get_commands` (TS `createAgentConnectionCommands`): prompt
/// templates, then skills.
async fn get_commands(state: &Arc<RpcState>) -> Result<ResponseData, String> {
    let session = state.session.session().await;
    let resources = &session.deps().resources;
    let mut commands: Vec<Value> = Vec::new();
    for template in &resources.prompts {
        let mut entry = json!({
            "name": template.name,
            "source": "prompt",
            "sourceInfo": template.source_info,
        });
        if let Some(hint) = &template.argument_hint {
            entry["argumentHint"] = json!(hint);
        }
        if !template.description.is_empty() {
            entry["description"] = json!(template.description);
        }
        commands.push(entry);
    }
    for skill in &resources.skills {
        let mut entry = json!({
            "name": format!("skill:{}", skill.name),
            "source": "skill",
            "sourceInfo": skill.source_info,
        });
        if !skill.description.is_empty() {
            entry["description"] = json!(skill.description);
        }
        commands.push(entry);
    }
    Ok(ResponseData::Present(json!({ "commands": commands })))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn entry_ids_parse_from_strings_and_numbers() {
        assert_eq!(parse_entry_id(&json!("12")), Some(EntryId::from_number(12)));
        assert_eq!(parse_entry_id(&json!(7)), Some(EntryId::from_number(7)));
        assert_eq!(parse_entry_id(&json!("nope")), None);
        assert_eq!(parse_entry_id(&Value::Null), None);
    }

    #[test]
    fn message_stats_count_roles_and_usage() {
        let messages = vec![
            json!({ "role": "user", "content": "hi" }),
            json!({
                "role": "assistant",
                "content": [
                    { "type": "text", "text": "x" },
                    { "type": "toolCall", "id": "c", "name": "t", "arguments": {} },
                ],
                "usage": {
                    "input": 10, "output": 5, "cacheRead": 2, "cacheWrite": 1,
                    "cost": { "total": 0.5 },
                },
            }),
            json!({ "role": "toolResult", "content": [] }),
            json!({ "role": "custom", "content": "row" }),
        ];
        assert_eq!(
            message_stats(&messages),
            json!({
                "userMessages": 1,
                "assistantMessages": 1,
                "toolCalls": 1,
                "toolResults": 1,
                "totalMessages": 2,
                "tokens": {
                    "input": 10, "output": 5, "cacheRead": 2, "cacheWrite": 1, "total": 18,
                },
                "cost": 0.5,
            })
        );
    }
}
