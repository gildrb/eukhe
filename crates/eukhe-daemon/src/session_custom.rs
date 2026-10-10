//! The custom-message & session-command surface (protocol breadth wave
//! b4): the worker arms for `append_custom_message`, `restore_next_turn`,
//! `restore_actions`, `refine`, and `reload` (TS daemon-mode cases). Wire
//! contracts are TS-verbatim. Custom rows are `eukhe.custom` write
//! submissions on the main conversation (the event bridge broadcasts their
//! `message_start`/`message_end`); restored actions are input submissions
//! keyed by their action id, so a repeated restore never queues twice.

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::durable::custom_entry_draft;
use eukhe_core::durable::rlm::{refine_now, RefineRequest};
use eukhe_durable::harness::types::{WhenBusy, WriteSubmissionDraft};
use eukhe_durable::harness::Conversation;
use eukhe_types::pi_ai::UserContent;
use serde_json::{json, Value};

use crate::protocol::{response_failure, response_success, DaemonResponse};
use crate::worker::{parse_prompt_images, submit_input, InputRequest, Worker};

/// The session-action recovery snapshot format this port restores (TS
/// `SESSION_ACTION_RECOVERY_FORMAT_VERSION`).
const SESSION_ACTION_RECOVERY_FORMAT_VERSION: u64 = 1;

impl Worker {
    /// `append_custom_message { message }` (TS `session.sendCustomMessage`
    /// default path): append the custom row durably; the event bridge
    /// broadcasts its `message_start`/`message_end` pair.
    pub(crate) async fn handle_append_custom_message(&self, payload: &Value) -> DaemonResponse {
        let hosted = match self.hosted("append_custom_message") {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let Some(message) = custom_message_value(payload.get("message")) else {
            return response_failure(
                None,
                "append_custom_message",
                "append_custom_message requires a custom message",
                None,
            );
        };
        let written = async {
            let main = hosted.main()?;
            write_custom_row(&main, &message).await
        }
        .await;
        match written {
            Ok(()) => response_success(None, "append_custom_message", None),
            Err(error) => {
                response_failure(None, "append_custom_message", &format!("{error:#}"), None)
            }
        }
    }

    /// `restore_next_turn { messages }` (TS
    /// `restorePendingNextTurnMessages`): the custom rows land, in order,
    /// before the next delivered turn's prompt — written now when the
    /// conversation is idle, else queued in the inbox for the next boundary.
    pub(crate) async fn handle_restore_next_turn(&self, payload: &Value) -> DaemonResponse {
        let hosted = match self.hosted("restore_next_turn") {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let Some(messages) = payload.get("messages").and_then(Value::as_array) else {
            return response_failure(
                None,
                "restore_next_turn",
                "restore_next_turn requires a messages array",
                None,
            );
        };
        let mut rows = Vec::with_capacity(messages.len());
        for message in messages {
            let Some(row) = custom_message_value(Some(message)) else {
                return response_failure(
                    None,
                    "restore_next_turn",
                    "restore_next_turn requires custom messages",
                    None,
                );
            };
            rows.push(row);
        }
        let written = async {
            let main = hosted.main()?;
            for row in &rows {
                write_custom_row(&main, row).await?;
            }
            anyhow::Ok(())
        }
        .await;
        match written {
            Ok(()) => response_success(None, "restore_next_turn", None),
            Err(error) => response_failure(None, "restore_next_turn", &format!("{error:#}"), None),
        }
    }

    /// `restore_actions { snapshot }` (TS `restoreSessionActions`): the
    /// crash-recovery snapshot of queued session actions. The TS-verbatim
    /// validation errors fail the command; every restored action is
    /// admitted on its delivery lane (steer for `next_turn_boundary`,
    /// follow-up for `when_run_idle`) under the request id
    /// `restored-action:<id>`, and the response carries the restored count.
    pub(crate) async fn handle_restore_actions(&self, payload: &Value) -> DaemonResponse {
        let hosted = match self.hosted("restore_actions") {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let Some(snapshot) = payload.get("snapshot").and_then(Value::as_object) else {
            return response_failure(
                None,
                "restore_actions",
                "restore_actions requires a snapshot",
                None,
            );
        };
        let format_version = snapshot
            .get("formatVersion")
            .and_then(Value::as_u64)
            .unwrap_or_default();
        if format_version != SESSION_ACTION_RECOVERY_FORMAT_VERSION {
            return response_failure(
                None,
                "restore_actions",
                &format!("Unsupported session action recovery format version: {format_version}"),
                None,
            );
        }
        let Some(actions) = snapshot.get("actions").and_then(Value::as_array) else {
            return response_failure(
                None,
                "restore_actions",
                "restore_actions requires a snapshot actions array",
                None,
            );
        };
        // Validation pass first (TS validates every action before
        // admitting any): ids must be unique within the snapshot, and a
        // turn payload's delivery records must correlate to their action.
        let mut seen_ids = std::collections::HashSet::new();
        for action in actions {
            let Some(id) = action.get("id").and_then(Value::as_str) else {
                return response_failure(
                    None,
                    "restore_actions",
                    "restore_actions requires an action id",
                    None,
                );
            };
            if !seen_ids.insert(id.to_string()) {
                return response_failure(
                    None,
                    "restore_actions",
                    &format!("Duplicate session action id: {id}"),
                    None,
                );
            }
            let payload = action.get("payload").unwrap_or(&Value::Null);
            if payload.get("kind").and_then(Value::as_str) == Some("turn") {
                let records = payload
                    .get("records")
                    .and_then(Value::as_array)
                    .cloned()
                    .unwrap_or_default();
                let correlated = records
                    .iter()
                    .all(|record| record.get("ownerActionId").and_then(Value::as_str) == Some(id));
                if !correlated {
                    return response_failure(
                        None,
                        "restore_actions",
                        &format!("Session action {id} has invalid delivery correlation"),
                        None,
                    );
                }
            }
            // The reserved child-status kinds are daemon provenance (the
            // queue-fold anti-spoof): a restored custom row claiming one
            // is caller-supplied on this surface — answered loudly, the
            // whole snapshot refused before any action admits. The
            // daemon-written recovery journal is the only legitimate
            // source of a parked reserved-kind row.
            if let Some(row) = payload.get("customMessage") {
                if crate::child_status_notices::is_reserved_child_status_custom_type(row) {
                    return response_failure(
                        None,
                        "restore_actions",
                        &format!(
                            "{} (action {id})",
                            crate::child_status_notices::reserved_intake_error()
                        ),
                        None,
                    );
                }
            }
        }
        let main = match hosted.main() {
            Ok(main) => main,
            Err(error) => {
                return response_failure(None, "restore_actions", &error.to_string(), None)
            }
        };
        for action in actions {
            let id = action.get("id").and_then(Value::as_str).unwrap_or_default();
            let payload = action.get("payload").unwrap_or(&Value::Null);
            let request = InputRequest {
                text: payload
                    .get("text")
                    .and_then(Value::as_str)
                    .unwrap_or_default()
                    .to_string(),
                images: parse_prompt_images(payload),
                custom_row: payload
                    .get("customMessage")
                    .filter(|message| !message.is_null())
                    .cloned(),
                when_busy: if action.get("delivery").and_then(Value::as_str)
                    == Some("next_turn_boundary")
                {
                    WhenBusy::Steer
                } else {
                    WhenBusy::FollowUp
                },
                request_id: Some(format!("restored-action:{id}")),
            };
            if let Err(error) = submit_input(&main, &request, &BACKGROUND_CONTEXT).await {
                return response_failure(None, "restore_actions", &format!("{error:#}"), None);
            }
        }
        response_success(
            None,
            "restore_actions",
            Some(json!({ "restored": actions.len() })),
        )
    }

    /// `refine { instructions?, rollbackId?, global? }` (TS
    /// `session.refine`): run the refinement on the main conversation
    /// (plan, apply, persist the harness state, commit the audit, outcome
    /// and notice rows) and answer the `RefinementResult`.
    pub(crate) async fn handle_refine(&self, payload: &Value) -> DaemonResponse {
        let hosted = match self.hosted("refine") {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let request = RefineRequest {
            instructions: payload
                .get("instructions")
                .and_then(Value::as_str)
                .map(str::to_string),
            rollback_id: payload
                .get("rollbackId")
                .and_then(Value::as_str)
                .map(str::to_string),
            global: payload
                .get("global")
                .and_then(Value::as_bool)
                .unwrap_or(false),
        };
        let refined = async {
            let main = hosted.main()?;
            refine_now(hosted.deps(), &main, request, &BACKGROUND_CONTEXT).await
        }
        .await;
        match refined {
            Ok(result) => {
                // The committed audit row carries `refine_complete` through
                // the event bridge; answer once it reached the wire.
                hosted.events_delivered().await;
                response_success(
                    None,
                    "refine",
                    Some(serde_json::to_value(&result).unwrap_or(Value::Null)),
                )
            }
            Err(error) => {
                // A failed refinement commits nothing: the failure event
                // (TS `refine_failed`) is the worker's to emit.
                let error = format!("{error:#}");
                self.emit_worker_event(json!({
                    "type": "refine_failed",
                    "error": error,
                }));
                response_failure(None, "refine", &error, None)
            }
        }
    }

    /// `reload` (TS `session.reload`): re-read the session's live inputs —
    /// settings, provider auth, and the MCP user-server config. This port
    /// resolves each of those per use (the settings source reloads on file
    /// change, auth on every model resolution, MCP user servers on every
    /// store resolve), so the reload's observable state is already fresh and
    /// the command is the TS success with no extra work to perform.
    pub(crate) fn handle_reload(&self) -> DaemonResponse {
        if let Err(response) = self.require_created("reload") {
            return response;
        }
        response_success(None, "reload", None)
    }
}

/// Write one wire custom row (`custom_message_value` shape) as an
/// `eukhe.custom` entry on `conversation`: at once when idle, else at the
/// next boundary.
pub(crate) async fn write_custom_row(
    conversation: &Conversation,
    row: &Value,
) -> anyhow::Result<()> {
    let custom_type = row
        .get("customType")
        .and_then(Value::as_str)
        .unwrap_or_default()
        .to_string();
    let content: UserContent =
        serde_json::from_value(row.get("content").cloned().unwrap_or(Value::Null))?;
    let display = row.get("display").and_then(Value::as_bool).unwrap_or(true);
    let details = row
        .get("details")
        .cloned()
        .filter(|details| !details.is_null());
    let timestamp = row
        .get("timestamp")
        .and_then(Value::as_u64)
        .unwrap_or_else(crate::util::now_ms);
    let entry = custom_entry_draft(custom_type, content, display, details, timestamp)?;
    conversation
        .submit(
            WriteSubmissionDraft {
                request_id: None,
                entry,
            },
            &BACKGROUND_CONTEXT,
        )
        .await?;
    Ok(())
}

/// The wire `CustomMessage` form (TS `Pick<CustomMessage, "customType" |
/// "content" | "display" | "details">` plus the row's timestamp): the
/// durable row the session appends and broadcasts.
fn custom_message_value(message: Option<&Value>) -> Option<Value> {
    let message = message?.as_object()?;
    let custom_type = message.get("customType")?;
    custom_type.as_str()?;
    let content = message.get("content")?;
    if !matches!(content, Value::String(_) | Value::Array(_)) {
        return None;
    }
    let display = message
        .get("display")
        .and_then(Value::as_bool)
        .unwrap_or(true);
    let mut row = json!({
        "role": "custom",
        "customType": custom_type,
        "content": content,
        "display": display,
        "timestamp": crate::util::now_ms(),
    });
    if let Some(details) = message.get("details").filter(|details| !details.is_null()) {
        row["details"] = details.clone();
    }
    Some(row)
}

#[cfg(test)]
mod tests;
