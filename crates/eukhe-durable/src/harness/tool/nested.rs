//! Nested calls of the tool task (`harness/tool.ts`): the caller's index of
//! its nested calls and their results, admission of a nested call, and the
//! results and summaries a nested call settles with.

use eukhe_chord::context::Context;
use eukhe_chord::json::{to_json, JsonValue};
use eukhe_types::pi_ai::{JsonObject as PiJsonObject, JsonValue as PiJsonValue, ToolCall};
use futures::future::BoxFuture;
use futures::FutureExt;
use indexmap::IndexMap;
use serde::{Deserialize, Serialize};
use std::sync::{Arc, Mutex, PoisonError};

use super::result::harness_error;
use super::{Runtime, ToolTaskInput, ToolTaskResult};
use crate::documents::{DocDefinition, DocFamilyDefinition, TaskDoc, TaskDocFamily};
use crate::harness::live::{
    child_draft, NestedToolSlot, NestedToolSummary, ToolSlotStatus, LIVE_DOC,
};
use crate::harness::types::{
    NestedToolExecutionResult, ToolDiagnosticSeverity, ToolExecutionResult,
};
use crate::session::{SessionError, SessionResult, Tx};
use crate::types::{TaskId, TaskOptions, TaskOutcome, TaskOwnership};
use eukhe_types::pi_ai::UserContentBlock;

/// The caller's index of its nested calls by key, so a rerun of the call
/// finds the nested calls it already made (TS `NestedCallsDoc`).
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub(super) struct NestedCalls {
    pub(super) calls: IndexMap<String, TaskId>,
}

/// `pi.tool.nested`: [`NestedCalls`] of one tool task.
pub(super) static NESTED_CALLS_DOC: TaskDoc<NestedCalls> = match TaskDoc::define(DocDefinition {
    kind: "pi.tool.nested",
    version: 1,
    initial: NestedCalls::default,
    migrate: None,
    checkpoint_when: None,
}) {
    Ok(token) => token,
    Err(_) => panic!("invalid pi.tool.nested definition"),
};

/// One nested call's result, exactly as `execute_tool()` returns it.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct NestedResultState {
    pub result: NestedToolExecutionResult,
}

/// `pi.tool.nested-result` (TS `NestedResultDoc`): the result of one nested
/// call, a member of its caller's family keyed by the nested task ID. Written
/// in the nested call's terminal commit; one document per result, so no
/// write rewrites other results. Retires with the caller.
pub static NESTED_RESULT_DOC: TaskDocFamily<NestedResultState, NestedResultState> =
    match TaskDocFamily::define(DocFamilyDefinition {
        kind: "pi.tool.nested-result",
        version: 1,
        initial: |seed: NestedResultState| seed,
        migrate: None,
        checkpoint_when: None,
    }) {
        Ok(token) => token,
        Err(_) => panic!("invalid pi.tool.nested-result definition"),
    };

/// What a nested call is made with.
pub(super) struct NestedCallRequest {
    pub(super) parent_call_id: String,
    pub(super) name: String,
    pub(super) args: PiJsonObject,
    pub(super) key: String,
    pub(super) progress: Option<bool>,
    pub(super) abandon_on_restart: bool,
}

/// Create nested call `key` of the call `parent_call_id` in one commit,
/// enqueued now: its tool task, owned by the calling task, its slot, and its
/// index entry. A key already in the index returns that call's task when it
/// names the same tool and arguments.
pub(super) fn start_nested_call(
    runtime: &Runtime,
    request: NestedCallRequest,
    cx: &Context,
) -> BoxFuture<'static, SessionResult<TaskId>> {
    let NestedCallRequest {
        parent_call_id,
        name,
        args,
        key,
        progress,
        abandon_on_restart,
    } = request;
    let call = ToolCall {
        id: format!("{parent_call_id}/{key}"),
        name,
        arguments: args,
        ..ToolCall::default()
    };
    let task_id = runtime.task_id().erase();
    let conversation_id = runtime.conversation_id();
    let tool = runtime.registry().builtins().tool.clone();
    let created = Arc::new(Mutex::new(None));
    let slot = Arc::clone(&created);
    let committed = runtime.commit(
        move |tx, _current| async move {
            let index = tx.doc(&NESTED_CALLS_DOC, task_id).await?;
            let calls = index.child("calls")?;
            let existing = calls
                .get(key.as_str())?
                .and_then(|item| match item {
                    eukhe_chord::delta::DraftItem::Value(value) => value.as_u64(),
                    eukhe_chord::delta::DraftItem::Draft(_) => None,
                })
                .map(TaskId::from_number);
            if let Some(existing) = existing {
                check_reattach(&tx, existing, task_id, &call).await?;
                *slot.lock().unwrap_or_else(PoisonError::into_inner) = Some(existing);
                return Ok(None);
            }
            let input = ToolTaskInput::Nested {
                parent: task_id,
                parent_call_id: parent_call_id.clone(),
                key: key.clone(),
                call: call.clone(),
                progress: (progress == Some(false)).then_some(false),
            };
            let created_id = tx
                .create_task(
                    tool.as_definition_ref(),
                    to_json(&input)?,
                    TaskOptions {
                        ownership: TaskOwnership::Task { task_id },
                        conversation_id: None,
                        background: None,
                        abandon_on_restart: Some(abandon_on_restart),
                    },
                )
                .await?;
            calls.set(key.as_str(), to_json(&created_id)?)?;
            let live = tx.doc(&LIVE_DOC, conversation_id).await?;
            if child_draft(&live, "nestedTools")?.is_none() {
                live.set("nestedTools", JsonValue::array())?;
            }
            let nested_slot = NestedToolSlot {
                call_id: call.id.clone(),
                name: call.name.clone(),
                status: ToolSlotStatus::Pending,
                output: None,
                dropped_bytes: None,
                dropped_lines: None,
                details: None,
                diagnostics: None,
                parent_call_id,
                parent_task_id: task_id,
                task_id: created_id,
                arguments: call.arguments,
                summary: None,
            };
            live.child("nestedTools")?.push([to_json(&nested_slot)?])?;
            *slot.lock().unwrap_or_else(PoisonError::into_inner) = Some(created_id);
            Ok(None)
        },
        cx,
    );
    async move {
        committed.await?;
        let id = created
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .take();
        id.ok_or_else(|| SessionError::error("Nested call admission committed without a task"))
    }
    .boxed()
}

/// Reattaching to `existing` under the same key requires the same tool and
/// arguments, made by the same caller.
async fn check_reattach(
    tx: &Tx,
    existing: TaskId,
    task_id: TaskId,
    call: &ToolCall,
) -> SessionResult<()> {
    let input = match tx.task(existing).await? {
        Some(record) => eukhe_chord::json::from_json::<ToolTaskInput>(&record.input).ok(),
        None => None,
    };
    let same = matches!(
        &input,
        Some(ToolTaskInput::Nested { parent, call: made, .. })
            if *parent == task_id
                && made.name == call.name
                && json_equal(
                    &PiJsonValue::Object(made.arguments.clone()),
                    &PiJsonValue::Object(call.arguments.clone()),
                )
    );
    if same {
        return Ok(());
    }
    Err(SessionError::error(format!(
        "Nested call {} was already made with another tool or other arguments",
        call.id
    )))
}

/// A nested call's result, as stored and returned: without `output`, which
/// only the model reads, and without `control`, which only model-issued
/// calls apply.
pub(super) fn nested_result(
    task_id: TaskId,
    result: &ToolExecutionResult,
    duration_ms: Option<u64>,
) -> NestedToolExecutionResult {
    NestedToolExecutionResult {
        task_id,
        structured_output: result.structured_output.clone(),
        is_error: result.is_error.unwrap_or(false),
        details: result.details.clone(),
        diagnostics: result.diagnostics.clone().unwrap_or_default(),
        usage: result.usage,
        duration_ms,
    }
}

/// What programs get of a tool's output when it declares no schema: one text
/// item as its string, one image as itself, nothing as `""`, and anything
/// else as the content list.
pub(super) fn output_value(output: &[UserContentBlock]) -> SessionResult<JsonValue> {
    Ok(match output {
        [] => JsonValue::from(""),
        [UserContentBlock::Text(text)] => JsonValue::from(text.text.as_str()),
        [only @ UserContentBlock::Image(_)] => to_json(only)?,
        list => to_json(&list)?,
    })
}

/// What the caller gets for a nested call without a stored result: one the
/// scheduler faulted or orphaned.
pub(super) fn fallback_result(
    task_id: TaskId,
    name: &str,
    outcome: &TaskOutcome<ToolTaskResult>,
) -> NestedToolExecutionResult {
    let (status, message) = match outcome {
        TaskOutcome::Faulted { error } => {
            ("faulted", format!("Tool {name} failed: {}", error.message))
        }
        TaskOutcome::Orphaned { reason } => (
            "orphaned",
            format!("Tool {name} could not resume: {reason}"),
        ),
        TaskOutcome::Completed { .. } => ("completed", ended_without_result(name)),
        TaskOutcome::Failed { .. } => ("failed", ended_without_result(name)),
        TaskOutcome::Aborted { .. } => ("aborted", ended_without_result(name)),
    };
    let error = harness_error(status, &message);
    NestedToolExecutionResult {
        task_id,
        structured_output: None,
        is_error: true,
        details: None,
        diagnostics: error.diagnostics.unwrap_or_default(),
        usage: None,
        duration_ms: None,
    }
}

fn ended_without_result(name: &str) -> String {
    format!("Tool {name} ended without a result")
}

/// Error text a nested call's summary keeps, in UTF-16 code units (JS
/// `String.prototype.slice`).
const MAX_SUMMARY_ERROR_CHARS: usize = 500;

/// How a nested call ended, for its slot: error text, from its diagnostics
/// or else its `output`, bounded.
pub(super) fn summary_of(
    result: &NestedToolExecutionResult,
    output: &[UserContentBlock],
) -> NestedToolSummary {
    let error = if result.is_error {
        utf16_prefix(&error_text_of(result, output), MAX_SUMMARY_ERROR_CHARS)
    } else {
        String::new()
    };
    NestedToolSummary {
        is_error: result.is_error,
        duration_ms: result.duration_ms,
        usage: result.usage,
        error: (!error.is_empty()).then_some(error),
    }
}

/// The first `units` UTF-16 code units of `text`. A character the bound
/// splits is left out: JS would keep its lone high surrogate, which a Rust
/// string cannot hold.
fn utf16_prefix(text: &str, units: usize) -> String {
    let mut count = 0;
    let mut end = 0;
    for (index, c) in text.char_indices() {
        count += c.len_utf16();
        if count > units {
            break;
        }
        end = index + c.len_utf8();
    }
    text[..end].to_owned()
}

/// The error messages of a nested result, else the text items of its
/// output, joined with newlines.
fn error_text_of(result: &NestedToolExecutionResult, output: &[UserContentBlock]) -> String {
    let errors: Vec<&str> = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == ToolDiagnosticSeverity::Error)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect();
    if !errors.is_empty() {
        return errors.join("\n");
    }
    output
        .iter()
        .filter_map(|item| match item {
            UserContentBlock::Text(text) => Some(text.text.as_str()),
            UserContentBlock::Image(_) => None,
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Explicit nested call keys are path segments of the call ID, so IDs of
/// different nested calls never collide, and are never plain positive
/// integers, which default keys use. `__proto__` would not land in the TS
/// index as an own key.
pub(super) fn check_key(key: &str) -> SessionResult<()> {
    let positive_integer = key
        .as_bytes()
        .first()
        .is_some_and(|first| (b'1'..=b'9').contains(first))
        && key.bytes().all(|byte| byte.is_ascii_digit());
    if key.is_empty() || key.contains('/') || key == "__proto__" || positive_integer {
        let quoted = serde_json::to_string(key).map_err(SessionError::other)?;
        return Err(SessionError::error(format!(
            "Nested call key {quoted} must be non-empty, without \"/\", not \"__proto__\", and not a positive integer"
        )));
    }
    Ok(())
}

/// Structural JSON equality; object key order does not matter, and numbers
/// compare by value, as JS `===` does.
pub(super) fn json_equal(a: &PiJsonValue, b: &PiJsonValue) -> bool {
    match (a, b) {
        (PiJsonValue::Number(a), PiJsonValue::Number(b)) => a.as_f64() == b.as_f64(),
        (PiJsonValue::Array(a), PiJsonValue::Array(b)) => {
            a.len() == b.len() && a.iter().zip(b).all(|(a, b)| json_equal(a, b))
        }
        (PiJsonValue::Object(a), PiJsonValue::Object(b)) => {
            a.len() == b.len()
                && a.iter()
                    .all(|(key, value)| b.get(key).is_some_and(|other| json_equal(value, other)))
        }
        (a, b) => a == b,
    }
}
