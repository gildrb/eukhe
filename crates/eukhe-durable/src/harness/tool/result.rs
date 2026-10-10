//! Result building of the tool task: Harness error results, truncation
//! diagnostics, bounded content, and the `pi.tool-result` entry.

use eukhe_chord::json::from_json;
use eukhe_types::pi_ai::{
    JsonValue as PiJsonValue, Message, TextContent, ToolCall, ToolResultMessage, UserContentBlock,
};

use crate::entries::{ToolResultData, TOOL_RESULT_ENTRY};
use crate::harness::live::SlotProgress;
use crate::harness::output::{bound_output, OutputLimits};
use crate::harness::types::{
    OutputRetain, ToolDiagnostic, ToolDiagnosticSeverity, ToolExecutionResult,
};
use crate::harness::usage::{record_usage, UsageBucket};
use crate::session::{SessionResult, Tx};
use crate::types::{ConversationId, TypedEntry, TypedEntryDraft};

/// How a tool task ends; the result is settled either way. `Failed`
/// (execution threw or was interrupted) records cancellation intent for the
/// conversations the call owns; a result with `is_error` still completes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum ToolEnding {
    Completed,
    Aborted,
    Failed { message: String },
}

/// An error diagnostic with `code`.
pub(super) fn tool_diagnostic(code: &str, message: &str) -> ToolDiagnostic {
    ToolDiagnostic {
        severity: ToolDiagnosticSeverity::Error,
        code: Some(code.to_owned()),
        message: message.to_owned(),
    }
}

/// An error result the Harness writes itself: no output and one `error`
/// diagnostic with `code`.
#[must_use]
pub fn harness_error(code: &str, message: &str) -> ToolExecutionResult {
    ToolExecutionResult {
        output: Some(Vec::new()),
        is_error: Some(true),
        diagnostics: Some(vec![tool_diagnostic(code, message)]),
        ..ToolExecutionResult::default()
    }
}

/// The Harness's truncation diagnostic; `retain` is unknown when rebuilt from
/// a slot after recovery.
pub(super) fn truncated(
    dropped_lines: u64,
    dropped_bytes: u64,
    retain: Option<OutputRetain>,
) -> ToolDiagnostic {
    let kept = match retain {
        None => "",
        Some(OutputRetain::Head) => " to its beginning",
        Some(OutputRetain::Tail) => " to its end",
    };
    ToolDiagnostic {
        severity: ToolDiagnosticSeverity::Warn,
        code: Some("truncated".to_owned()),
        message: format!(
            "Output truncated{kept}: {dropped_lines} lines, {dropped_bytes} bytes dropped"
        ),
    }
}

/// An error result from the slot's durable partial output, details, and
/// diagnostics.
pub(super) fn from_slot(
    slot: Option<&SlotProgress>,
    code: &str,
    message: &str,
) -> ToolExecutionResult {
    let mut diagnostics = slot
        .and_then(|slot| slot.diagnostics.clone())
        .unwrap_or_default();
    let dropped_bytes = slot.and_then(|slot| slot.dropped_bytes).unwrap_or(0);
    if dropped_bytes > 0 {
        let dropped_lines = slot.and_then(|slot| slot.dropped_lines).unwrap_or(0);
        diagnostics.push(truncated(dropped_lines, dropped_bytes, None));
    }
    diagnostics.push(tool_diagnostic(code, message));
    let output = match slot.and_then(|slot| slot.output.as_deref()) {
        None | Some("") => Vec::new(),
        Some(output) => vec![UserContentBlock::Text(TextContent::new(output))],
    };
    ToolExecutionResult {
        output: Some(output),
        is_error: Some(true),
        details: slot.and_then(|slot| slot.details.clone()),
        diagnostics: Some(diagnostics),
        ..ToolExecutionResult::default()
    }
}

fn severity_text(severity: ToolDiagnosticSeverity) -> &'static str {
    match severity {
        ToolDiagnosticSeverity::Info => "info",
        ToolDiagnosticSeverity::Warn => "warn",
        ToolDiagnosticSeverity::Error => "error",
    }
}

fn render_diagnostics(diagnostics: &[ToolDiagnostic]) -> String {
    let lines: Vec<String> = diagnostics
        .iter()
        .map(|diagnostic| {
            format!(
                "[{}] {}",
                severity_text(diagnostic.severity),
                diagnostic.message
            )
        })
        .collect();
    format!("<harness>\n{}\n</harness>", lines.join("\n"))
}

/// When a result was created and how long its execution took (TS `{
/// timestamp, durationMs? }`).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ToolResultMeta {
    /// The Harness clock.
    pub timestamp: f64,
    /// How long `execute()` took in this attempt, measured with a monotonic
    /// clock; `None` for calls that did not execute, and for interrupted or
    /// aborted calls.
    pub duration_ms: Option<u64>,
}

/// Append a `pi.tool-result` entry. The content ends with the rendered
/// diagnostics, so the stored message is exactly what the model sees; `data`
/// keeps the structured list. A result's usage is added to `pi.usage` in the
/// same commit.
///
/// # Errors
///
/// The transaction settled, the details are not JSON, or a usage document
/// failure.
pub async fn append_tool_result(
    tx: &Tx,
    conversation_id: ConversationId,
    call: &ToolCall,
    result: &ToolExecutionResult,
    meta: ToolResultMeta,
) -> SessionResult<TypedEntry<ToolResultData>> {
    let ToolResultMeta {
        timestamp,
        duration_ms,
    } = meta;
    let diagnostics = result.diagnostics.clone().unwrap_or_default();
    let mut content = result.output.clone().unwrap_or_default();
    if !diagnostics.is_empty() {
        content.push(UserContentBlock::Text(TextContent::new(
            render_diagnostics(&diagnostics),
        )));
    }
    let details = match &result.details {
        Some(details) => Some(from_json::<PiJsonValue>(details)?),
        None => None,
    };
    let message = ToolResultMessage {
        tool_call_id: call.id.clone(),
        tool_name: call.name.clone(),
        content,
        details,
        usage: result.usage,
        nested_calls: None,
        is_error: result.is_error.unwrap_or(false),
        timestamp: timestamp_ms(timestamp),
        duration_ms,
    };
    if let Some(usage) = &result.usage {
        record_usage(tx, conversation_id, UsageBucket::Tools, &call.name, usage).await?;
    }
    tx.append_typed_entry(
        &TOOL_RESULT_ENTRY,
        conversation_id,
        TypedEntryDraft {
            model: Some(vec![Message::ToolResult(message)]),
            data: ToolResultData { diagnostics },
            head: None,
            edits: None,
        },
    )
    .await
}

/// The Harness clock as the message's millisecond timestamp.
#[expect(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    reason = "the Harness clock is a non-negative millisecond time"
)]
fn timestamp_ms(timestamp: f64) -> u64 {
    timestamp as u64
}

/// Bounded result content and what bounding dropped.
pub(super) struct BoundedContent {
    pub(super) content: Vec<UserContentBlock>,
    pub(super) dropped_bytes: usize,
    pub(super) dropped_lines: usize,
}

/// Bound the text of result content. When the joined text exceeds the
/// limits, the text items are replaced by one bounded item at the position of
/// the first (head) or last (tail) text item; other content is kept.
pub(super) fn bound_content(
    content: Vec<UserContentBlock>,
    limits: &OutputLimits,
) -> BoundedContent {
    let texts: Vec<usize> = content
        .iter()
        .enumerate()
        .filter_map(|(index, item)| matches!(item, UserContentBlock::Text(_)).then_some(index))
        .collect();
    let joined: String = content
        .iter()
        .filter_map(|item| match item {
            UserContentBlock::Text(text) => Some(text.text.as_str()),
            UserContentBlock::Image(_) => None,
        })
        .collect();
    let bounded = bound_output(&joined, limits);
    if bounded.dropped_bytes == 0 {
        return BoundedContent {
            content,
            dropped_bytes: 0,
            dropped_lines: 0,
        };
    }
    let keep = match limits.retain {
        OutputRetain::Head => texts.first(),
        OutputRetain::Tail => texts.last(),
    }
    .copied();
    let mut result = Vec::new();
    let mut text = Some(bounded.text);
    for (index, item) in content.into_iter().enumerate() {
        match item {
            UserContentBlock::Image(_) => result.push(item),
            UserContentBlock::Text(mut item) => {
                if Some(index) == keep {
                    item.text = text.take().unwrap_or_default();
                    result.push(UserContentBlock::Text(item));
                }
            }
        }
    }
    BoundedContent {
        content: result,
        dropped_bytes: bounded.dropped_bytes,
        dropped_lines: bounded.dropped_lines,
    }
}
