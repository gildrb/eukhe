//! The editor's say on an irreversible effect (spec I12): before a `bash`
//! step, a document access or an MCP call whose classes are irreversible
//! runs, the session's [`EditorPermissionSink`] is asked (the daemon
//! asks the editor attached through ACP). Allow runs it, reject refuses
//! it; with no sink, nothing asks. A reversible effect never asks.

use eukhe_bend::rules::irreversible;
use eukhe_types::effects::{EditorPermissionRequest, EditorVerdict, EffectClass};

use super::deps::EditorPermissionSink;

/// What the agent reads of an effect the editor refused.
pub(crate) const EDITOR_REFUSED: &str = "the editor refused it";

/// Whether an effect of `classes` (`command`, for people) may run: true
/// unless it is irreversible and the editor rejects it. `request_id` is
/// unique within the session; `tool_call_id` names the tool call that
/// runs it.
pub(crate) async fn allows(
    sink: Option<EditorPermissionSink>,
    request_id: String,
    tool_call_id: Option<String>,
    command: String,
    classes: Vec<EffectClass>,
) -> bool {
    let Some(sink) = sink else {
        return true;
    };
    if !irreversible::is_irreversible(&classes) {
        return true;
    }
    let verdict = sink(EditorPermissionRequest {
        request_id,
        tool_call_id,
        command,
        classes,
        agent: None,
    })
    .await;
    verdict != EditorVerdict::Reject
}
