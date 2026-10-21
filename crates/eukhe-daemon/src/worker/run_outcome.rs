//! `get_run_outcome`: the session's run outcome, read from its durable
//! state, as a parent's child-settle watch needs it (omp2 ADR 0004: the
//! lifecycle derives from the durable tree, not from "idle twice").
//!
//! A run in flight (or an input still owed a turn) is `Running`. Otherwise
//! the last assistant entry is the last run's terminal: a provider error
//! is `Failed` with the provider's classified kind and an abort is
//! `Failed` as aborted — a failed run settles now even while background
//! jobs remain, the failure is what the parent must act on. A run that
//! answered is `Idle` while background jobs it started (the kernel's
//! running background bash handles, its own unsettled children and
//! workflow runs) still
//! run, since their settlement wakes it into another run; else `Answered`.
//!
//! The reply carries the session's progress token (rule H5): its distinct
//! acts (tool calls with their results, and accepted progress notes:
//! [`eukhe_core::durable::children::WorkLedger`]), plus its unsettled
//! children's tokens, plus its kernel
//! jobs' output progress. So a parent sees this child progress while it
//! does new work, waits on a busy child of its own, or waits on a
//! background job that writes output (a long build or test run). Events
//! are not progress: a child that streams, retries, or repeats the same
//! calls with the same results keeps its token, and its parent reports it
//! stalled after `subagentStallMs`.

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::durable::children::{
    unsettled_children, RlmChildOutcome, RlmChildRunState, RLM_CHILD_ANSWER_MAX_BYTES,
};
use eukhe_core::durable::rlm::{kernel_background_jobs, kernel_job_progress};
use eukhe_core::durable::workflow::unsettled_runs;
use eukhe_durable::entries::ASSISTANT_ENTRY;
use eukhe_types::input_origin::ChildFailure;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, Message, StopReason, StreamFailureKind,
};

use super::session_core::SessionCore;
use super::summary::queued_inputs;
use super::{response_failure, response_success, Worker};
use crate::protocol::DaemonResponse;

/// The diagnostic a terminal provider stream failure records; its
/// `details.kind` is the [`StreamFailureKind`].
const PROVIDER_STREAM_FAILURE: &str = "provider_stream_failure";

impl Worker {
    /// `get_run_outcome`: the main conversation's [`RlmChildOutcome`].
    pub(crate) async fn handle_get_run_outcome(&self) -> DaemonResponse {
        const COMMAND: &str = "get_run_outcome";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let main = match hosted.main() {
            Ok(main) => main,
            Err(error) => return response_failure(None, COMMAND, &error.to_string(), None),
        };
        let children =
            match unsettled_children(hosted.harness(), main.id(), &BACKGROUND_CONTEXT).await {
                Ok(children) => children,
                Err(error) => return response_failure(None, COMMAND, &error.to_string(), None),
            };
        let runs = match unsettled_runs(hosted.harness(), main.id(), &BACKGROUND_CONTEXT).await {
            Ok(runs) => runs,
            Err(error) => return response_failure(None, COMMAND, &error.to_string(), None),
        };
        let pending_jobs =
            children.count + runs.count + kernel_background_jobs(hosted.deps(), main.id());
        let job_progress = kernel_job_progress(hosted.deps(), main.id()).await;
        let state = {
            let mut core = self
                .core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            let busy = core.is_busy() || core.is_compacting() || queued_inputs(&core) > 0;
            let work = work_progress(&mut core);
            let last = core.view.as_ref().and_then(|view| {
                view.translator
                    .mirror()
                    .entries
                    .iter()
                    .rev()
                    .filter(|entry| entry.kind == ASSISTANT_ENTRY.kind())
                    .find_map(|entry| {
                        entry
                            .model
                            .as_deref()
                            .and_then(<[Message]>::first)
                            .and_then(Message::as_assistant)
                            .cloned()
                    })
            });
            let state = run_outcome(
                busy,
                u32::try_from(pending_jobs).unwrap_or(u32::MAX),
                last.as_ref(),
            );
            let answer = match &state {
                RlmChildRunState::Answered { .. } => last.as_ref().and_then(full_answer),
                RlmChildRunState::Running
                | RlmChildRunState::Idle { .. }
                | RlmChildRunState::Failed { .. } => None,
            };
            RlmChildOutcome {
                state,
                progress: Some(
                    work.wrapping_add(children.progress)
                        .wrapping_add(runs.progress)
                        .wrapping_add(job_progress),
                ),
                answer,
            }
        };
        match serde_json::to_value(&state) {
            Ok(data) => response_success(None, COMMAND, Some(data)),
            Err(error) => response_failure(None, COMMAND, &error.to_string(), None),
        }
    }
}

/// The session's own work ([`eukhe_core::durable::children::WorkLedger`]):
/// the ledger reads the entries of the shown conversation it did not read
/// yet and the latest accepted progress note.
fn work_progress(core: &mut SessionCore) -> u64 {
    if let Some(view) = &core.view {
        core.work_ledger
            .read_entries(&view.translator.mirror().entries);
    }
    if let Some(note) = &core.progress_note {
        core.work_ledger.read_note(&note.text);
    }
    core.work_ledger.count()
}

/// The text blocks of `message` joined by blank lines, capped at
/// [`RLM_CHILD_ANSWER_MAX_BYTES`] on a char boundary; `None` when it has
/// no text.
fn full_answer(message: &AssistantMessage) -> Option<String> {
    let text = message
        .content
        .iter()
        .filter_map(|block| match block {
            AssistantContentBlock::Text(text) => Some(text.text.as_str()),
            AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => None,
        })
        .collect::<Vec<_>>()
        .join("\n\n");
    if text.trim().is_empty() {
        return None;
    }
    if text.len() <= RLM_CHILD_ANSWER_MAX_BYTES {
        return Some(text);
    }
    let mut end = RLM_CHILD_ANSWER_MAX_BYTES;
    while !text.is_char_boundary(end) {
        end -= 1;
    }
    Some(text[..end].to_owned())
}

/// The run outcome of a session `busy` or not, owning `pending_jobs`
/// background jobs, whose last assistant entry is `last`.
fn run_outcome(busy: bool, pending_jobs: u32, last: Option<&AssistantMessage>) -> RlmChildRunState {
    if busy {
        return RlmChildRunState::Running;
    }
    let settled = || {
        if pending_jobs > 0 {
            return RlmChildRunState::Idle { pending_jobs };
        }
        RlmChildRunState::Answered {
            answer_preview: last
                .map(|message| {
                    message
                        .content
                        .iter()
                        .filter_map(|block| {
                            let AssistantContentBlock::Text(text) = block else {
                                return None;
                            };
                            Some(text.text.as_str())
                        })
                        .collect::<Vec<_>>()
                        .join(" ")
                })
                .filter(|text| !text.is_empty())
                .map(|text| crate::rlm_child_model::compact_rlm_text(&text)),
        }
    };
    let Some(message) = last else {
        return settled();
    };
    let failed = |failure: ChildFailure| RlmChildRunState::Failed {
        failure,
        error: message
            .error_message
            .clone()
            .filter(|error| !error.is_empty())
            .unwrap_or_else(|| format!("The child's run failed ({failure})")),
    };
    match message.stop_reason {
        StopReason::Error => {
            let kind = message
                .diagnostics
                .as_deref()
                .unwrap_or_default()
                .iter()
                .rev()
                .filter(|diagnostic| diagnostic.kind == PROVIDER_STREAM_FAILURE)
                .find_map(|diagnostic| {
                    StreamFailureKind::parse(diagnostic.details.as_ref()?.get("kind")?.as_str()?)
                })
                .unwrap_or(StreamFailureKind::Unknown);
            failed(ChildFailure::Provider { kind })
        }
        StopReason::Aborted => failed(ChildFailure::Aborted),
        StopReason::Stop
        | StopReason::Length
        | StopReason::ToolUse
        | StopReason::Pending
        | StopReason::Deferred => settled(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use eukhe_types::pi_ai::{AssistantMessageDiagnostic, JsonObject};
    use serde_json::json;

    fn assistant(stop_reason: &str, extra: serde_json::Value) -> AssistantMessage {
        let mut message = json!({
            "role": "assistant",
            "content": [{ "type": "text", "text": "The full check is running." }],
            "api": "anthropic-messages",
            "provider": "anthropic",
            "model": "claude",
            "usage": {
                "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
                "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
            },
            "stopReason": stop_reason,
            "timestamp": 1,
        });
        if let (Some(message), serde_json::Value::Object(extra)) = (message.as_object_mut(), extra)
        {
            message.extend(extra);
        }
        serde_json::from_value(message).expect("an assistant message")
    }

    /// Regression (stuck.md cause 3): a child that ended its turn while a
    /// background job it started still runs is idle with that job, not
    /// answered.
    #[test]
    fn an_answer_with_a_pending_job_is_idle() {
        let last = assistant("stop", json!({}));
        assert_eq!(
            run_outcome(false, 1, Some(&last)),
            RlmChildRunState::Idle { pending_jobs: 1 }
        );
        assert_eq!(
            run_outcome(false, 0, Some(&last)),
            RlmChildRunState::Answered {
                answer_preview: Some("The full check is running.".to_owned()),
            }
        );
        assert_eq!(run_outcome(true, 1, Some(&last)), RlmChildRunState::Running);
    }

    /// Regression (stuck.md causes 3 and 6): a run that ended on a
    /// provider error is a failure with the provider's classified kind,
    /// even while a background job remains.
    #[test]
    fn a_provider_error_is_a_typed_failure() {
        let mut details = JsonObject::new();
        details.insert("kind".to_owned(), json!("auth"));
        details.insert("status".to_owned(), json!(401));
        let mut last = assistant(
            "error",
            json!({ "errorMessage": "401 OAuth access token has expired" }),
        );
        last.diagnostics = Some(vec![AssistantMessageDiagnostic {
            kind: PROVIDER_STREAM_FAILURE.to_owned(),
            timestamp: 1,
            error: None,
            details: Some(details),
        }]);
        assert_eq!(
            run_outcome(false, 1, Some(&last)),
            RlmChildRunState::Failed {
                failure: ChildFailure::Provider {
                    kind: StreamFailureKind::Auth,
                },
                error: "401 OAuth access token has expired".to_owned(),
            }
        );
        // An error without a classified diagnostic still fails, as unknown.
        let unclassified = assistant(
            "error",
            json!({ "errorMessage": "No API key for provider: anthropic" }),
        );
        assert_eq!(
            run_outcome(false, 0, Some(&unclassified)),
            RlmChildRunState::Failed {
                failure: ChildFailure::Provider {
                    kind: StreamFailureKind::Unknown,
                },
                error: "No API key for provider: anthropic".to_owned(),
            }
        );
    }

    #[test]
    fn an_aborted_run_is_an_aborted_failure() {
        let last = assistant("aborted", json!({}));
        assert_eq!(
            run_outcome(false, 0, Some(&last)),
            RlmChildRunState::Failed {
                failure: ChildFailure::Aborted,
                error: "The child's run failed (aborted)".to_owned(),
            }
        );
    }

    /// The core showing a conversation with `entries`, as a new snapshot
    /// installs it (the ledger reads a replaced view again).
    fn show(core: &mut SessionCore, entries: &[serde_json::Value]) {
        let snapshot = serde_json::from_value(json!({
            "entries": entries, "tools": [], "nestedTools": [], "compactions": [], "inbox": [],
            "agent": {}, "usage": { "models": {}, "tools": {} },
        }))
        .expect("snapshot");
        core.view = Some(crate::worker::durable_host::ShownView {
            epoch: 1,
            translator: crate::worker::durable_host::translator::EventTranslator::new(
                &snapshot,
                crate::worker::durable_host::translator::CoalesceMode::Immediate,
            ),
            inbox: Vec::new(),
            active: None,
            goal: serde_json::Value::Null,
        });
    }

    /// One round: the call `read {"path": path}` with id `id`, its result
    /// `text`, and some words around the call.
    fn round(entries: &mut Vec<serde_json::Value>, id: &str, path: &str, text: &str) {
        let mut call = serde_json::to_value(assistant("toolUse", json!({}))).expect("json");
        call["content"] = json!([
            { "type": "thinking", "thinking": format!("thinking about {id}") },
            { "type": "text", "text": format!("Let me check again ({id}).") },
            { "type": "toolCall", "id": id, "name": "read", "arguments": { "path": path } },
        ]);
        let result = json!({
            "role": "toolResult", "toolCallId": id, "toolName": "read",
            "content": [{ "type": "text", "text": text }], "isError": false, "timestamp": 2,
        });
        for (kind, message) in [("pi.assistant", call), ("pi.toolResult", result)] {
            let id = entries.len() + 1;
            entries
                .push(json!({ "model": [message], "kind": kind, "id": id, "conversationId": 1 }));
        }
    }

    /// Regression (audit H7): the progress token was the session's event
    /// sequence, so a child that loops (the same call with the same result,
    /// new words and thinking each time, streamed events) moved it at every
    /// poll and was never stalled. The token is the session's work now:
    /// a repeat keeps it, a new result or a new progress note moves it.
    #[test]
    fn a_looping_child_keeps_its_progress_token() {
        let mut core = SessionCore::test_core("/tmp".to_owned());
        let mut entries = Vec::new();
        let mut tokens = Vec::new();
        round(&mut entries, "c1", "a.rs", "fn a() {}");
        show(&mut core, &entries);
        tokens.push(work_progress(&mut core));
        for id in ["c2", "c3", "c4"] {
            core.last_event_sequence += 50;
            round(&mut entries, id, "a.rs", "fn a() {}");
            show(&mut core, &entries);
            tokens.push(work_progress(&mut core));
        }
        round(&mut entries, "c5", "a.rs", "fn a() { b() }");
        show(&mut core, &entries);
        tokens.push(work_progress(&mut core));
        core.progress_note = Some(crate::worker::summary::TimedNote {
            text: "editing a.rs".to_owned(),
            at_ms: 1,
        });
        tokens.push(work_progress(&mut core));
        tokens.push(work_progress(&mut core));
        assert_eq!(tokens, vec![1, 1, 1, 1, 2, 3, 3]);
    }
}
