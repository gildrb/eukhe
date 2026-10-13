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
//! running background bash handles, its own unsettled children) still
//! run, since their settlement wakes it into another run; else `Answered`.

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::durable::children::{unsettled_child_tasks, RlmChildRunState};
use eukhe_core::durable::rlm::kernel_background_jobs;
use eukhe_durable::entries::ASSISTANT_ENTRY;
use eukhe_types::input_origin::ChildFailure;
use eukhe_types::pi_ai::{AssistantMessage, Message, StopReason, StreamFailureKind};

use super::durable_host::wire_messages::assistant_wire_message;
use super::summary::queued_inputs;
use super::{response_failure, response_success, Worker};
use crate::protocol::DaemonResponse;

/// The diagnostic a terminal provider stream failure records; its
/// `details.kind` is the [`StreamFailureKind`].
const PROVIDER_STREAM_FAILURE: &str = "provider_stream_failure";

impl Worker {
    /// `get_run_outcome`: the main conversation's [`RlmChildRunState`].
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
            match unsettled_child_tasks(hosted.harness(), main.id(), &BACKGROUND_CONTEXT).await {
                Ok(children) => children.len(),
                Err(error) => return response_failure(None, COMMAND, &error.to_string(), None),
            };
        let pending_jobs = children + kernel_background_jobs(hosted.deps(), main.id());
        let state = {
            let core = self
                .core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            let busy = core.is_busy() || core.is_compacting() || queued_inputs(&core) > 0;
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
            run_outcome(
                busy,
                u32::try_from(pending_jobs).unwrap_or(u32::MAX),
                last.as_ref(),
            )
        };
        match serde_json::to_value(&state) {
            Ok(data) => response_success(None, COMMAND, Some(data)),
            Err(error) => response_failure(None, COMMAND, &error.to_string(), None),
        }
    }
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
                .map(|message| crate::types::message_text(&assistant_wire_message(message)))
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
}
