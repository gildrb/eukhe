//! Report texts a parent receives about its children (TS
//! `createRlmChildTerminalNoticeMessage` / `createRlmChildFailureMessage`)
//! and the roster's one-line labels (daemon `rlm_child_model.rs`).

use eukhe_types::input_origin::{ChildExit, ChildFailure, InputOrigin, Report};

use crate::agent_messaging::sanitize_message_header_value;
use serde::{Deserialize, Serialize};

/// Cap on the one-line task label shown in kernel rosters.
const LABEL_MAX_CHARS: usize = 200;
const ELLIPSIS: &str = "...";

/// The reason a deleted running child's notice carries.
pub(crate) const DELETED_BY_PARENT: &str = "Deleted by parent orchestrator";

/// How a child run ended, as reported to the parent.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(
    tag = "kind",
    rename_all = "camelCase",
    rename_all_fields = "camelCase"
)]
pub(crate) enum ChildReport {
    /// The parent deleted a still-running child.
    Cancelled {
        session_name: String,
        reason: Option<String>,
    },
    /// The child finished its task without sending an agent message back.
    CompletedWithoutReply {
        session_name: String,
        last_assistant_text_preview: Option<String>,
    },
    /// The child's run failed. `failure` is absent on a report checkpointed
    /// before failures were typed.
    Failed {
        session_name: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        failure: Option<ChildFailure>,
        error: String,
    },
}

impl ChildReport {
    /// The typed origin of the report input.
    pub(crate) fn origin(&self) -> InputOrigin {
        InputOrigin::Report {
            report: self.report(),
        }
    }

    /// The follow-up text: `[child-exited: cancelled|no-reply child:<name>]`
    /// or `[child-failed: <failure> child:<name>]` with the reason,
    /// preview, or error as the body.
    pub(crate) fn text(&self) -> String {
        let body = match self {
            Self::Cancelled { reason, .. } => reason.clone().unwrap_or_default(),
            Self::CompletedWithoutReply {
                last_assistant_text_preview,
                ..
            } => last_assistant_text_preview
                .as_deref()
                .filter(|preview| !preview.is_empty())
                .map(|preview| format!("Last assistant text: {preview}"))
                .unwrap_or_default(),
            Self::Failed { error, .. } => error.clone(),
        };
        self.report().render(&body)
    }

    fn report(&self) -> Report {
        match self {
            Self::Cancelled { session_name, .. } => Report::ChildExited {
                child: sanitize_message_header_value(session_name),
                exit: ChildExit::Cancelled,
            },
            Self::CompletedWithoutReply { session_name, .. } => Report::ChildExited {
                child: sanitize_message_header_value(session_name),
                exit: ChildExit::NoReply,
            },
            Self::Failed {
                session_name,
                failure,
                ..
            } => Report::ChildFailed {
                child: sanitize_message_header_value(session_name),
                failure: *failure,
            },
        }
    }
}

/// One-line task label: the collapsed prompt, capped for roster rows.
pub(crate) fn rlm_child_label(prompt: &str) -> String {
    let collapsed = prompt.split_whitespace().collect::<Vec<_>>().join(" ");
    if collapsed.is_empty() {
        return "child agent".to_owned();
    }
    if collapsed.chars().count() <= LABEL_MAX_CHARS {
        return collapsed;
    }
    let kept: String = collapsed
        .chars()
        .take(LABEL_MAX_CHARS - ELLIPSIS.len())
        .collect();
    format!("{}{ELLIPSIS}", kept.trim_end())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_reply_notice_matches_the_ts_shape() {
        let report = ChildReport::CompletedWithoutReply {
            session_name: "f20-worker".to_owned(),
            last_assistant_text_preview: Some("done with the task".to_owned()),
        };
        assert_eq!(
            report.text(),
            "[child-exited: no-reply child:f20-worker]\n\nLast assistant text: done with the task"
        );
    }

    #[test]
    fn cancelled_notice_without_reason_has_no_body() {
        let report = ChildReport::Cancelled {
            session_name: "worker [x]".to_owned(),
            reason: None,
        };
        assert_eq!(report.text(), "[child-exited: cancelled child:worker x]");
    }

    #[test]
    fn cancelled_notice_carries_the_reason_body() {
        let report = ChildReport::Cancelled {
            session_name: "worker".to_owned(),
            reason: Some(DELETED_BY_PARENT.to_owned()),
        };
        assert_eq!(
            report.text(),
            "[child-exited: cancelled child:worker]\n\nDeleted by parent orchestrator"
        );
    }

    #[test]
    fn failure_notice_names_the_typed_failure() {
        let report = ChildReport::Failed {
            session_name: "lane".to_owned(),
            failure: Some(ChildFailure::Provider {
                kind: eukhe_types::pi_ai::StreamFailureKind::RateLimit,
            }),
            error: "429 usage limit".to_owned(),
        };
        assert_eq!(
            report.text(),
            "[child-failed: provider-rate_limit child:lane]\n\n429 usage limit"
        );
        assert_eq!(
            report.origin(),
            InputOrigin::Report {
                report: Report::ChildFailed {
                    child: "lane".to_owned(),
                    failure: Some(ChildFailure::Provider {
                        kind: eukhe_types::pi_ai::StreamFailureKind::RateLimit,
                    }),
                },
            }
        );
    }

    #[test]
    fn untyped_failure_checkpoint_keeps_the_ts_shape() {
        let report: ChildReport = serde_json::from_value(serde_json::json!({
            "kind": "failed", "sessionName": "lane", "error": "boom",
        }))
        .expect("a checkpoint from before typed failures loads");
        assert_eq!(report.text(), "[child-failed child:lane]\n\nboom");
    }

    #[test]
    fn labels_collapse_whitespace_and_cap() {
        assert_eq!(rlm_child_label("  do\n the   thing "), "do the thing");
        assert_eq!(rlm_child_label(" \n"), "child agent");
        let long = "x".repeat(300);
        let label = rlm_child_label(&long);
        assert_eq!(label.chars().count(), LABEL_MAX_CHARS);
        assert!(label.ends_with(ELLIPSIS));
    }
}
