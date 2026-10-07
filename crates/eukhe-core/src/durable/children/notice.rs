//! Report texts a parent receives about its children (port of the content
//! text of `session_engine/rlm_notices.rs`, TS
//! `createRlmChildTerminalNoticeMessage` / `createRlmChildFailureMessage`)
//! and the roster's one-line labels (daemon `rlm_child_model.rs`).

/// Cap on the one-line task label shown in kernel rosters.
const LABEL_MAX_CHARS: usize = 200;
const ELLIPSIS: &str = "...";

/// The reason a deleted running child's notice carries.
pub(crate) const DELETED_BY_PARENT: &str = "Deleted by parent orchestrator";

/// How a child run ended, as reported to the parent.
#[derive(Debug, Clone, PartialEq, Eq)]
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
    /// The child's run failed.
    Failed { session_name: String, error: String },
}

impl ChildReport {
    /// The follow-up text: `[child-exited: cancelled|no-reply child:<name>]`
    /// or `[child-failed child:<name>]` with the reason, preview, or error as
    /// the body.
    pub(crate) fn text(&self) -> String {
        match self {
            Self::Cancelled {
                session_name,
                reason,
            } => {
                let name = sanitize_message_header_value(session_name);
                let mut content = format!("[child-exited: cancelled child:{name}]");
                if let Some(reason) = reason.as_deref().filter(|reason| !reason.is_empty()) {
                    content.push_str("\n\n");
                    content.push_str(reason);
                }
                content
            }
            Self::CompletedWithoutReply {
                session_name,
                last_assistant_text_preview,
            } => {
                let name = sanitize_message_header_value(session_name);
                let mut content = format!("[child-exited: no-reply child:{name}]");
                if let Some(preview) = last_assistant_text_preview
                    .as_deref()
                    .filter(|preview| !preview.is_empty())
                {
                    content.push_str("\n\nLast assistant text: ");
                    content.push_str(preview);
                }
                content
            }
            Self::Failed {
                session_name,
                error,
            } => {
                let name = sanitize_message_header_value(session_name);
                format!("[child-failed child:{name}]\n\n{error}")
            }
        }
    }
}

/// Names interpolated into a `[<kind> ...]` header line must not carry the
/// characters that delimit the header (brackets, newlines, commas, or ":"):
/// runs of those collapse into one space, then the value trims (TS
/// `sanitizeMessageHeaderValue`).
fn sanitize_message_header_value(value: &str) -> String {
    let mut out = String::with_capacity(value.len());
    let mut pending_space = false;
    for char in value.chars() {
        if char.is_whitespace() || matches!(char, ',' | ':' | '[' | ']') {
            pending_space = true;
        } else {
            if pending_space && !out.is_empty() {
                out.push(' ');
            }
            pending_space = false;
            out.push(char);
        }
    }
    out
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
    fn failure_notice_matches_the_ts_shape() {
        let report = ChildReport::Failed {
            session_name: "lane".to_owned(),
            error: "boom".to_owned(),
        };
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
