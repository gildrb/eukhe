//! What main sent its worker (docs/interface.md, "Worker pane"): the
//! user's own messages, byte for byte, as a task, context, or a redirect,
//! with main's optional note. The worker's transcript shows it as the
//! received `agent_message` row (`details.deliveryKind`), main's as its
//! `worker_assign` / `worker_forward` tool card (the result's details);
//! both render the same body so the user sees exactly what went.

use serde_json::Value;

/// How the worker takes a forwarded message.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ForwardKind {
    /// New work.
    Task,
    /// Information for the running work: folded in, no change of course.
    Context,
    /// A change of course: the worker re-plans at its next boundary.
    Redirect,
}

impl ForwardKind {
    fn parse(kind: &str) -> Option<Self> {
        match kind {
            "task" => Some(Self::Task),
            "context" => Some(Self::Context),
            "redirect" => Some(Self::Redirect),
            _ => None,
        }
    }

    /// The row's label.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Self::Task => "Task",
            Self::Context => "Context",
            Self::Redirect => "Redirect",
        }
    }
}

/// One forward: its kind, the user's messages in order, main's note.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Forward {
    pub kind: ForwardKind,
    /// Each forwarded user message's text, verbatim, in order.
    pub user_messages: Vec<String>,
    /// How many images rode the messages (the rows name the count).
    pub images: usize,
    /// Main's own note, labelled apart from the user's words.
    pub note: Option<String>,
    /// The worker it went to (main's tool card names it).
    pub worker: Option<String>,
}

impl Forward {
    /// The forward a row's or a tool result's `details` carry
    /// (`deliveryKind`, `userMessages`, `note`, `worker`); `None` when
    /// they carry none.
    #[must_use]
    pub fn from_details(details: &Value) -> Option<Self> {
        let kind = ForwardKind::parse(details.get("deliveryKind")?.as_str()?)?;
        let messages = details
            .get("userMessages")
            .and_then(Value::as_array)
            .map(Vec::as_slice)
            .unwrap_or_default();
        let text = |key: &str| {
            details
                .get(key)
                .and_then(Value::as_str)
                .filter(|text| !text.trim().is_empty())
                .map(str::to_string)
        };
        Some(Self {
            kind,
            user_messages: messages
                .iter()
                // A message is its text, or `{text, images}`.
                .filter_map(|message| {
                    message
                        .as_str()
                        .or_else(|| message.get("text").and_then(Value::as_str))
                })
                .map(str::to_string)
                .collect(),
            images: messages
                .iter()
                .filter_map(|message| message.get("images").and_then(Value::as_array))
                .map(Vec::len)
                .sum(),
            note: text("note"),
            worker: text("worker"),
        })
    }

    /// The body every view shows: the user's messages (a blank line
    /// between two), the image count, then `[note from main] <note>`.
    #[must_use]
    pub fn body(&self) -> String {
        let mut parts = self.user_messages.clone();
        if self.images > 0 {
            parts.push(format!(
                "[{} image{}]",
                self.images,
                if self.images == 1 { "" } else { "s" }
            ));
        }
        if let Some(note) = &self.note {
            parts.push(format!("[note from main] {note}"));
        }
        parts.join("\n\n")
    }
}

#[cfg(test)]
mod tests {
    use super::{Forward, ForwardKind};
    use serde_json::json;

    #[test]
    fn a_forward_keeps_the_users_words_in_order_and_labels_the_note() {
        let forward = Forward::from_details(&json!({
            "deliveryKind": "context",
            "userMessages": ["use  tabs\n", {"text": "and the v2 api", "images": [{}]}],
            "note": "the user asked this mid-run",
            "worker": "worker",
        }))
        .unwrap();
        assert_eq!(
            forward,
            Forward {
                kind: ForwardKind::Context,
                user_messages: vec!["use  tabs\n".to_string(), "and the v2 api".to_string()],
                images: 1,
                note: Some("the user asked this mid-run".to_string()),
                worker: Some("worker".to_string()),
            }
        );
        assert_eq!(
            forward.body(),
            "use  tabs\n\n\nand the v2 api\n\n[1 image]\n\n[note from main] the user asked this mid-run"
        );
        assert_eq!(
            Forward::from_details(&json!({"deliveryKind": "steer"})),
            None
        );
    }
}
