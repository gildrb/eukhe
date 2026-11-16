//! Whether a headless run acted, the fact the headless task rule reads
//! before it asks the judge (`bend/headless_task.bend`): a tool call with an
//! effect since the run began (an edit, a write, a program run, a spawned
//! child: every tool but the read-only ones, and a `bash` call any of whose
//! steps has an effect other than reading), or a goal opened.

use eukhe_bend::rules::headless::Activity;
use eukhe_chord::context::Context;
use eukhe_durable::harness::{Conversation, ConversationEntryQuery};
use eukhe_durable::session::SessionError;
use eukhe_durable::types::EntryId;
use eukhe_types::goal::{GoalState, GoalStatus};
use eukhe_types::pi_ai::{Message, ToolResultMessage};

/// The transcript read's page size.
const PAGE: usize = 64;

/// The tools that only read: the documents' read tools and the chat
/// memory's.
const READ_TOOLS: [&str; 5] = ["read", "grep", "glob", "zoom", "date"];

/// The newest entry of `conversation` before the run: the run's entries
/// are the ones after it.
pub(super) async fn newest_entry(
    conversation: &Conversation,
    cx: &Context,
) -> Result<Option<EntryId>, SessionError> {
    let page = conversation
        .entries(ConversationEntryQuery::default(), 1, None, cx)
        .await?;
    Ok(page.items.first().map(|entry| entry.id))
}

/// Whether the run acted: its goal opened, or a tool result newer than
/// `since` (none: the whole transcript) from a call with an effect.
pub(super) async fn run_activity(
    conversation: &Conversation,
    since: Option<EntryId>,
    goal: &GoalState,
    cx: &Context,
) -> Result<Activity, SessionError> {
    if goal_opened(goal) {
        return Ok(Activity::Acted);
    }
    let mut cursor = None;
    loop {
        let page = conversation
            .entries(ConversationEntryQuery::default(), PAGE, cursor, cx)
            .await?;
        for entry in page.items {
            if Some(entry.id) == since {
                return Ok(Activity::ReadOnly);
            }
            let acted = entry.model.iter().flatten().any(|message| match message {
                Message::ToolResult(result) => tool_acted(result),
                Message::System(_) | Message::User(_) | Message::Assistant(_) => false,
            });
            if acted {
                return Ok(Activity::Acted);
            }
        }
        match page.next {
            Some(next) => cursor = Some(next),
            None => return Ok(Activity::ReadOnly),
        }
    }
}

/// Whether the run has a goal (any but none).
fn goal_opened(goal: &GoalState) -> bool {
    goal.objective.is_some()
        && match goal.status {
            GoalStatus::Idle => false,
            GoalStatus::Active
            | GoalStatus::Paused
            | GoalStatus::BudgetLimited
            | GoalStatus::Complete
            | GoalStatus::Error => true,
        }
}

/// Whether the call behind `result` had an effect: every tool but the
/// read-only ones; a `bash` call when a step has an effect other than
/// reading, or when its steps are not recorded.
pub(super) fn tool_acted(result: &ToolResultMessage) -> bool {
    match result.tool_name.as_str() {
        name if READ_TOOLS.contains(&name) => false,
        "bash" => result
            .details
            .as_ref()
            .and_then(|details| details.get("steps"))
            .and_then(serde_json::Value::as_array)
            .is_none_or(|steps| {
                steps.iter().any(|step| {
                    step.get("effects")
                        .and_then(serde_json::Value::as_array)
                        .is_none_or(|effects| {
                            effects.iter().any(|effect| effect.as_str() != Some("read"))
                        })
                })
            }),
        _ => true,
    }
}
