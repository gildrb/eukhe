//! What one committed entry adds to the chat log (`OptChat` §9), and what
//! each entry is to a call's request (§7). The user's words, the agent's
//! replies and tool calls, and tool results are logged; reports and
//! background events that reach the model are logged as `user` messages
//! starting with one `[id] `; harness nudges (autonomous and goal
//! continuations: not the user's words) and harness state the next turn
//! re-derives (kernel notices, bookkeeping rows, summaries) are not.
//! Thinking is never logged (§2).

use eukhe_durable::entries::{ASSISTANT_ENTRY, TOOL_RESULT_ENTRY, USER_ENTRY};
use eukhe_durable::types::EntryRecord;
use eukhe_types::pi_ai::{AssistantContentBlock, Message, UserContent, UserContentBlock};

use crate::durable::entries::{BASH_ENTRY, CUSTOM_ENTRY};
use crate::memory::{cap_text, Kind};

/// What an entry's model messages are to the first message of a call.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Lead {
    /// Joins the user's texts in the call's first message: the user's
    /// words, reports, nudges, the user's `!` runs.
    Joins,
    /// Harness state or a summary: rides right after the call's first
    /// message.
    State,
}

/// How a leading entry of a call enters its first message.
pub(crate) fn lead_of(entry: &EntryRecord) -> Lead {
    if entry.kind == USER_ENTRY.kind() || entry.kind == BASH_ENTRY.kind() {
        return Lead::Joins;
    }
    if entry.kind == CUSTOM_ENTRY.kind() {
        return match classify_custom(&custom_type(entry)) {
            CustomRow::Report | CustomRow::Nudge => Lead::Joins,
            CustomRow::State => Lead::State,
        };
    }
    Lead::State
}

/// The chat log lines of one committed entry, in order.
pub(crate) fn entry_lines(entry: &EntryRecord) -> Vec<(Kind, String)> {
    let messages = entry.model.as_deref().unwrap_or_default();
    if entry.kind == USER_ENTRY.kind() {
        return messages.iter().filter_map(user_input_line).collect();
    }
    if entry.kind == ASSISTANT_ENTRY.kind() {
        return messages.iter().flat_map(assistant_lines).collect();
    }
    if entry.kind == TOOL_RESULT_ENTRY.kind() {
        return messages.iter().filter_map(tool_result_line).collect();
    }
    if entry.kind == CUSTOM_ENTRY.kind() {
        let text = messages
            .iter()
            .filter_map(|message| match message {
                Message::User(user) => Some(user_text(&user.content)),
                Message::System(_) | Message::Assistant(_) | Message::ToolResult(_) => None,
            })
            .collect::<Vec<_>>()
            .join("\n");
        if text.trim().is_empty() {
            return Vec::new();
        }
        let custom_type = custom_type(entry);
        return match classify_custom(&custom_type) {
            CustomRow::Report => vec![(Kind::User, report_line(&custom_type, &text))],
            CustomRow::Nudge | CustomRow::State => Vec::new(),
        };
    }
    if entry.kind == BASH_ENTRY.kind() {
        return bash_line(entry).into_iter().collect();
    }
    // `pi.system`, `pi.reset`, `pi.compaction`, branch and compaction
    // summaries, custom state: the harness's own rows and rewrites of
    // history already in the log.
    Vec::new()
}

/// A user input: the user's words, or a report delivered as input (a
/// child's notice) normalized to its `[id] ` line; harness nudges are not
/// logged.
fn user_input_line(message: &Message) -> Option<(Kind, String)> {
    let Message::User(user) = message else {
        return None;
    };
    let text = user_text(&user.content);
    if text.trim().is_empty()
        || crate::autonomous::is_autonomous_continuation(&text)
        || crate::durable::goals::is_goal_nudge(&text)
    {
        return None;
    }
    let report = REPORT_HEADERS
        .iter()
        .find(|(header, _)| text.starts_with(header))
        .and_then(|(_, custom_type)| normalized_report(custom_type, &text));
    Some((Kind::User, report.unwrap_or(text)))
}

fn assistant_lines(message: &Message) -> Vec<(Kind, String)> {
    let Message::Assistant(assistant) = message else {
        return Vec::new();
    };
    let mut entries = Vec::new();
    let mut talk = String::new();
    for block in &assistant.content {
        match block {
            AssistantContentBlock::Text(text) => {
                if !talk.is_empty() && !text.text.is_empty() {
                    talk.push('\n');
                }
                talk.push_str(&text.text);
            }
            AssistantContentBlock::ToolCall(call) => {
                if !talk.trim().is_empty() {
                    entries.push((Kind::Talk, std::mem::take(&mut talk)));
                }
                talk.clear();
                let arguments = serde_json::Value::Object(call.arguments.clone());
                entries.push((Kind::Tool, format!("{} {arguments}", call.name)));
            }
            AssistantContentBlock::Thinking(_) => {}
        }
    }
    if !talk.trim().is_empty() {
        entries.push((Kind::Talk, talk));
    }
    entries
}

fn tool_result_line(message: &Message) -> Option<(Kind, String)> {
    let Message::ToolResult(result) = message else {
        return None;
    };
    Some((Kind::Echo, cap_text(&blocks_text(&result.content))))
}

/// The user's own `!command`: what it ran and printed.
fn bash_line(entry: &EntryRecord) -> Option<(Kind, String)> {
    let data = entry.data.as_ref().map(serde_json::Value::from)?;
    if data
        .get("excludeFromContext")
        .and_then(serde_json::Value::as_bool)
        .unwrap_or(false)
    {
        return None;
    }
    let field = |name: &str| {
        data.get(name)
            .and_then(serde_json::Value::as_str)
            .unwrap_or("")
            .to_string()
    };
    let (command, output) = (field("command"), field("output"));
    Some((Kind::User, cap_text(&format!("Ran `{command}`\n{output}"))))
}

fn custom_type(entry: &EntryRecord) -> String {
    entry
        .data
        .as_ref()
        .map(serde_json::Value::from)
        .and_then(|data| {
            data.get("customType")
                .and_then(serde_json::Value::as_str)
                .map(str::to_string)
        })
        .unwrap_or_default()
}

/// What a session `custom` row is to the chat.
enum CustomRow {
    /// A report or a background event: logged as `[id] ...` and delivered
    /// with the user's texts.
    Report,
    /// A harness nudge (a goal continuation): delivered with the user's
    /// texts, never logged (not the user's words).
    Nudge,
    /// Harness state and bookkeeping: re-derived every turn, or never
    /// model context; never logged, never among the user's texts.
    State,
}

fn classify_custom(custom_type: &str) -> CustomRow {
    match custom_type {
        "goal_context" | "autonomous_status" => CustomRow::Nudge,
        "harness_digest"
        | "ipython_state"
        | "ipython_state_restored"
        | "python_skills_unavailable"
        | "thread_goal_state"
        | "refinement_notice"
        | "refinement_outcome"
        | "compaction_outcome"
        | "provider_retry_outcome"
        | "model_prompt_error"
        | "session_slash_command"
        | "session_slash_command_result"
        | "anthropic_subscription_warning_shown" => CustomRow::State,
        _ => CustomRow::Report,
    }
}

/// The headers of reports that arrive as plain user input (a child's
/// terminal notice, a forwarded message), with the custom type whose
/// normalization they take.
const REPORT_HEADERS: [(&str, &str); 5] = [
    ("[agent-message from ", "agent_message"),
    ("[child-exited: ", "rlm_child_terminal_notice"),
    ("[child-failed ", "rlm_child_failure"),
    ("[heartbeat: ", "heartbeat_prompt"),
    ("[bash-", "async_bash_completion"),
];

/// A report's log line: ONE leading `[id] `, then the report (§9), so the
/// compactor and the view tag it `work`. The delivered row keeps its own
/// header (`[agent-message from child:x]\n\nbody` and the like); the log
/// holds `[child:x] body`.
pub(crate) fn report_line(custom_type: &str, text: &str) -> String {
    normalized_report(custom_type, text).unwrap_or_else(|| format!("[{custom_type}] {text}"))
}

/// The `[id] headline\nbody` form of a report whose header `custom_type`
/// knows; `None` for other headers.
fn normalized_report(custom_type: &str, text: &str) -> Option<String> {
    let (header, body) = text.strip_prefix('[').and_then(|rest| {
        let end = rest.find(']')?;
        Some((&rest[..end], rest[end + 1..].trim_start_matches('\n')))
    })?;
    // `[id] headline`, the body on its own line after a headline.
    let line = |id: &str, headline: &str| {
        let mut line = format!("[{id}] {headline}");
        if !body.is_empty() {
            if !headline.is_empty() {
                line.push('\n');
            }
            line.push_str(body);
        }
        line
    };
    match custom_type {
        "agent_message" => header
            .strip_prefix("agent-message from ")
            .map(|sender| line(sender, "")),
        "rlm_child_terminal_notice" => header
            .strip_prefix("child-exited: ")
            .and_then(|rest| rest.split_once(' '))
            .map(|(how, child)| line(child, &format!("exited ({how})"))),
        "rlm_child_failure" => header
            .strip_prefix("child-failed ")
            .map(|child| line(child, "failed")),
        "heartbeat_prompt" => header
            .strip_prefix("heartbeat: ")
            .map(|run| line("heartbeat", run)),
        "async_bash_completion" => header.strip_prefix("bash-").map(|done| line("bash", done)),
        _ => None,
    }
}

/// The text of user content: text blocks, images as `[image: mime]`, one
/// per line.
pub(crate) fn user_text(content: &UserContent) -> String {
    match content {
        UserContent::Text(text) => text.clone(),
        UserContent::Blocks(blocks) => blocks_text(blocks),
    }
}

fn blocks_text(blocks: &[UserContentBlock]) -> String {
    blocks
        .iter()
        .map(|block| match block {
            UserContentBlock::Text(text) => text.text.clone(),
            UserContentBlock::Image(image) => format!("[image: {}]", image.mime_type),
        })
        .collect::<Vec<_>>()
        .join("\n")
}
