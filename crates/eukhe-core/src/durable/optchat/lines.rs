//! What one committed entry adds to the chat log (spec §1, §6), and what
//! each entry is to a call's request. The user's words, the agent's
//! replies and tool calls, and tool results are logged; reports and
//! background events that reach the model are logged as `work` messages
//! starting with one `[id] `; harness nudges (autonomous and goal
//! continuations: not the user's words) and harness state the next turn
//! re-derives (kernel notices, bookkeeping rows, summaries) are not.
//! Thinking is never logged. A tool result is clipped to its head and
//! tail; any other text longer than [`crate::memory::CAP`] characters is
//! logged as several messages in a row, never cut. Images ride with their
//! message (its first piece), so `zoom(id, 1)` gives them back (§5).

use eukhe_durable::entries::{UserData, ASSISTANT_ENTRY, TOOL_RESULT_ENTRY, USER_ENTRY};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::{EntryData, EntryRecord};
use eukhe_types::input_origin::{InputOrigin, Report};
use eukhe_types::pi_ai::{
    AssistantContentBlock, ImageContent, Message, UserContent, UserContentBlock,
};

use crate::durable::entries::{is_input_entry, CustomEntryData, BASH_ENTRY, CUSTOM_ENTRY};
use crate::memory::{cap_text, labeled, split_text, Kind};

/// One message for the chat log.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LogLine {
    pub kind: Kind,
    pub text: String,
    /// The images the message carried, `[image: mime]` in its text.
    pub images: Vec<ImageContent>,
}

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
    if is_input_entry(entry) || entry.kind == BASH_ENTRY.kind() {
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

/// The chat log lines of one committed entry, in order: a long text is
/// split over several lines of the same kind, the first carrying the
/// entry's images.
///
/// # Errors
///
/// A `pi.user` entry whose origin does not decode, or a report whose text
/// does not start with its header.
pub(crate) fn entry_lines(entry: &EntryRecord) -> SessionResult<Vec<LogLine>> {
    let mut lines = Vec::new();
    for (kind, text, images) in whole_lines(entry)? {
        let mut images = Some(images);
        for piece in split_text(&text) {
            lines.push(LogLine {
                kind,
                text: piece,
                images: images.take().unwrap_or_default(),
            });
        }
    }
    Ok(lines)
}

/// A chat as `zoom("Name")` gives it: each of its entries' log lines as
/// `kind: text`, one after the other.
///
/// # Errors
///
/// As [`entry_lines`].
pub(crate) fn chat_text(entries: &[EntryRecord]) -> SessionResult<String> {
    let mut lines = Vec::new();
    for entry in entries {
        for (kind, text, _) in whole_lines(entry)? {
            lines.push(labeled(kind, &text));
        }
    }
    Ok(lines.join("\n"))
}

/// One message of an entry before long texts are split: kind, text, and
/// images.
type WholeLine = (Kind, String, Vec<ImageContent>);

/// The lines of one entry before long texts are split.
fn whole_lines(entry: &EntryRecord) -> SessionResult<Vec<WholeLine>> {
    let messages = entry.model.as_deref().unwrap_or_default();
    if is_input_entry(entry) {
        let origin = input_origin(entry)?;
        let mut lines = Vec::new();
        for message in messages {
            if let Some(line) = user_input_line(message, &origin)? {
                lines.push(line);
            }
        }
        return Ok(lines);
    }
    if entry.kind == ASSISTANT_ENTRY.kind() {
        return Ok(messages.iter().flat_map(assistant_lines).collect());
    }
    if entry.kind == TOOL_RESULT_ENTRY.kind() {
        return Ok(messages.iter().filter_map(tool_result_line).collect());
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
            return Ok(Vec::new());
        }
        let custom_type = custom_type(entry);
        return Ok(match classify_custom(&custom_type) {
            CustomRow::Report => vec![(
                Kind::Work,
                custom_report_line(entry, &custom_type, &text),
                Vec::new(),
            )],
            CustomRow::Nudge | CustomRow::State => Vec::new(),
        });
    }
    if entry.kind == BASH_ENTRY.kind() {
        return Ok(bash_line(entry).into_iter().collect());
    }
    // `pi.system`, `pi.reset`, `pi.compaction`, branch and compaction
    // summaries, custom state: the harness's own rows and rewrites of
    // history already in the log.
    Ok(Vec::new())
}

/// Who produced a placed input: a `pi.user` entry's origin, or an input
/// entry's `data.origin` (the user's when absent, as `pi.user` reads).
fn input_origin(entry: &EntryRecord) -> SessionResult<InputOrigin> {
    if entry.kind == USER_ENTRY.kind() {
        return Ok(UserData::decode(entry.data.as_ref())?.origin);
    }
    let data = CustomEntryData::decode(entry.data.as_ref())?;
    Ok(data.origin.unwrap_or(InputOrigin::User))
}

/// A user input by its origin: the user's words with their images, or a
/// report normalized to its `[id] ` line; harness nudges are not logged.
fn user_input_line(message: &Message, origin: &InputOrigin) -> SessionResult<Option<WholeLine>> {
    let Message::User(user) = message else {
        return Ok(None);
    };
    let text = user_text(&user.content);
    if text.trim().is_empty() {
        return Ok(None);
    }
    Ok(match origin {
        InputOrigin::User => Some((Kind::User, text, user_images(&user.content))),
        InputOrigin::Goal { .. }
        | InputOrigin::Autonomous { .. }
        | InputOrigin::Director
        | InputOrigin::QuotaResume => None,
        InputOrigin::Report { report } => {
            let body = report.body(&text).map_err(SessionError::other)?;
            Some((Kind::Work, report_line(report, body), Vec::new()))
        }
    })
}

fn assistant_lines(message: &Message) -> Vec<WholeLine> {
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
                    entries.push((Kind::Eukhe, std::mem::take(&mut talk), Vec::new()));
                }
                talk.clear();
                let arguments = serde_json::Value::Object(call.arguments.clone());
                entries.push((Kind::Tool, format!("{} {arguments}", call.name), Vec::new()));
            }
            AssistantContentBlock::Thinking(_) => {}
        }
    }
    if !talk.trim().is_empty() {
        entries.push((Kind::Eukhe, talk, Vec::new()));
    }
    entries
}

/// A tool result, clipped, with the images it returned.
fn tool_result_line(message: &Message) -> Option<WholeLine> {
    let Message::ToolResult(result) = message else {
        return None;
    };
    Some((
        Kind::Echo,
        cap_text(&blocks_text(&result.content)),
        blocks_images(&result.content),
    ))
}

/// The user's own `!command`: what it ran and printed.
fn bash_line(entry: &EntryRecord) -> Option<WholeLine> {
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
    Some((
        Kind::User,
        cap_text(&format!("Ran `{command}`\n{output}")),
        Vec::new(),
    ))
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
        | "anthropic_subscription_warning_shown"
        | crate::agent_messaging::AGENT_REPLY_OWED_CUSTOM_TYPE
        | crate::durable::settings::SETTINGS_ERROR_CUSTOM_TYPE => CustomRow::State,
        _ => CustomRow::Report,
    }
}

/// A report's log line: ONE leading `[id] `, then the headline and the
/// body (§6: "[Name] report"), so the compactor and the view tag it
/// `work`. The delivered input keeps its own header (`[agent-message from
/// child:x]\n\nbody` and the like); the log holds `[child:x] body`.
fn report_line(report: &Report, body: &str) -> String {
    let (id, headline) = match report {
        Report::AgentMessage { sender } => (sender.clone(), String::new()),
        Report::ChildExited { child, exit } => (
            format!("child:{child}"),
            format!("exited ({})", exit.label()),
        ),
        Report::ChildFailed {
            child,
            failure: Some(failure),
        } => (format!("child:{child}"), format!("failed ({failure})")),
        Report::ChildFailed {
            child,
            failure: None,
        } => (format!("child:{child}"), "failed".to_owned()),
        Report::Heartbeat { schedule, run } => {
            ("heartbeat".to_owned(), format!("{schedule} run#{run}"))
        }
        Report::BashDone {
            pid,
            exit_code,
            stopped_by: None,
        } => (
            "bash".to_owned(),
            format!("done pid:{pid} exit:{exit_code}"),
        ),
        Report::BashDone {
            pid,
            exit_code,
            stopped_by: Some(stopper),
        } => (
            "bash".to_owned(),
            format!("stopped by {} pid:{pid} exit:{exit_code}", stopper.label()),
        ),
        Report::JobSettled { job, status } => (
            format!("job:{job}"),
            format!("settled ({})", status.label()),
        ),
    };
    let mut line = format!("[{id}] {headline}");
    if !body.is_empty() {
        if !headline.is_empty() {
            line.push('\n');
        }
        line.push_str(body);
    }
    line
}

/// A custom report row's log line: an agent's answer as `[name] answer`
/// from its details, any other report as `[custom_type] text`.
fn custom_report_line(entry: &EntryRecord, custom_type: &str, text: &str) -> String {
    let details = entry
        .data
        .as_ref()
        .map(serde_json::Value::from)
        .and_then(|data| data.get("details").cloned());
    let reply = details.as_ref().and_then(|details| {
        Some((
            details.get("from")?.as_str()?,
            details.get("message")?.as_str()?,
        ))
    });
    match reply {
        Some((from, message)) if custom_type == crate::agent_messaging::AGENT_REPLY_CUSTOM_TYPE => {
            format!(
                "[{}] {message}",
                crate::agent_messaging::sanitize_message_header_value(from)
            )
        }
        Some(_) | None => format!("[{custom_type}] {text}"),
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

/// The images of user content, in order (none for plain text).
pub(crate) fn user_images(content: &UserContent) -> Vec<ImageContent> {
    match content {
        UserContent::Text(_) => Vec::new(),
        UserContent::Blocks(blocks) => blocks_images(blocks),
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

/// The image blocks among `blocks`, in order.
fn blocks_images(blocks: &[UserContentBlock]) -> Vec<ImageContent> {
    blocks
        .iter()
        .filter_map(|block| match block {
            UserContentBlock::Image(image) => Some(image.clone()),
            UserContentBlock::Text(_) => None,
        })
        .collect()
}
