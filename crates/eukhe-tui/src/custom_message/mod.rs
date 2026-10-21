//! Custom-message chat rows: the decorated transcript surfaces for
//! `role: "custom"` wire messages (TS `agent-message.ts`,
//! `injected-prompt-message.ts`, `compaction-outcome-message.ts`,
//! `refinement-outcome-message.ts`, `shell-completion.ts`, and the generic
//! `custom-message.ts` panel) plus the user-message skill-invocation card
//! (TS `skill-invocation-message.ts`, parsed out of a user message's
//! `<skill>` block). Decode maps every custom type to the component
//! the TS dispatch (`createDisplayedCustomMessageComponent` /
//! `buildConversationComponents`) picks; rendering ports each component's
//! row geometry and theme colors.
//!
//! Rendering lives in the sibling modules (`render` for most components,
//! `injected_prompt` for the injected-prompt rows, `refinement` for the
//! refinement-outcome component).
//!
//! The dispatch follows the TS live path
//! (`createDisplayedCustomMessageComponent`): non-display rows render
//! nothing, every displayed type without a dedicated component (engine
//! bookkeeping like `harness_digest`, unknown types) renders the generic
//! `[<customType>]` panel. (The TS replay path `buildConversationComponents`
//! drops unknown types instead; the live interactive path is the TUI ground
//! truth, and the Rust engine persists those types with `display: false`.)
//!
//! Divergence (the operator's 2026-10-01 directive: "the factory child
//! status notices should be like subagent messages not user messages"): the
//! RLM child status notices (`rlm_child_terminal_notice` /
//! `rlm_child_failure`) render in the `agent_message` component's class --
//! child-originated mail, attributed to the exited subagent -- where the TS
//! dispatch classes them as injected-prompt rows (turn prompts). The
//! notices still drive their turn (the daemon's `followUp` notice action is
//! unchanged); only the transcript row's class moves.

pub(crate) mod injected_prompt;
pub(crate) mod refinement;
pub(crate) mod render;
pub mod skill_invocation;

pub use skill_invocation::{skill_invocation_entries, SkillInvocationRow};

use injected_prompt::injected_prompt_row;
pub use injected_prompt::{InjectedPromptKind, InjectedPromptRow};

use crate::chat::{ChatEntry, StatusKind};
use crate::theme::ThemeColor;
use eukhe_types::ai::{UserContent, UserContentBlock};
use eukhe_types::custom_type::CustomType;
use serde_json::Value;

// ---------------------------------------------------------------------------
// Row payloads (carried by ChatEntry variants)
// ---------------------------------------------------------------------------

/// Which agent-message side a row renders: the received notice of the
/// transcript custom-message rows (TS `AgentMessageComponent`), or the
/// sent/queued receipts of the ipython cell output (TS
/// `renderSentAgentMessages`). The variants carry no label of their own:
/// the operator's 2026-09-25 arrow directive folds the direction word into
/// the viewer-relative arrow (received `down`, sent/queued `up`) that renders
/// next to the shared `AGENT_MESSAGE_LABEL`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AgentMessageDirection {
    /// The transcript custom-message rows (this chat received the mail).
    Received,
    /// A delivered receipt in ipython cell output.
    Sent,
    /// An undelivered receipt in ipython cell output.
    Queued,
}

/// The summary-line label (the operator's 2026-09-25 arrow directive: the
/// `received`/`sent`/`queued` word folds into the viewer-relative arrow,
/// so every direction carries the same label).
pub(crate) const AGENT_MESSAGE_LABEL: &str = "Agent message";

/// One agent-message summary row:
/// `mail Agent message * <arrow> <counterpart>` plus the guttered body when
/// expanded (TS `AgentMessageComponent` for received rows; the sent/queued
/// directions feed the ipython cell receipt rows). The `mail` mail envelope
/// is the row's icon -- a sanctioned divergence (Kevin directive 2026-09-24)
/// from the TS `*` diamond; the TS side is expected to adopt the same
/// glyph. The collapsed row carries no body preview (the operator's
/// 2026-09-25 directive: display only `Agent message`, the viewer-relative
/// arrow, and the counterpart agent's name).
#[derive(Debug, Clone, PartialEq)]
pub struct AgentMessageRow {
    /// Which side renders: it drives the viewer-relative arrow (`up`
    /// sent/queued, `down` received).
    pub direction: AgentMessageDirection,
    /// The counterpart agent's display name (session name, then the id
    /// fallbacks, then `unknown`): the other end of the mail the row
    /// summarizes. The `to`/`from` word and the relationship word fold
    /// into the arrow and never render (the operator's 2026-09-25
    /// directive).
    pub counterpart: String,
    /// `details.message` (the body shown expanded; never a collapsed
    /// preview).
    pub message: String,
}

/// One background-shell completion row (TS `ShellCompletionComponent`,
/// standalone form: the completion attaches to a tool card only in the TS
/// live path, which the Rust engine does not emit).
#[derive(Debug, Clone, PartialEq)]
pub struct ShellCompletionRow {
    pub pid: Option<i64>,
    pub exit_code: Option<i64>,
    /// Raw content (`[bash-done pid:N exit:M] ...`).
    pub content: String,
}

/// One refinement outcome row (TS `RefinementOutcomeMessageComponent`).
#[derive(Debug, Clone, PartialEq)]
pub struct RefinementOutcomeRow {
    /// `* <header>` (`Harness refined` or the full outcome line).
    pub header: String,
    /// Summary text (collapsed: two-line clamp).
    pub summary: String,
    /// `<outcome> * Refinement <id> * <scope>[ * rollback of <id>]` (dim).
    pub meta: String,
    pub edits: Vec<RefinementEditRow>,
}

/// One applied-edit section of a refinement outcome.
#[derive(Debug, Clone, PartialEq)]
pub struct RefinementEditRow {
    /// Label spans: the verb (or the whole failed line) carries its color.
    pub label: Vec<LabelPart>,
    pub reason: Option<String>,
    /// Expanded detail fields (label + plain value or removed/added change).
    pub fields: Vec<EditField>,
}

/// One label span: text plus an optional theme color.
#[derive(Debug, Clone, PartialEq)]
pub struct LabelPart {
    pub text: String,
    pub color: Option<ThemeColor>,
}

/// One edit field (TS `EditFieldRows`): plain value rows or a -/+ change.
#[derive(Debug, Clone, PartialEq)]
pub struct EditField {
    pub label: String,
    pub value: Vec<String>,
    pub change: Option<(Vec<String>, Vec<String>)>,
}

/// One generic custom row (TS `CustomMessageComponent`, after #2779's one
/// shared layout): the bold `[<customType>]` label header with the
/// guttered markdown body in `customMessageText`. Every display-true
/// custom type without a dedicated component renders this way (e.g.
/// `autonomous_status`).
#[derive(Debug, Clone, PartialEq)]
pub struct CustomPanelRow {
    pub custom_type: String,
    pub content: String,
}

// ---------------------------------------------------------------------------
// Decode
// ---------------------------------------------------------------------------

/// The transcript entries for one `custom`-role message, mirroring the TS
/// dispatch order: slash rows, compaction and refinement outcomes, agent
/// messages (the received agent-message rows and the RLM child status
/// notices, the same class), shell completions, injected prompts, then the
/// generic panel. Non-display rows render nothing.
#[must_use]
pub fn custom_message_entries(
    custom_type: &CustomType,
    content: &UserContent,
    display: bool,
    details: Option<&Value>,
) -> Vec<ChatEntry> {
    if !display {
        return Vec::new();
    }
    let text = crate::snapshot::content_text(content);
    let details = details.unwrap_or(&Value::Null);
    match custom_type {
        CustomType::SessionSlashCommand => slash_row_entries(content, true, &text, details),
        CustomType::SessionSlashCommandResult => slash_row_entries(content, false, &text, details),
        CustomType::CompactionOutcome => vec![compaction_outcome_entry(content, details)],
        CustomType::ProviderRetryOutcome => {
            // The ONE line a retry episode leaves in the chat: the row text
            // the daemon carried (the live rows use the same text), the
            // tone from the structured verdict. A failed episode ended its
            // turn without an answer, so its row names the next step.
            if details.get("success").and_then(Value::as_bool) == Some(true) {
                vec![ChatEntry::Status {
                    text,
                    kind: crate::chat::StatusKind::Info,
                }]
            } else {
                let text = match crate::error_summary::failure_next_step(&text) {
                    Some(step) => format!("{text}{}{step}", crate::glyphs::SEP),
                    None => text,
                };
                vec![ChatEntry::Status {
                    text,
                    kind: crate::chat::StatusKind::Error,
                }]
            }
        }
        CustomType::ModelPromptError => vec![ChatEntry::Status {
            text,
            kind: crate::chat::StatusKind::Warning,
        }],
        CustomType::RefinementOutcome => refinement::refinement_outcome_entries(content, details),
        CustomType::AgentMessage => agent_message_entry(details).map_or_else(
            || vec![generic_panel_entry(custom_type, content)],
            |entry| vec![entry],
        ),
        // An agent's answer to the user's `@name` message: the
        // `name -> you` family row (first line; full text at Detail::All).
        CustomType::AgentReply => {
            let field = |key: &str| details.get(key).and_then(Value::as_str);
            match (field("from"), field("message")) {
                (Some(from), Some(text)) => vec![ChatEntry::Swarm(Box::new(
                    crate::swarm_block::SwarmRow::Relay(eukhe_types::daemon::AgentRelayEvent {
                        from: from.to_string(),
                        to: "you".to_string(),
                        text: text.to_string(),
                    }),
                ))],
                (None, _) | (_, None) => vec![generic_panel_entry(custom_type, content)],
            }
        }
        CustomType::AsyncBashCompletion => vec![ChatEntry::ShellCompletion(Box::new(
            shell_completion_row(content, details),
        ))],
        CustomType::HeartbeatPrompt
        | CustomType::GoalContext
        | CustomType::IpythonStateRestored
        | CustomType::PythonSkillsUnavailable => injected_prompt_row(custom_type, content, details)
            .map(|row| ChatEntry::InjectedPrompt(Box::new(row)))
            .into_iter()
            .collect(),
        // The RLM child status notices are child-originated mail -- the
        // spawned subagent's exit status (a factory's children included) --
        // so they render in the same quiet, counterpart-attributed
        // `Agent message` class the children's own `agent_message` rows
        // use (the operator's 2026-10-01 directive: "the factory child
        // status notices should be like subagent messages not user
        // messages"), not as turn-prompt rows. The notice text rides as
        // the row body, so nothing is lost.
        CustomType::RlmChildFailure | CustomType::RlmChildTerminalNotice => {
            vec![ChatEntry::AgentMessage(Box::new(rlm_child_status_row(
                content, details,
            )))]
        }
        // Everything else - engine bookkeeping (`harness_digest`,
        // `refinement_notice`, worker recovery) and unknown types - renders
        // the generic panel, exactly like the TS live dispatch fallthrough
        // (those types persist with `display: false` and render nothing).
        CustomType::Other(_) => vec![generic_panel_entry(custom_type, content)],
    }
}

/// TS `CustomMessageComponent` fallthrough: the `[<customType>]` guttered
/// panel row.
fn generic_panel_entry(custom_type: &CustomType, content: &UserContent) -> ChatEntry {
    ChatEntry::CustomPanel(Box::new(CustomPanelRow {
        custom_type: custom_type.as_str().to_string(),
        content: custom_content_text(content),
    }))
}

/// The session-command echo/result rows: the echo decodes to the
/// user-block slash row (the typed command IS user input); the result
/// row decodes to the status-row class with the severity's tone.
fn slash_row_entries(
    content: &UserContent,
    is_command_row: bool,
    text: &str,
    details: &Value,
) -> Vec<ChatEntry> {
    let content_is_text = match content {
        UserContent::Text(_) => true,
        UserContent::Blocks(blocks) => match blocks.as_slice() {
            [UserContentBlock::Text(_)] => true,
            [UserContentBlock::Raw(raw)] => raw.get("type").is_none(),
            [] | [UserContentBlock::Image(_)] | [_, _, ..] => false,
        },
    };
    let command_details_valid = details.get("command").is_some_and(|command| {
        command.get("name").is_some()
            && command.get("args").is_some()
            && command.get("text").is_some()
    });
    if !content_is_text || (is_command_row && !command_details_valid) {
        return vec![ChatEntry::User {
            text: "[Malformed session command message]".to_string(),
        }];
    }
    if is_command_row {
        vec![ChatEntry::SlashCommand {
            text: text.to_string(),
        }]
    } else {
        // The outcome row is system output, never user text (the
        // operator's 2026-09-25 bug report: the user-message box read as
        // the "no active goal" reply being a user prompt): it renders in
        // the status-row class, the severity driving the tone like the
        // compaction and retry outcome rows.
        let kind = match details.get("severity").and_then(Value::as_str) {
            Some("error") => StatusKind::Error,
            Some("warning") => StatusKind::Warning,
            _ => StatusKind::Info,
        };
        vec![ChatEntry::Status {
            text: text.to_string(),
            kind,
        }]
    }
}

/// TS `isCompactionOutcomeMessage` envelope: content string + a known
/// reason/outcome pair; anything else is the malformed notice.
fn compaction_outcome_entry(content: &UserContent, details: &Value) -> ChatEntry {
    let valid = matches!(content, UserContent::Text(_))
        && matches!(
            details.get("reason").and_then(Value::as_str),
            Some("threshold" | "overflow" | "requested")
        )
        && matches!(
            details.get("outcome").and_then(Value::as_str),
            Some("skipped" | "cancelled" | "failed")
        );
    if !valid {
        return ChatEntry::Status {
            text: "[Malformed compaction outcome message]".to_string(),
            kind: StatusKind::Error,
        };
    }
    let outcome = details
        .get("outcome")
        .and_then(Value::as_str)
        .unwrap_or("failed");
    ChatEntry::Status {
        text: crate::snapshot::content_text(content),
        kind: if outcome == "skipped" {
            StatusKind::Warning
        } else {
            StatusKind::Error
        },
    }
}

/// TS `isAgentSessionMessage`: string `details.id` + string
/// `details.message` (no emptiness check); anything else is not an
/// agent-message row and the dispatch falls through to the generic box.
fn agent_message_entry(details: &Value) -> Option<ChatEntry> {
    details.get("id").and_then(Value::as_str)?;
    let message = details.get("message").and_then(Value::as_str)?;
    let from = details.get("from").unwrap_or(&Value::Null);
    let counterpart = ["sessionName", "activeSessionId", "clientId", "sessionId"]
        .iter()
        .find_map(|key| {
            from.get(*key)
                .and_then(Value::as_str)
                .map(str::to_string)
                .filter(|name| !name.trim().is_empty())
        })
        .unwrap_or_else(|| "unknown".to_string());
    Some(ChatEntry::AgentMessage(Box::new(AgentMessageRow {
        direction: AgentMessageDirection::Received,
        counterpart,
        message: message.to_string(),
    })))
}

/// One RLM child status notice (`rlm_child_terminal_notice` /
/// `rlm_child_failure`) as the subagent-mail row: the child that exited is
/// the mail's counterpart, the notice text is the body (the full content,
/// header included, so the outcome wording rides intact).
fn rlm_child_status_row(content: &UserContent, details: &Value) -> AgentMessageRow {
    let text = custom_content_text(content);
    AgentMessageRow {
        direction: AgentMessageDirection::Received,
        counterpart: rlm_child_session_name(details),
        message: text,
    }
}

/// The child's session name: the `sessionName` details key, else the
/// agent-message row's `unknown`.
fn rlm_child_session_name(details: &Value) -> String {
    details
        .get("sessionName")
        .and_then(Value::as_str)
        .filter(|name| !name.is_empty())
        .map_or_else(|| "unknown".to_string(), str::to_string)
}

/// TS `readShellCompletion` + `ShellCompletionComponent.render`: a valid
/// completion needs an object details block with a positive-integer `pid`,
/// a string `command`, and an integer `exitCode`; anything else renders the
/// default finished row. The expanded raw text follows the same validity:
/// `shellCompletionText` for a valid completion (content string or text
/// blocks joined with newlines, images as `[image]`), the content string or
/// its JSON form otherwise.
fn shell_completion_row(content: &UserContent, details: &Value) -> ShellCompletionRow {
    let pid = details.get("pid").and_then(Value::as_i64);
    let command = details.get("command").and_then(Value::as_str);
    let exit_code = details.get("exitCode").and_then(Value::as_i64);
    let valid = details.is_object()
        && pid.is_some_and(|pid| pid > 0)
        && command.is_some()
        && exit_code.is_some();
    if valid {
        ShellCompletionRow {
            pid,
            exit_code,
            content: custom_content_text(content),
        }
    } else {
        ShellCompletionRow {
            pid: None,
            exit_code: None,
            content: match content {
                UserContent::Text(text) => text.clone(),
                UserContent::Blocks(blocks) => serde_json::to_string(blocks).unwrap_or_default(),
            },
        }
    }
}

/// TS `readCustomText`: content string or blocks joined with newlines
/// (text blocks keep their text, every non-text block renders `[image]`).
pub(crate) fn custom_content_text(content: &UserContent) -> String {
    match content {
        UserContent::Text(text) => text.clone(),
        UserContent::Blocks(blocks) => blocks
            .iter()
            .map(|block| match block {
                UserContentBlock::Text(text) => text.text.clone(),
                UserContentBlock::Image(_) | UserContentBlock::Raw(_) => "[image]".to_string(),
            })
            .collect::<Vec<_>>()
            .join("\n"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Line, Span};
    use serde_json::json;

    /// Decode one `role: "custom"` wire fixture and dispatch it.
    pub(super) fn decoded(message: &serde_json::Value) -> Vec<ChatEntry> {
        let mut message = message.clone();
        message["timestamp"] = json!(0);
        let message: eukhe_types::session::CustomMessage =
            serde_json::from_value(message).expect("custom fixture decodes");
        custom_message_entries(
            &CustomType::parse(&message.custom_type),
            &message.content,
            message.display,
            message.details.as_ref(),
        )
    }

    /// An agent's answer to the user's `@name` message decodes to the
    /// `name -> you` family row.
    #[test]
    fn an_agent_reply_decodes_to_the_family_row() {
        let message = json!({
            "role": "custom", "customType": "agent_reply", "display": true,
            "content": "[agent-reply from alpha]\n\nI reported 42.",
            "details": { "id": "r1", "from": "alpha", "message": "I reported 42." },
        });
        assert_eq!(
            decoded(&message),
            vec![ChatEntry::Swarm(Box::new(
                crate::swarm_block::SwarmRow::Relay(eukhe_types::daemon::AgentRelayEvent {
                    from: "alpha".to_string(),
                    to: "you".to_string(),
                    text: "I reported 42.".to_string(),
                })
            ))]
        );
    }

    #[test]
    fn non_display_rows_render_nothing() {
        // TS skips display=false rows everywhere (harness digests,
        // refinement notices, worker recovery are bookkeeping).
        for custom_type in [
            "harness_digest",
            "refinement_notice",
            "eukhe.worker_recovery",
            "agent_message",
        ] {
            let entries = decoded(&json!({
                "role": "custom",
                "customType": custom_type,
                "content": "kept out of the transcript",
                "display": false,
                "details": { "id": "agentmsg_1", "message": "body" },
            }));
            assert!(entries.is_empty(), "{custom_type} rendered {entries:?}");
        }
    }

    #[test]
    fn bookkeeping_types_render_the_generic_box_when_displayed() {
        // The TS live dispatch has no dedicated component for engine
        // bookkeeping, so a stray display=true row falls through to the
        // generic `CustomMessageComponent` box (in practice these persist
        // with display=false and render nothing).
        for custom_type in [
            "harness_digest",
            "refinement_notice",
            "eukhe.worker_recovery",
            "ipython_state",
            "thread_goal_state",
        ] {
            let entries = decoded(&json!({
                "role": "custom",
                "customType": custom_type,
                "content": "digest",
                "display": true,
            }));
            assert!(
                matches!(
                    entries.as_slice(),
                    [ChatEntry::CustomPanel(row)]
                        if row.custom_type == custom_type
                            && row.content == "digest"
                ),
                "{custom_type} rendered {entries:?}"
            );
        }
    }

    #[test]
    fn agent_message_decodes_counterpart_and_body() {
        let entries = decoded(&json!({
            "role": "custom",
            "customType": "agent_message",
            "content": "[agent-message from child:model-probe]\n\nready",
            "display": true,
            "details": {
                "id": "agentmsg_1",
                "message": "ready",
                "from": {
                    "sessionName": "model-probe",
                    "sessionId": "sess-1",
                    "activeSessionId": "aaa111",
                    "runtimeKind": "subagent",
                },
                "fromRelationship": "child",
            },
        }));
        let [ChatEntry::AgentMessage(row)] = entries.as_slice() else {
            panic!("agent message row: {entries:?}");
        };
        assert_eq!(row.counterpart, "model-probe");
        assert_eq!(row.message, "ready");
    }

    #[test]
    fn agent_message_counterpart_falls_back_to_ids() {
        // TS `formatAgentMessageParticipant`'s name leg: session name,
        // then active session id, client id, session id, then "unknown".
        // The relationship word never reaches the row (the arrow carries
        // the direction, the operator's 2026-09-25 directive).
        let base = |from: serde_json::Value| {
            decoded(&json!({
                "role": "custom",
                "customType": "agent_message",
                "content": "[agent-message from x]\n\nhi",
                "display": true,
                "details": {
                    "id": "agentmsg_2",
                    "message": "hi",
                    "from": from,
                    "fromRelationship": "child",
                },
            }))
        };
        let entry = |entries: Vec<ChatEntry>| match entries.as_slice() {
            [ChatEntry::AgentMessage(row)] => row.counterpart.clone(),
            other => panic!("agent message row: {other:?}"),
        };
        assert_eq!(
            entry(base(
                json!({ "activeSessionId": "aaa111", "sessionId": "s1" })
            )),
            "aaa111"
        );
        assert_eq!(
            entry(base(json!({ "clientId": "client-9", "sessionId": "s1" }))),
            "client-9"
        );
        assert_eq!(entry(base(json!({ "sessionId": "s1" }))), "s1");
        assert_eq!(entry(base(json!(null))), "unknown");
        assert_eq!(
            entry(base(json!({ "sessionName": "model-probe" }))),
            "model-probe"
        );
        // Without valid id/message details the row is not an agent message;
        // it falls through to the generic box.
        let entries = decoded(&json!({
            "role": "custom",
            "customType": "agent_message",
            "content": "[agent-message from x]",
            "display": true,
            "details": { "id": 1, "message": null },
        }));
        assert!(matches!(entries.as_slice(), [ChatEntry::CustomPanel(_)]));
    }

    #[test]
    fn injected_prompt_kinds_decode() {
        let heartbeat = decoded(&json!({
            "role": "custom",
            "customType": "heartbeat_prompt",
            "content": "[heartbeat: every 10m run#0]\n\nnudge",
            "display": true,
            "details": { "jobId": "j1", "schedule": "every 10m", "runCount": 0 },
        }));
        assert!(matches!(
            heartbeat.as_slice(),
            [ChatEntry::InjectedPrompt(boxed)]
                if matches!(boxed.kind, InjectedPromptKind::Heartbeat { ref schedule }
                    if schedule.as_deref() == Some("every 10m"))
        ));
        let goal = decoded(&json!({
            "role": "custom",
            "customType": "goal_context",
            "content": "[goal: continuation]",
            "display": true,
            "details": { "kind": "continuation", "objective": "ship it" },
        }));
        assert!(matches!(
            goal.as_slice(),
            [ChatEntry::InjectedPrompt(boxed)]
                if matches!(&boxed.kind,
                    InjectedPromptKind::Goal { kind, objective }
                        if kind.as_deref() == Some("continuation")
                            && objective.as_deref() == Some("ship it"))
        ));
        let restored = decoded(&json!({
            "role": "custom",
            "customType": "ipython_state_restored",
            "content": "[python-state-restored]",
            "display": true,
            "details": { "restored": false },
        }));
        assert!(matches!(
            restored.as_slice(),
            [ChatEntry::InjectedPrompt(boxed)]
                if matches!(boxed.kind, InjectedPromptKind::KernelRestored { restored: false })
        ));
        // The kernel-state row carries no expandable body.
        let restored = decoded(&json!({
            "role": "custom",
            "customType": "ipython_state_restored",
            "content": "[python-state-restored]",
            "display": true,
            "details": { "restored": true },
        }));
        assert!(matches!(
            restored.as_slice(),
            [ChatEntry::InjectedPrompt(boxed)] if boxed.body.is_none()
        ));
    }

    /// The RLM child status notices decode to the subagent-mail class
    /// (the operator's 2026-10-01 directive: "the factory child status
    /// notices should be like subagent messages not user messages"): the
    /// row carries the child as its counterpart and the notice text as
    /// the body, and it never renders as a turn-prompt (injected) or
    /// user row -- the class assertion is the mutation pin (routing the
    /// types back through the injected-prompt arm fails it).
    #[test]
    fn rlm_child_notice_rows_decode_to_the_agent_message_class() {
        let notices = [
            (
                "rlm_child_failure",
                "[child-failed child:lane]\n\nboom",
                json!({ "childId": "sub-1", "sessionName": "lane", "error": "boom" }),
            ),
            (
                "rlm_child_terminal_notice",
                "[child-exited: no-reply child:lane]\n\nLast assistant text: done",
                json!({ "childId": "sub-2", "sessionName": "lane", "kind": "completed_without_reply" }),
            ),
            (
                "rlm_child_terminal_notice",
                "[child-exited: cancelled child:cancel-worker]\n\nDeleted by parent",
                json!({ "childId": "sub-3", "sessionName": "cancel-worker", "kind": "cancelled", "reason": "Deleted by parent" }),
            ),
        ];
        for (custom_type, content, details) in notices {
            let entries = decoded(&json!({
                "role": "custom",
                "customType": custom_type,
                "content": content,
                "display": true,
                "details": details,
            }));
            let row = match entries.as_slice() {
                [ChatEntry::AgentMessage(row)] => row,
                other => panic!("{custom_type} must decode to the agent-message class: {other:?}"),
            };
            assert_eq!(row.direction, AgentMessageDirection::Received);
            assert_eq!(row.counterpart, details["sessionName"]);
            // The content rides intact as the body (outcome wording and
            // the child's last text included).
            assert_eq!(row.message, content);
            assert!(
                !matches!(
                    entries.as_slice(),
                    [ChatEntry::InjectedPrompt(_) | ChatEntry::User { .. }]
                ),
                "{custom_type} must not render as a turn-prompt/user row"
            );
        }
        // A row without details names no counterpart: the content header
        // is never parsed for one.
        let entries = decoded(&json!({
            "role": "custom",
            "customType": "rlm_child_failure",
            "content": "[child-failed child:legacy-worker]\n\nspawn failed",
            "display": true,
            "details": serde_json::Value::Null,
        }));
        assert!(matches!(
            entries.as_slice(),
            [ChatEntry::AgentMessage(row)]
                if row.counterpart == "unknown"
                    && row.message == "[child-failed child:legacy-worker]\n\nspawn failed"
        ));
    }

    /// The unavailable-skills row decodes the failed names and keeps the
    /// full report as its expandable body.
    #[test]
    fn python_skills_unavailable_row_decodes() {
        let unavailable = decoded(&json!({
            "role": "custom",
            "customType": "python_skills_unavailable",
            "content": "[python-skills-unavailable]\n\n- lookup: No module named 'lookup'",
            "display": true,
            "details": { "skills": ["lookup", "edit"] },
        }));
        assert!(matches!(
            unavailable.as_slice(),
            [ChatEntry::InjectedPrompt(boxed)]
                if matches!(&boxed.kind,
                    InjectedPromptKind::PythonSkillsUnavailable { skills }
                        if skills == &vec!["lookup".to_string(), "edit".to_string()])
                    && boxed.body.as_deref() == Some("[python-skills-unavailable]\n\n- lookup: No module named 'lookup'")
        ));
    }

    #[test]
    fn model_prompt_error_row_is_a_warning_status_line() {
        let entries = decoded(&json!({
            "role": "custom",
            "customType": "model_prompt_error",
            "content": "[model-prompt-error]\n\nPer-model system prompt additions were not applied:\n- /x/model-prompts.toml: bad TOML",
            "display": true,
        }));
        assert!(
            matches!(
                entries.as_slice(),
                [ChatEntry::Status { text, kind: crate::chat::StatusKind::Warning }]
                    if text.contains("[model-prompt-error]")
            ),
            "entries: {entries:?}"
        );
    }

    #[test]
    fn shell_completion_decodes_details() {
        let entries = decoded(&json!({
            "role": "custom",
            "customType": "async_bash_completion",
            "content": "[bash-done pid:4371 exit:0]\n\nCommand: \"ls\"",
            "display": true,
            "details": { "pid": 4371, "command": "ls", "exitCode": 0 },
        }));
        assert!(matches!(
            entries.as_slice(),
            [ChatEntry::ShellCompletion(row)]
                if row.pid == Some(4371) && row.exit_code == Some(0)
        ));
        // An invalid details block (TS `readShellCompletion` requires a
        // positive pid, a string command, and an integer exit code) keeps
        // the default finished row and the JSON content fallback.
        let entries = decoded(&json!({
            "role": "custom",
            "customType": "async_bash_completion",
            "content": [{ "type": "text", "text": "[bash-done]" }],
            "display": true,
            "details": { "pid": -1, "exitCode": 3 },
        }));
        assert!(matches!(
            entries.as_slice(),
            [ChatEntry::ShellCompletion(row)]
                if row.pid.is_none() && row.exit_code.is_none()
        ));
    }

    #[test]
    fn agent_message_accepts_empty_string_details() {
        // TS `isAgentSessionMessage` checks only `typeof id === "string"`
        // and `typeof message === "string"`; empty strings still decode as
        // agent-message rows.
        let entries = decoded(&json!({
            "role": "custom",
            "customType": "agent_message",
            "content": "[agent-message from x]",
            "display": true,
            "details": { "id": "", "message": "" },
        }));
        assert!(matches!(entries.as_slice(), [ChatEntry::AgentMessage(_)]));
    }

    #[test]
    fn compaction_outcome_maps_to_status_rows() {
        let skipped = decoded(&json!({
            "role": "custom",
            "customType": "compaction_outcome",
            "content": "Compaction skipped: below threshold",
            "display": true,
            "details": { "reason": "threshold", "outcome": "skipped" },
        }));
        assert_eq!(
            skipped,
            vec![ChatEntry::Status {
                text: "Compaction skipped: below threshold".to_string(),
                kind: StatusKind::Warning,
            }]
        );
        let failed = decoded(&json!({
            "role": "custom",
            "customType": "compaction_outcome",
            "content": "Compaction failed",
            "display": true,
            "details": { "reason": "requested", "outcome": "failed" },
        }));
        assert_eq!(
            failed,
            vec![ChatEntry::Status {
                text: "Compaction failed".to_string(),
                kind: StatusKind::Error,
            }]
        );
        let malformed = decoded(&json!({
            "role": "custom",
            "customType": "compaction_outcome",
            "content": "Compaction?",
            "display": true,
            "details": { "reason": "wat" },
        }));
        assert_eq!(
            malformed,
            vec![ChatEntry::Status {
                text: "[Malformed compaction outcome message]".to_string(),
                kind: StatusKind::Error,
            }]
        );
    }

    #[test]
    fn unknown_displayed_types_render_the_generic_box() {
        let entries = decoded(&json!({
            "role": "custom",
            "customType": "autonomous_status",
            "content": "[autonomous-status: on]",
            "display": true,
            "details": { "enabled": true },
        }));
        assert!(matches!(
            entries.as_slice(),
            [ChatEntry::CustomPanel(row)]
                if row.custom_type == "autonomous_status"
                    && row.content == "[autonomous-status: on]"
        ));
    }

    /// Flattened rows with the trailing padding trimmed (whole-vector
    /// equality against the painted transcript text).
    fn plain_rows(rows: &[Line]) -> Vec<String> {
        rows.iter()
            .map(|row| {
                row.iter()
                    .map(|span| span.content.as_str())
                    .collect::<String>()
                    .trim_end()
                    .to_string()
            })
            .collect()
    }

    /// One gutter for every expandable chat body, the Rust twin of TS
    /// #2779's `expandable-event-message.test.ts`: the dim gutter row sits
    /// right below the header, the rest on the four-column indent, and the
    /// collapsed rows stay bare. The compaction metadata rides its header
    /// row, and the skill name lives on the header only.
    #[test]
    fn expandable_bodies_hang_on_one_gutter() {
        use crate::chat::Detail;
        use crate::compaction_row::render_compaction_summary;
        let theme = crate::theme::Theme::builtin("eukhe", crate::theme::ColorMode::TrueColor);
        let gutter = Span::styled(
            crate::branch::BRANCH_GUTTER.to_string(),
            theme.fg_style(ThemeColor::Dim),
        );
        // 57 columns wrap at the branch content width 56: one full row
        // plus one.
        let body = "w".repeat(57);
        let head = format!(" {}{}", crate::branch::BRANCH_GUTTER, "w".repeat(56));
        let tail = format!("{}w", crate::branch::BRANCH_INDENT);
        let skill = SkillInvocationRow {
            name: "review".to_string(),
            content: body.clone(),
        };
        let goal = InjectedPromptRow {
            kind: InjectedPromptKind::Goal {
                kind: Some("continuation".to_string()),
                objective: Some("Ship.".to_string()),
            },
            body: Some(body.clone()),
        };
        let shell = ShellCompletionRow {
            pid: None,
            exit_code: Some(0),
            content: body.clone(),
        };
        let panel = CustomPanelRow {
            custom_type: "notice".to_string(),
            content: body.clone(),
        };
        let compacted = format!(" {body}");
        // (collapsed rows + their expected text, expanded rows, expanded
        // header text)
        let cases = vec![
            (
                Some((
                    skill_invocation::render_skill_invocation(
                        &skill,
                        Detail::Overview,
                        &theme,
                        60,
                        false,
                    ),
                    vec![" [skill] review"],
                )),
                skill_invocation::render_skill_invocation(&skill, Detail::All, &theme, 60, false),
                vec![" [skill] review"],
            ),
            (
                Some((
                    injected_prompt::render_injected_prompt(&goal, Detail::Overview, &theme, 60),
                    vec!["", " Goal continuation - Ship."],
                )),
                injected_prompt::render_injected_prompt(&goal, Detail::All, &theme, 60),
                vec!["", " Goal continuation - Ship."],
            ),
            (
                Some((
                    render::render_shell_completion(&shell, Detail::Overview, &theme, 60, false),
                    vec![" ok Background shell command finished"],
                )),
                render::render_shell_completion(&shell, Detail::All, &theme, 60, false),
                vec![" ok Background shell command finished"],
            ),
            (
                None,
                render::render_custom_panel(&panel, &theme, 60),
                vec!["", " [notice]"],
            ),
            (
                Some((
                    render_compaction_summary(&body, 480, None, false, &theme, 60),
                    vec![" * Context compacted", compacted.as_str()],
                )),
                render_compaction_summary(&body, 480, None, true, &theme, 60),
                vec![" * Context compacted - Compacted from 480 tokens"],
            ),
        ];
        for (collapsed, expanded, header) in cases {
            if let Some((rows, text)) = collapsed {
                assert_eq!(plain_rows(&rows), text, "{rows:?}");
            }
            let mut text = header.clone();
            text.extend([head.as_str(), tail.as_str()]);
            assert_eq!(plain_rows(&expanded), text, "{expanded:?}");
            assert_eq!(expanded[header.len()][1], gutter, "{expanded:?}");
        }
    }
}
