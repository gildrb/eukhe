//! Session slash commands on the durable session: `/compact`, `/refine`,
//! `/goal`, and `/autonomous` (port of `session_engine::session_commands`
//! and the session half of `session_engine::slash_commands`). Shared by
//! print mode, rpc mode, and the daemon worker's prompt path.
//!
//! The rows are `eukhe.custom` entries committed on the command's
//! conversation: the `session_slash_command` echo first (durable whether the
//! command succeeds or fails), then the command's own rows and its
//! `session_slash_command_result` row. A failure appends the
//! `Command failed: <e>` result row and reports the raw error.

use eukhe_chord::context::Context;
use eukhe_durable::harness::types::CompactionResult;
use eukhe_durable::harness::Conversation;
use eukhe_durable::types::{EntryDraft, TaskId};
use eukhe_types::pi_ai::UserContent;
use eukhe_types::slash_commands::SlashCommandRegistry;
use serde_json::{json, Value};

use super::entries::custom_entry_draft;
use super::goals::{
    autonomous_state, clear_goal, goal_state, pause_goal, resume_goal, set_autonomous, start_goal,
    AutonomousChange,
};
use super::rlm::{refine_now, RefineRequest};
use super::EukheSession;
use crate::autonomous::{now_millis, AgentAutonomousStatus, AUTONOMOUS_STATUS_CUSTOM_TYPE};
use crate::goals::{GoalState, GoalStatus};
use crate::session_engine::messages::{
    SESSION_SLASH_COMMAND_CUSTOM_TYPE, SESSION_SLASH_COMMAND_RESULT_CUSTOM_TYPE,
};
use crate::session_engine::slash_commands::parse_refine_command_options;
use crate::slash_command_args::{
    format_autonomous_status, parse_autonomous_command, parse_goal_command, AutonomousCommand,
    GoalCommand,
};

#[cfg(test)]
mod tests;

/// The session-executed commands.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SessionCommandName {
    Compact,
    Refine,
    Goal,
    Autonomous,
}

impl SessionCommandName {
    /// The command's name as typed (`compact`, `refine`, `goal`, `autonomous`).
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Compact => "compact",
            Self::Refine => "refine",
            Self::Goal => "goal",
            Self::Autonomous => "autonomous",
        }
    }

    /// The session command named `name`; `None` for any other name.
    #[must_use]
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "compact" => Some(Self::Compact),
            "refine" => Some(Self::Refine),
            "goal" => Some(Self::Goal),
            "autonomous" => Some(Self::Autonomous),
            _ => None,
        }
    }
}

/// A parsed session slash command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SessionCommand {
    pub name: SessionCommandName,
    /// The arguments after the command name.
    pub args: String,
    /// The input as typed.
    pub text: String,
}

/// What one execution produced.
#[derive(Debug, Default)]
pub struct SessionCommandOutcome {
    /// The raw failure (the `Command failed: ...` row is already committed).
    pub error: Option<String>,
    /// `/compact`: the admitted compaction task (it emits its own events).
    pub compaction: Option<TaskId<CompactionResult>>,
    /// `/goal`: the resulting goal.
    pub goal: Option<GoalState>,
    /// `/autonomous`: the resulting status.
    pub autonomous: Option<AgentAutonomousStatus>,
    /// `/refine`: the refinement run's own failure (TS `refine_failed`;
    /// a usage error never ran a refinement and leaves it `None`).
    pub refinement_failed: Option<String>,
}

/// Classify `text` as a session command through the builtin slash-command
/// table (aliases resolve to their command); `None` for any other input.
/// Prompt templates are the caller's: classify the expanded text.
#[must_use]
pub fn classify_session_command(text: &str) -> Option<SessionCommand> {
    let resolved = SlashCommandRegistry::builtin_cached().parse(text)?;
    Some(SessionCommand {
        name: SessionCommandName::from_name(resolved.name)?,
        args: resolved.args,
        text: text.to_owned(),
    })
}

/// Execute `command` on `conversation` of `session`: commit the echo row,
/// run the command, and commit its rows. Failures land in `error` with the
/// `Command failed: <e>` result row committed; a failed echo commit runs
/// nothing.
pub async fn execute_session_command(
    session: &EukheSession,
    conversation: &Conversation,
    command: &SessionCommand,
    cx: &Context,
) -> SessionCommandOutcome {
    let mut outcome = SessionCommandOutcome::default();
    if let Err(error) = append_rows(conversation, vec![echo_row(command)], cx).await {
        outcome.error = Some(error);
        return outcome;
    }
    let result = match command.name {
        SessionCommandName::Compact => {
            execute_compact(conversation, command, &mut outcome, cx).await
        }
        SessionCommandName::Refine => {
            execute_refine(session, conversation, command, &mut outcome, cx).await
        }
        SessionCommandName::Goal => {
            execute_goal(session, conversation, command, &mut outcome, cx).await
        }
        SessionCommandName::Autonomous => {
            execute_autonomous(session, conversation, command, &mut outcome, cx).await
        }
    };
    if let Err(message) = result {
        let committed = append_rows(conversation, vec![failure_row(command, &message)], cx).await;
        outcome.error = Some(committed.err().unwrap_or(message));
    }
    outcome
}

/// A custom row before its timestamp and draft.
struct Row {
    custom_type: &'static str,
    text: String,
    display: bool,
    details: Value,
}

/// The command description carried by echo and result rows.
fn command_details(command: &SessionCommand) -> Value {
    json!({
        "command": {
            "name": command.name.as_str(),
            "args": command.args,
            "text": command.text,
        }
    })
}

/// The `session_slash_command` echo row.
fn echo_row(command: &SessionCommand) -> Row {
    Row {
        custom_type: SESSION_SLASH_COMMAND_CUSTOM_TYPE,
        text: command.text.clone(),
        display: true,
        details: command_details(command),
    }
}

/// How a result row reads.
#[derive(Clone, Copy)]
enum Visibility {
    Shown,
    Hidden,
}

/// The `session_slash_command_result` row of a success.
fn result_row(command: &SessionCommand, text: String, visibility: Visibility) -> Row {
    let mut details = command_details(command);
    details["success"] = json!(true);
    details["severity"] = json!("info");
    Row {
        custom_type: SESSION_SLASH_COMMAND_RESULT_CUSTOM_TYPE,
        text,
        display: matches!(visibility, Visibility::Shown),
        details,
    }
}

/// The `session_slash_command_result` row of a failure.
fn failure_row(command: &SessionCommand, error: &str) -> Row {
    let mut details = command_details(command);
    details["success"] = json!(false);
    details["severity"] = json!("error");
    details["error"] = json!(error);
    Row {
        custom_type: SESSION_SLASH_COMMAND_RESULT_CUSTOM_TYPE,
        text: format!("Command failed: {error}"),
        display: true,
        details,
    }
}

/// Commit `rows` in order on `conversation`, in one commit.
async fn append_rows(
    conversation: &Conversation,
    rows: Vec<Row>,
    cx: &Context,
) -> Result<(), String> {
    let timestamp = now_millis();
    let drafts = rows
        .into_iter()
        .map(|row| {
            custom_entry_draft(
                row.custom_type,
                UserContent::Text(row.text),
                row.display,
                Some(row.details),
                timestamp,
            )
        })
        .collect::<Result<Vec<EntryDraft>, _>>()
        .map_err(|error| error.to_string())?;
    let conversation_id = conversation.id();
    conversation
        .commit(
            move |tx| async move {
                for draft in drafts {
                    tx.append_entry(conversation_id, draft).await?;
                }
                Ok(())
            },
            cx,
        )
        .await
        .map_err(|error| error.to_string())
}

/// `/compact [instructions]`: admit a manual compaction (no result row: the
/// compaction is the outcome).
async fn execute_compact(
    conversation: &Conversation,
    command: &SessionCommand,
    outcome: &mut SessionCommandOutcome,
    cx: &Context,
) -> Result<(), String> {
    let instructions = (!command.args.is_empty()).then(|| command.args.clone());
    let task = conversation
        .compact(instructions, cx)
        .await
        .map_err(|error| error.to_string())?;
    outcome.compaction = Some(task);
    Ok(())
}

/// `/refine`: run the refinement (it commits its audit, outcome, and notice
/// rows) and record the applied-edit count in a hidden result row (the
/// outcome row renders the details).
async fn execute_refine(
    session: &EukheSession,
    conversation: &Conversation,
    command: &SessionCommand,
    outcome: &mut SessionCommandOutcome,
    cx: &Context,
) -> Result<(), String> {
    let options = parse_refine_command_options(&command.args)?;
    let request = RefineRequest {
        instructions: options.instructions,
        global: options.global,
        rollback_id: options.rollback_id,
    };
    let result = match refine_now(session.deps(), conversation, request, cx).await {
        Ok(result) => result,
        Err(error) => {
            let message = format!("{error:#}");
            outcome.refinement_failed = Some(message.clone());
            return Err(message);
        }
    };
    let applied = result
        .applied_edits
        .iter()
        .filter(|edit| edit.applied)
        .count();
    let text = format!(
        "Refined continual harness state: {applied} edit{} applied.",
        if applied == 1 { "" } else { "s" }
    );
    append_rows(
        conversation,
        vec![result_row(command, text, Visibility::Hidden)],
        cx,
    )
    .await
}

/// The goal status line (`Goal <status>: <objective>` / `No active goal.`).
fn goal_status_text(state: &GoalState) -> String {
    match &state.objective {
        Some(objective) if state.status != GoalStatus::Idle => {
            format!("Goal {}: {objective}", state.status.slug())
        }
        _ => "No active goal.".to_owned(),
    }
}

/// `/goal`: status, clear, pause, resume, and start (start and resume submit
/// their continuation context themselves).
async fn execute_goal(
    session: &EukheSession,
    conversation: &Conversation,
    command: &SessionCommand,
    outcome: &mut SessionCommandOutcome,
    cx: &Context,
) -> Result<(), String> {
    let goal = parse_goal_command(&command.args)?;
    let harness = session.harness();
    let id = conversation.id();
    let failed = |error: eukhe_durable::session::SessionError| error.to_string();
    let (state, text) = match goal {
        GoalCommand::Status => {
            let state = goal_state(harness, id, cx).await.map_err(failed)?;
            let text = goal_status_text(&state);
            (state, text)
        }
        GoalCommand::Clear => {
            // A clear that removed a goal says so; with nothing to clear
            // it answers the plain status.
            let cleared = clear_goal(harness, id, cx).await.map_err(failed)?;
            let state = goal_state(harness, id, cx).await.map_err(failed)?;
            let text = if cleared {
                "Goal cleared.".to_owned()
            } else {
                goal_status_text(&state)
            };
            (state, text)
        }
        GoalCommand::Pause => {
            let state = pause_goal(harness, id, cx).await.map_err(failed)?;
            let text = goal_status_text(&state);
            (state, text)
        }
        GoalCommand::Resume => {
            let state = resume_goal(harness, id, cx).await.map_err(failed)?;
            let text = goal_status_text(&state);
            (state, text)
        }
        GoalCommand::Start {
            objective,
            token_budget,
        } => {
            let state = start_goal(harness, id, &objective, token_budget, cx)
                .await
                .map_err(failed)?;
            let text = goal_status_text(&state);
            (state, text)
        }
    };
    outcome.goal = Some(state);
    append_rows(
        conversation,
        vec![result_row(command, text, Visibility::Shown)],
        cx,
    )
    .await
}

/// `/autonomous`: status, on (with budget flags), off; each appends the
/// `autonomous_status` row.
async fn execute_autonomous(
    session: &EukheSession,
    conversation: &Conversation,
    command: &SessionCommand,
    outcome: &mut SessionCommandOutcome,
    cx: &Context,
) -> Result<(), String> {
    let parsed = parse_autonomous_command(&command.args)?;
    let harness = session.harness();
    let id = conversation.id();
    let change = match parsed {
        AutonomousCommand::On { config } => AutonomousChange::On(config),
        AutonomousCommand::Off => AutonomousChange::Off,
        AutonomousCommand::Status => {
            let status = autonomous_state(harness, id, cx)
                .await
                .map_err(|error| error.to_string())?
                .status();
            let details = serde_json::to_value(&status).map_err(|error| error.to_string())?;
            let row = Row {
                custom_type: AUTONOMOUS_STATUS_CUSTOM_TYPE,
                text: format_autonomous_status(&status),
                display: true,
                details,
            };
            outcome.autonomous = Some(status);
            return append_rows(conversation, vec![row], cx).await;
        }
    };
    let status = set_autonomous(harness, id, change, cx)
        .await
        .map_err(|error| error.to_string())?;
    outcome.autonomous = Some(status);
    Ok(())
}
