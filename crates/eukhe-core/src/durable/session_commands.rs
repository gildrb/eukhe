//! Session slash commands on the durable session: `/compact`, `/refine`,
//! `/goal`, `/autonomous`, `/remind`, `/force`, and `/dynamic-workflow`, including the
//! `/refine` and `/force` argument parsing.
//! Shared by print mode, rpc mode, and the daemon worker's prompt path.
//! On main (`sessionShape` `main-worker`) `/goal` and `/autonomous` run on
//! its worker, where the work runs.
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

use super::children::worker_session_command;
use super::deps::SessionShape;
use super::directors::{push_director, DirectorLimits, Layer};
use super::entries::custom_entry_draft;
use super::goals::{
    autonomous_state, clear_goal, goal_state, pause_goal, resume_goal, set_autonomous, start_goal,
    AutonomousChange,
};
use super::messages::{
    SESSION_SLASH_COMMAND_CUSTOM_TYPE, SESSION_SLASH_COMMAND_RESULT_CUSTOM_TYPE,
};
use super::rlm::{refine_now, RefineRequest};
use super::workflow::command::parse_dynamic_workflow_args;
use super::workflow::effective_limits;
use super::EukheSession;
use crate::autonomous::{now_millis, AgentAutonomousStatus, AUTONOMOUS_STATUS_CUSTOM_TYPE};
use crate::goals::{GoalState, GoalStatus};
use crate::slash_command_args::{
    format_autonomous_status, parse_autonomous_command, parse_goal_command, AutonomousCommand,
    GoalCommand,
};
use eukhe_durable::harness::types::{InputSubmissionDraft, WhenBusy};
use eukhe_types::input_origin::InputOrigin;
use eukhe_types::workflow::WorkflowSize;

#[cfg(test)]
mod tests;

/// Parsed `/refine` options.
#[derive(Debug, Default, PartialEq)]
pub(crate) struct RefineCommandOptions {
    pub(crate) instructions: Option<String>,
    pub(crate) rollback_id: Option<String>,
    pub(crate) global: bool,
}

/// Parse `/refine [--global] [instructions]` and `/refine rollback <id>`.
///
/// # Errors
///
/// Returns a usage-error string when `rollback` is given without a
/// refinement id.
pub(crate) fn parse_refine_command_options(args: &str) -> Result<RefineCommandOptions, String> {
    let mut rest = args.trim();
    let mut global = false;
    if rest.starts_with("--global") && matches!(rest.as_bytes().get(8), None | Some(b' ' | b'\t')) {
        global = true;
        rest = rest["--global".len()..].trim();
    }
    if rest == "rollback" {
        return Err("Usage: /refine rollback <refinement-id>".to_string());
    }
    if let Some(tail) = rest.strip_prefix("rollback") {
        if tail.starts_with('\t') || tail.starts_with(' ') {
            let mut rollback_id = rest["rollback".len()..].trim().to_string();
            if rollback_id == "--global" {
                return Err("Usage: /refine rollback <refinement-id>".to_string());
            }
            if rollback_id.ends_with(" --global") {
                global = true;
                rollback_id = rollback_id.trim_end_matches(" --global").trim().to_string();
            }
            if rollback_id.is_empty() {
                return Err("Usage: /refine rollback <refinement-id>".to_string());
            }
            return Ok(RefineCommandOptions {
                instructions: None,
                rollback_id: Some(rollback_id),
                global,
            });
        }
    }
    Ok(RefineCommandOptions {
        instructions: (!rest.is_empty()).then(|| rest.to_string()),
        rollback_id: None,
        global,
    })
}

/// The session-executed commands.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SessionCommandName {
    Compact,
    Refine,
    Goal,
    Autonomous,
    Remind,
    Force,
    DynamicWorkflow,
}

impl SessionCommandName {
    /// The command's name as typed (`compact`, `refine`, `goal`,
    /// `autonomous`, `remind`, `force`).
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Compact => "compact",
            Self::Refine => "refine",
            Self::Goal => "goal",
            Self::Autonomous => "autonomous",
            Self::Remind => "remind",
            Self::Force => "force",
            Self::DynamicWorkflow => "dynamic-workflow",
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
            "remind" => Some(Self::Remind),
            "force" => Some(Self::Force),
            "dynamic-workflow" => Some(Self::DynamicWorkflow),
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
    /// `/dynamic-workflow`: the size of the workflow it asked for.
    pub dynamic_workflow: Option<WorkflowSize>,
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
        // Main's directors drive the work, and the work runs on its worker.
        SessionCommandName::Goal | SessionCommandName::Autonomous
            if session.deps().shape == SessionShape::Main =>
        {
            execute_on_worker(session, conversation, command, cx).await
        }
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
        SessionCommandName::Remind => match command.args.trim() {
            "" => Err("Usage: /remind <text>".to_owned()),
            text => {
                let layer = Layer::reminder(text.to_owned());
                let report = "Reminder added: it leads the next continuation.".to_owned();
                push_layer(session, conversation, command, layer, report, cx).await
            }
        },
        SessionCommandName::Force => match parse_force_command(&command.args) {
            Ok((tool, tries)) => {
                let report = format!("The next requests force a call to `{tool}`.");
                let layer = Layer::force_tool(tool, tries);
                push_layer(session, conversation, command, layer, report, cx).await
            }
            Err(usage) => Err(usage),
        },
        SessionCommandName::DynamicWorkflow => {
            execute_dynamic_workflow(session, conversation, command, &mut outcome, cx).await
        }
    };
    if let Err(message) = result {
        let committed = append_rows(conversation, vec![failure_row(command, &message)], cx).await;
        outcome.error = Some(committed.err().unwrap_or(message));
    }
    outcome
}

/// Commit only the `session_slash_command` echo row of `command`: the
/// host that runs the command itself (the daemon worker's `/compact`,
/// which drives the manual compaction and its event pair) records the
/// attempt first, as [`execute_session_command`] does.
///
/// # Errors
///
/// The commit failure.
pub async fn commit_session_command_echo(
    conversation: &Conversation,
    command: &SessionCommand,
    cx: &Context,
) -> Result<(), String> {
    append_rows(conversation, vec![echo_row(command)], cx).await
}

/// Commit the `Command failed: <error>` result row of `command` (the
/// failure arm of a host-run command, see [`commit_session_command_echo`]).
///
/// # Errors
///
/// The commit failure.
pub async fn commit_session_command_failure(
    conversation: &Conversation,
    command: &SessionCommand,
    error: &str,
    cx: &Context,
) -> Result<(), String> {
    append_rows(conversation, vec![failure_row(command, error)], cx).await
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

/// `/goal` and `/autonomous` on main (`sessionShape` `main-worker`): the
/// command runs on main's worker as if typed there (a stopped worker
/// wakes for it); main records where it went. Main without a worker yet
/// refuses: its first hand-over creates the worker.
async fn execute_on_worker(
    session: &EukheSession,
    conversation: &Conversation,
    command: &SessionCommand,
    cx: &Context,
) -> Result<(), String> {
    let name = command.name.as_str();
    let no_worker = || {
        format!("No worker yet: /{name} applies to the worker, which main creates with the first work you give it")
    };
    let Some(host) = session.deps().children.as_ref() else {
        return Err(no_worker());
    };
    match worker_session_command(
        session.harness(),
        host.as_ref(),
        conversation.id(),
        &command.text,
        cx,
    )
    .await
    {
        Ok(Some(worker)) => {
            let text = format!("/{name} applied to {worker}: its chat shows the result.");
            append_rows(
                conversation,
                vec![result_row(command, text, Visibility::Shown)],
                cx,
            )
            .await
        }
        Ok(None) => Err(no_worker()),
        Err(error) => Err(format!("{error:#}")),
    }
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

/// Parse `/force <tool> [--tries <n>]`: the tool and its retries per
/// forced run (default 1).
///
/// # Errors
///
/// A usage-error string when the tool is missing or `--tries` has no
/// non-negative integer.
fn parse_force_command(args: &str) -> Result<(String, u32), String> {
    const USAGE: &str = "Usage: /force <tool> [--tries <n>]";
    let mut words = args.split_whitespace();
    let Some(tool) = words.next().filter(|tool| !tool.starts_with("--")) else {
        return Err(USAGE.to_owned());
    };
    let tries = match (words.next(), words.next(), words.next()) {
        (None, None, None) => 1,
        (Some("--tries"), Some(tries), None) => tries.parse().map_err(|_| USAGE.to_owned())?,
        _ => return Err(USAGE.to_owned()),
    };
    Ok((tool.to_owned(), tries))
}

/// `/dynamic-workflow [--size <size>] <request>`: submit the request as a
/// user turn that asks for one `workflow` tool call of the chosen size
/// (the `workflow.size` setting when no `--size` is given).
async fn execute_dynamic_workflow(
    session: &EukheSession,
    conversation: &Conversation,
    command: &SessionCommand,
    outcome: &mut SessionCommandOutcome,
    cx: &Context,
) -> Result<(), String> {
    let parsed = parse_dynamic_workflow_args(&command.args)?;
    let manager = session.deps().settings.manager();
    let size = parsed.size.unwrap_or_else(|| manager.get_workflow_size());
    let limits = effective_limits(size, manager.get_subagent_max_concurrency());
    let request_json = serde_json::Value::String(parsed.request.clone());
    let text = format!(
        "Run this request as a dynamic workflow: author one orchestration script and run it with one `workflow` tool call, with `size: \"{size}\"` and `args: {request_json}`. Size {size}: at most {concurrency} agents at once and {max_agents} in total; plan the work to fit. Give each agent a short `label`, use `meta.phases` and `phase()` for the stages. The run goes on in the background: tell me it started, then end your turn; when its result message arrives, summarize the result for me.\n\nRequest: {request}",
        size = size.as_str(),
        concurrency = limits.concurrency,
        max_agents = limits.max_agents,
        request = parsed.request,
    );
    conversation
        .submit(
            InputSubmissionDraft {
                request_id: None,
                content: UserContent::Text(text),
                when_busy: Some(WhenBusy::FollowUp),
                origin: InputOrigin::User,
                entry: None,
            },
            cx,
        )
        .await
        .map_err(|error| error.to_string())?;
    outcome.dynamic_workflow = Some(size);
    Ok(())
}

/// `/remind` and `/force`: put `layer` on the Director stack of the
/// conversation, and report `text` in a shown result row.
#[tracing::instrument(skip_all)]
async fn push_layer(
    session: &EukheSession,
    conversation: &Conversation,
    command: &SessionCommand,
    layer: Layer,
    text: String,
    cx: &Context,
) -> Result<(), String> {
    let limits = DirectorLimits::of(session.deps().settings.manager().settings());
    push_director(session.harness(), conversation.id(), layer, limits, cx)
        .await
        .map_err(|error| error.to_string())?;
    append_rows(
        conversation,
        vec![result_row(command, text, Visibility::Shown)],
        cx,
    )
    .await
}
