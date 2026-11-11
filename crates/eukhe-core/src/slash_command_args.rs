//! Session slash-command arguments and status formatting for `/goal` and
//! `/autonomous`. The arguments are the compiled core's
//! (`eukhe_bend::rules::slash_args`, `laws/slash_args.bend`): this module
//! maps its answers to the session's types. The status text is a port of
//! agent-session.ts `_formatAutonomousStatus`; its turns, tokens and time
//! are the session budget's (requests, tokens, deadline).

use eukhe_bend::rules::slash_args::{self, AutonomousArgs, GoalArgs, Limit};
use eukhe_types::budget::BudgetDimension;

use crate::autonomous::{
    AgentAutonomousConfig, AgentAutonomousGateConfig, AgentAutonomousStatus,
    UNLIMITED_AUTONOMOUS_LIMIT,
};

/// A parsed `/goal` argument string.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GoalCommand {
    Status,
    Clear,
    Pause,
    Resume,
    Start {
        objective: String,
        token_budget: Option<u64>,
    },
}

/// The compiled core's refusal of a `/goal` or `/autonomous` argument
/// string: its usage text, shown as the core wrote it.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("{text}")]
pub struct SlashArgsRefusal {
    /// The core's usage text.
    pub text: String,
}

/// Parse `/goal [status|clear|stop|pause|resume|[--budget <tokens>] <objective>]`.
///
/// # Errors
///
/// The core's usage text when the budget flag is given without a value or
/// an objective, when the budget is not a positive integer, or when the
/// objective is missing or exceeds the configured character limit.
pub fn parse_goal_command(args: &str) -> Result<GoalCommand, SlashArgsRefusal> {
    match slash_args::goal(args) {
        GoalArgs::Status => Ok(GoalCommand::Status),
        GoalArgs::Clear => Ok(GoalCommand::Clear),
        GoalArgs::Pause => Ok(GoalCommand::Pause),
        GoalArgs::Resume => Ok(GoalCommand::Resume),
        GoalArgs::Start {
            objective,
            token_budget,
        } => Ok(GoalCommand::Start {
            objective,
            token_budget,
        }),
        GoalArgs::Error(text) => Err(SlashArgsRefusal { text }),
    }
}

/// A parsed `/autonomous` argument string.
#[derive(Debug, Clone, PartialEq)]
pub enum AutonomousCommand {
    Status,
    On { config: AgentAutonomousConfig },
    Off,
}

/// Parse `/autonomous [status|off|on [--max-continuations <n>] ...]`.
///
/// # Errors
///
/// The core's usage text for an unexpected subcommand, trailing arguments
/// after `status`/`off`, or invalid budget options.
pub fn parse_autonomous_command(args: &str) -> Result<AutonomousCommand, SlashArgsRefusal> {
    match slash_args::autonomous(args) {
        AutonomousArgs::Status => Ok(AutonomousCommand::Status),
        AutonomousArgs::Off => Ok(AutonomousCommand::Off),
        AutonomousArgs::Error(text) => Err(SlashArgsRefusal { text }),
        AutonomousArgs::On(options) => Ok(AutonomousCommand::On {
            config: AgentAutonomousConfig {
                max_continuations: options.max_continuations.map(limit),
                max_turns: options.max_turns.map(limit),
                max_tokens: options.max_tokens.map(limit),
                timeout_ms: options.timeout_ms.map(limit),
                gates: options.gates.map(|gates| AgentAutonomousGateConfig {
                    commands: gates.commands,
                    max_retries: gates.max_retries,
                    timeout_ms: gates.timeout_ms,
                }),
                subagent_keep_alive_ms: options.subagent_keep_alive_ms,
                ..AgentAutonomousConfig::default()
            },
        }),
    }
}

/// A named limit as the autonomous config holds it.
fn limit(limit: Limit) -> u64 {
    match limit {
        Limit::Unlimited => UNLIMITED_AUTONOMOUS_LIMIT,
        Limit::Value(value) => value,
    }
}

/// `formatCount` for autonomous status values: unlimited or en-US grouping.
fn format_count(value: u64) -> String {
    if value == UNLIMITED_AUTONOMOUS_LIMIT {
        "unlimited".to_string()
    } else {
        let mut grouped = String::new();
        let digits = value.to_string();
        for (index, digit) in digits.chars().enumerate() {
            if index > 0 && (digits.len() - index).is_multiple_of(3) {
                grouped.push(',');
            }
            grouped.push(digit);
        }
        grouped
    }
}

/// `_formatAutonomousStatus`: the `[autonomous-status: ...]` block. Turns,
/// tokens and time are the session budget's requests, tokens and deadline
/// (`unlimited` where it sets none); the time used without a deadline is
/// the run's age.
#[must_use]
pub fn format_autonomous_status(status: &AgentAutonomousStatus) -> String {
    let state = if status.enabled { "on" } else { "off" };
    let budget = status.budget.as_ref();
    let used = |dimension: BudgetDimension| budget.map_or(0, |report| report.spent.get(dimension));
    let limit = |dimension: BudgetDimension| {
        budget
            .and_then(|report| report.limits.get(dimension))
            .map_or_else(|| "unlimited".to_string(), format_count)
    };
    let (elapsed_seconds, time_budget) =
        match budget.and_then(|report| report.limits.time_ms.map(|limit| (report, limit))) {
            Some((report, limit)) => (
                limit.saturating_sub(report.free.time_ms) / 1000,
                format!("{}s", format_count(limit / 1000)),
            ),
            None => (
                status.started_at.map_or(0, |started_at| {
                    now_millis().saturating_sub(started_at) / 1000
                }),
                "unlimited".to_string(),
            ),
        };
    let gate_summary = if status.gates.commands.is_empty() {
        "none".to_string()
    } else {
        status
            .gates
            .commands
            .iter()
            .map(|command| format!("\"{command}\""))
            .collect::<Vec<_>>()
            .join(", ")
    };
    let subagent_keep_alive_ms = status.subagent_keep_alive_ms.unwrap_or(0);
    let keep_alive = if subagent_keep_alive_ms > 0 {
        if subagent_keep_alive_ms >= 60_000 {
            format!("{}m", format_count(subagent_keep_alive_ms / 60_000))
        } else {
            format!("{}ms", format_count(subagent_keep_alive_ms))
        }
    } else {
        "off".to_string()
    };
    format!(
        "[autonomous-status: {state}]\n\nContinuations: {}/{}. Turns: {}/{}. Tokens: {}/{}. Time: {elapsed_seconds}s/{time_budget}. Gates: {gate_summary}. Subagent keep-alive: {keep_alive}.",
        format_count(status.continuations_used),
        format_count(status.limits.max_continuations),
        format_count(used(BudgetDimension::Requests)),
        limit(BudgetDimension::Requests),
        format_count(used(BudgetDimension::Tokens)),
        limit(BudgetDimension::Tokens),
    )
}

fn now_millis() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|duration| duration.as_millis() as u64)
        .unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The arguments reach the compiled core and map to the session's
    /// types: a budgeted goal, named limits (the others unlimited) with a
    /// gate, a usage error.
    #[test]
    fn slash_arguments_map_to_session_commands() {
        assert_eq!(
            parse_goal_command("--budget 5000 keep going"),
            Ok(GoalCommand::Start {
                objective: "keep going".to_string(),
                token_budget: Some(5000),
            })
        );
        assert_eq!(
            parse_autonomous_command("on --max-turns 5 --gate=ls"),
            Ok(AutonomousCommand::On {
                config: AgentAutonomousConfig {
                    max_continuations: Some(UNLIMITED_AUTONOMOUS_LIMIT),
                    max_turns: Some(5),
                    max_tokens: Some(UNLIMITED_AUTONOMOUS_LIMIT),
                    timeout_ms: Some(UNLIMITED_AUTONOMOUS_LIMIT),
                    gates: Some(AgentAutonomousGateConfig {
                        commands: Some(vec!["ls".to_string()]),
                        max_retries: None,
                        timeout_ms: None,
                    }),
                    ..AgentAutonomousConfig::default()
                },
            })
        );
        assert!(parse_autonomous_command("bogus")
            .is_err_and(|error| error.text.starts_with("Usage: /autonomous [status|off]")));
    }

    /// The turns, tokens and time are the session budget's; without one
    /// they are unlimited.
    #[test]
    fn autonomous_status_format() {
        let state = crate::autonomous::create_autonomous_runtime_state(None, None);
        let budget = eukhe_types::budget::BudgetReport {
            limits: eukhe_types::budget::BudgetLimits {
                tokens: Some(80_000),
                time_ms: Some(1_800_000),
                requests: Some(12),
                ..Default::default()
            },
            spent: eukhe_types::budget::BudgetAmounts {
                tokens: 1_500,
                requests: 2,
                ..Default::default()
            },
            free: eukhe_types::budget::BudgetAmounts {
                tokens: 78_500,
                time_ms: 1_740_000,
                requests: 10,
                ..Default::default()
            },
            ..Default::default()
        };
        let status = |budget| {
            format_autonomous_status(&crate::autonomous::autonomous_status(&state, budget))
        };
        assert_eq!(
            [status(Some(budget)), status(None)],
            [
                "[autonomous-status: off]\n\nContinuations: 0/3. Turns: 2/12. Tokens: 1,500/80,000. Time: 60s/1,800s. Gates: none. Subagent keep-alive: 25m.",
                "[autonomous-status: off]\n\nContinuations: 0/3. Turns: 0/unlimited. Tokens: 0/unlimited. Time: 0s/unlimited. Gates: none. Subagent keep-alive: 25m.",
            ]
            .map(str::to_owned)
        );
    }
}
