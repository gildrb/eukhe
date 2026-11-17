//! Session slash-command arguments and status formatting for `/auto`
//! (typed as `/auto`, `/autonomous` or the removed `/goal`). The arguments
//! are the compiled core's (`eukhe_bend::rules::slash_args`,
//! `laws/slash_args/`): this module maps its answers to the session's
//! types. The status text is a port of agent-session.ts
//! `_formatAutonomousStatus`; its strings are user-facing and
//! byte-identical.

use eukhe_bend::rules::slash_args::{self, AutoArgs, AutoName, AutoVia, Limit};

use crate::autonomous::{
    AgentAutonomousConfig, AgentAutonomousGateConfig, AgentAutonomousStatus,
    UNLIMITED_AUTONOMOUS_LIMIT,
};

/// The compiled core's refusal of an `/auto` argument string: its usage
/// text, shown as the core wrote it.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("{text}")]
pub struct SlashArgsRefusal {
    /// The core's usage text.
    pub text: String,
}

/// A parsed `/auto` argument string.
#[derive(Debug, Clone, PartialEq)]
pub enum AutonomousCommand {
    Status,
    On {
        config: AgentAutonomousConfig,
    },
    Off,
    /// Turn autonomous mode on, then send `text` as the user's message.
    Task {
        text: String,
        /// `/goal --budget N`: the run's token budget.
        token_budget: Option<u64>,
    },
}

/// What `/auto` asks, and how it was typed.
#[derive(Debug, Clone, PartialEq)]
pub struct AutoCommand {
    /// [`AutoVia::GoalAlias`]: typed as the removed `/goal`.
    pub via: AutoVia,
    /// The command, or the core's usage text.
    pub command: Result<AutonomousCommand, SlashArgsRefusal>,
}

/// Parse `/auto [status|off|on [--max-continuations <n>] ...|<task>]`, typed
/// as `name` (`/goal` maps each of its old forms to the `/auto` one).
#[must_use]
pub fn parse_auto_command(name: AutoName, args: &str) -> AutoCommand {
    let reply = slash_args::auto(name, args);
    AutoCommand {
        via: reply.via,
        command: command(reply.args),
    }
}

/// The session's command for the core's answer.
fn command(args: AutoArgs) -> Result<AutonomousCommand, SlashArgsRefusal> {
    match args {
        AutoArgs::Status => Ok(AutonomousCommand::Status),
        AutoArgs::Off => Ok(AutonomousCommand::Off),
        AutoArgs::Task { text, token_budget } => Ok(AutonomousCommand::Task { text, token_budget }),
        AutoArgs::Error(text) => Err(SlashArgsRefusal { text }),
        AutoArgs::On(options) => Ok(AutonomousCommand::On {
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

/// The `[autonomous-status: ...]` block: on or off, the continuations the
/// run made, why the last run stopped; the limits are the run's budget and
/// the checks the run's acceptance checks.
#[must_use]
pub fn format_autonomous_status(status: &AgentAutonomousStatus) -> String {
    let state = if status.enabled { "on" } else { "off" };
    let stop = status
        .last_stop
        .map(|stop| format!(" Last stop: {}.", stop.describe(status.budget.as_ref())))
        .unwrap_or_default();
    format!(
        "[autonomous-status: {state}]\n\nContinuations: {}.{stop} Limits: /budget. Checks: /accept status.",
        format_count(status.continuations_used),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The arguments reach the compiled core and map to the session's
    /// types: a task, `/goal`'s budgeted objective as a task flagged as the
    /// alias, `/goal resume` as `on`, `/autonomous on` with named limits
    /// (the others unlimited) and a gate, a usage error.
    #[test]
    fn slash_arguments_map_to_session_commands() {
        let task = |text: &str, token_budget| {
            Ok(AutonomousCommand::Task {
                text: text.to_string(),
                token_budget,
            })
        };
        let parsed = |via, command| AutoCommand { via, command };
        assert_eq!(
            [
                parse_auto_command(AutoName::Auto, "ship it"),
                parse_auto_command(AutoName::Goal, "--budget 5000 keep going"),
                parse_auto_command(AutoName::Goal, "resume"),
                parse_auto_command(AutoName::Autonomous, "on --max-turns 5 --gate=ls"),
            ],
            [
                parsed(AutoVia::Auto, task("ship it", None)),
                parsed(AutoVia::GoalAlias, task("keep going", Some(5000))),
                parsed(
                    AutoVia::GoalAlias,
                    Ok(AutonomousCommand::On {
                        config: AgentAutonomousConfig::default(),
                    })
                ),
                parsed(
                    AutoVia::Auto,
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
                ),
            ]
        );
        assert!(parse_auto_command(AutoName::Auto, "status now")
            .command
            .is_err_and(|error| error.text.starts_with(
                "Unexpected autonomous argument: now. Usage: /auto [status|off|<task>]"
            )));
    }

    /// The run's state, its continuations and its last stop; limits and
    /// checks name their commands.
    #[test]
    fn autonomous_status_format() {
        let status = |enabled, last_stop| {
            format_autonomous_status(&AgentAutonomousStatus {
                enabled,
                continuations_used: 1_200,
                started_at: None,
                last_stop,
                budget: None,
            })
        };
        assert_eq!(
            [
                status(true, None),
                status(
                    false,
                    Some(crate::autonomous::AutonomousStop::Checks(
                        eukhe_types::acceptance::AcceptanceLabel::Failed
                    ))
                ),
                status(false, Some(crate::autonomous::AutonomousStop::Budget)),
            ],
            [
                "[autonomous-status: on]\n\nContinuations: 1,200. Limits: /budget. Checks: /accept status.",
                "[autonomous-status: off]\n\nContinuations: 1,200. Last stop: the checks ended the claim: failed. Limits: /budget. Checks: /accept status.",
                "[autonomous-status: off]\n\nContinuations: 1,200. Last stop: the run's work budget is used up. Limits: /budget. Checks: /accept status.",
            ]
            .map(str::to_owned)
        );
    }
}
