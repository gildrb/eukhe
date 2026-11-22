//! Session slash-command arguments and status formatting for `/auto`
//! (typed as `/auto` or `/autonomous`) and the pointer the removed `/goal`
//! answers. The arguments are the compiled core's
//! (`eukhe_bend::rules::slash_args`, `laws/slash_args/`): this module maps
//! its answers to the session's types. The status text is a port of
//! agent-session.ts `_formatAutonomousStatus`; its strings are user-facing
//! and byte-identical.

use eukhe_bend::rules::slash_args::{self, AutoArgs, AutoName, Limit};

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
    },
}

/// Parse `/auto [status|off|on [--max-continuations <n>] ...|<task>]`, typed
/// as `name`: the command, or the core's usage text.
///
/// # Errors
///
/// The core's refusal of `args`.
pub fn parse_auto_command(
    name: AutoName,
    args: &str,
) -> Result<AutonomousCommand, SlashArgsRefusal> {
    command(slash_args::auto(name, args))
}

/// What the removed `/goal` answers, whatever its arguments: the core's
/// pointer to `/auto`.
#[must_use]
pub fn goal_pointer(args: &str) -> String {
    slash_args::goal_pointer(args)
}

/// The session's command for the core's answer.
fn command(args: AutoArgs) -> Result<AutonomousCommand, SlashArgsRefusal> {
    match args {
        AutoArgs::Status => Ok(AutonomousCommand::Status),
        AutoArgs::Off => Ok(AutonomousCommand::Off),
        AutoArgs::Task { text } => Ok(AutonomousCommand::Task { text }),
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
    /// types: a task, `/autonomous on` with named limits (the others
    /// unlimited) and a gate, a usage error; the removed `/goal` answers
    /// only its pointer, whatever it is given.
    #[test]
    fn slash_arguments_map_to_session_commands() {
        assert_eq!(
            [
                parse_auto_command(AutoName::Auto, "ship it"),
                parse_auto_command(AutoName::Autonomous, "on --max-turns 5 --gate=ls"),
            ],
            [
                Ok(AutonomousCommand::Task {
                    text: "ship it".to_string(),
                }),
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
                }),
            ]
        );
        assert!(
            parse_auto_command(AutoName::Auto, "status now").is_err_and(|error| error
                .text
                .starts_with(
                    "Unexpected autonomous argument: now. Usage: /auto [status|off|<task>]"
                ))
        );
        for args in ["", "--budget 5000 ship it", "resume", "status"] {
            assert_eq!(goal_pointer(args), "/goal is removed: use /auto");
        }
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
