//! The autonomous run of headless print/json/rpc runs -- the verifier and
//! eval composition surface. CLI autonomous flags enable the run on the
//! session's main conversation (TS `runtimeAutonomousConfigFromArgs`); the
//! durable `eukhe.goals` extension accounts usage, runs the gate commands,
//! and drives continuations. A stop surfaces only through the process exit
//! code and its stderr line (the TS print-mode contract, `print-mode.ts`).

use eukhe_core::autonomous::{
    autonomous_limit_reason, autonomous_status, describe_autonomous_limit,
    latest_autonomous_gate_attempt, now_millis, AgentAutonomousConfig, AutonomousRuntimeState,
};

use crate::args::AutonomousConfig;

/// The autonomous runtime config from the typed CLI flags (TS
/// `runtimeAutonomousConfigFromArgs`: any autonomous flag enables the run).
pub fn autonomous_runtime_config(config: &AutonomousConfig) -> AgentAutonomousConfig {
    AgentAutonomousConfig {
        enabled: Some(true),
        max_continuations: config.max_continuations.map(u64::from),
        max_turns: config.max_turns.map(u64::from),
        max_tokens: config.max_tokens,
        timeout_ms: config.timeout_ms,
        continuation_prompt: None,
        gates: config.gates.as_ref().map(|gates| {
            eukhe_core::autonomous::AgentAutonomousGateConfig {
                commands: Some(gates.commands.clone()),
                max_retries: gates.max_retries.map(u64::from),
                timeout_ms: gates.timeout_ms,
            }
        }),
        subagent_keep_alive_ms: None,
    }
}

/// The TS print-mode exit contract: stderr text when the run must exit
/// non-zero -- a configured gate still failing (after its retry window, or
/// with an autonomous limit reached), or an autonomous run without gates
/// that stopped before terminal evidence.
pub fn autonomous_exit_stderr(state: &AutonomousRuntimeState) -> Option<String> {
    let status = autonomous_status(state);
    let now = now_millis();
    let limit = autonomous_limit_reason(state, now);
    if let Some(failure) = status
        .last_gate_failure
        .as_ref()
        .filter(|_| status.enabled && !status.gates.commands.is_empty())
    {
        let limit_text = limit
            .map(|reason| {
                format!(
                    "; autonomous limit reached: {}",
                    describe_autonomous_limit(&status, reason, now)
                )
            })
            .unwrap_or_default();
        return Some(format!(
            "Autonomous quality gate still failing after attempt {}/{}: {}{}",
            latest_autonomous_gate_attempt(&status),
            status.gates.max_retries,
            failure.exit_text,
            limit_text
        ));
    }
    if status.enabled && status.gates.commands.is_empty() {
        if let Some(reason) = limit {
            return Some(format!(
                "Autonomous run stopped before terminal evidence; {}",
                describe_autonomous_limit(&status, reason, now)
            ));
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use eukhe_core::autonomous::{
        add_autonomous_continuation, create_autonomous_runtime_state, AgentAutonomousGateFailure,
    };

    #[test]
    fn a_disabled_run_exits_clean() {
        let state = create_autonomous_runtime_state(None, None);
        assert_eq!(autonomous_exit_stderr(&state), None);
    }

    #[test]
    fn a_gateless_run_at_its_limit_stopped_before_terminal_evidence() {
        let config = autonomous_runtime_config(&AutonomousConfig {
            max_continuations: Some(1),
            ..AutonomousConfig::default()
        });
        let mut state = create_autonomous_runtime_state(Some(&config), None);
        assert_eq!(autonomous_exit_stderr(&state), None);
        add_autonomous_continuation(&mut state);
        let stderr = autonomous_exit_stderr(&state).expect("the limit stops the run");
        assert!(
            stderr.starts_with("Autonomous run stopped before terminal evidence; "),
            "{stderr}"
        );
    }

    #[test]
    fn a_failing_gate_reports_its_attempt() {
        let config = autonomous_runtime_config(&AutonomousConfig {
            gates: Some(crate::args::AutonomousGates {
                commands: vec!["false".to_owned()],
                max_retries: Some(2),
                timeout_ms: None,
            }),
            ..AutonomousConfig::default()
        });
        let mut state = create_autonomous_runtime_state(Some(&config), None);
        state.gate_attempts.insert("false".to_owned(), 1);
        state.last_gate_failure = Some(AgentAutonomousGateFailure {
            command: "false".to_owned(),
            attempt: 1,
            exit_text: "exit 1".to_owned(),
            output: String::new(),
        });
        let stderr = autonomous_exit_stderr(&state).expect("the gate still fails");
        assert!(
            stderr.starts_with("Autonomous quality gate still failing after attempt 1/2: exit 1"),
            "{stderr}"
        );
    }
}
