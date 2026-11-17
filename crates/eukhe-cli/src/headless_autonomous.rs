//! The autonomous run of headless print/json/rpc runs: the CLI flags turn
//! the run on for the session's main conversation. Its checks are the
//! `--accept-*` checks (the intent check when none is given) and its
//! limits the `--budget-*` limits; its stop surfaces through them (the
//! checks' label and exit, the budget line).

use eukhe_core::autonomous::AgentAutonomousConfig;

use crate::args::AutonomousConfig;

/// The autonomous configuration of the CLI flags: on, with the checks'
/// return cap the removed `--autonomous-max-continuations` or
/// `--autonomous-gate-retries` asked.
pub fn autonomous_runtime_config(config: &AutonomousConfig) -> AgentAutonomousConfig {
    AgentAutonomousConfig {
        enabled: Some(true),
        max_continuations: config.returns.map(u64::from),
        ..AgentAutonomousConfig::default()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_flags_turn_the_run_on_with_their_return_cap() {
        assert_eq!(
            autonomous_runtime_config(&AutonomousConfig { returns: Some(2) }),
            AgentAutonomousConfig {
                enabled: Some(true),
                max_continuations: Some(2),
                ..AgentAutonomousConfig::default()
            }
        );
    }
}
