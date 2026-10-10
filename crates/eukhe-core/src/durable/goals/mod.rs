//! `eukhe.goals`: thread goals and autonomous continuation on the durable
//! Harness (port of `session_engine/{goal_driver, goal_boundary}`,
//! `crate::goals`' engine half, and the daemon's goal/autonomous
//! continuation loops).
//!
//! State lives in conversation documents (`eukhe.goal`, `eukhe.autonomous`,
//! and the hooks' bookkeeping `eukhe.goal.loop`); the `pi.generation` hooks
//! drive accounting and continuation; the kernel's `goal.*` host requests
//! and the `/goal` / `/autonomous` operations mutate the documents through
//! commits. [`watch_goal_updates`] feeds the `goal_update` event.

mod autonomous;
mod docs;
mod hooks;
mod host;
mod ops;
mod state;
mod watch;

#[cfg(test)]
mod tests;

use std::sync::Arc;

use eukhe_durable::harness::define::define_extension;
use eukhe_durable::harness::types::Extension;

pub use autonomous::{
    autonomous_state, set_autonomous, AutonomousChange, AutonomousDocState, AutonomousStop,
    WorktreeSnapshot,
};
pub use docs::{AUTONOMOUS_DOC, GOAL_DOC};
pub use ops::{
    clear_goal, complete_goal, goal_state, import_legacy_goal, is_goal_nudge, pause_goal,
    resume_goal, seed_initial_goal, start_goal, withdraw_queued_goal_contexts,
};
pub use state::{
    creation_elapsed_seconds, owns_continuation_wakeup, served, terminal_provider_failure,
    turn_produced_no_output, NO_PROGRESS_CAP_REASON,
};
pub use watch::{watch_goal_updates, GoalUpdates};

use self::host::{register_host_requests, GoalsHost};
use super::HostDeps;
use crate::autonomous::{GateCommandRunner, ShellGateRunner};
use crate::durable::{HarnessCell, HostRequestRegistry};

/// The extension's name.
pub const GOALS_EXTENSION: &str = "eukhe.goals";

/// The goal extension of one session: the `pi.generation` hooks, and the
/// `goal.get` / `goal.create` / `goal.complete` host requests registered in
/// `deps.host_requests`. Autonomous gates run in the session cwd.
#[must_use]
pub fn extension(deps: &Arc<HostDeps>) -> Arc<Extension> {
    goals_extension(
        deps.harness.clone(),
        Arc::new(ShellGateRunner::new(deps.cwd.clone())),
        &deps.host_requests,
    )
}

/// [`extension`] over explicit services (the gate runner is the seam the
/// tests script).
pub(crate) fn goals_extension(
    harness: HarnessCell,
    gates: Arc<dyn GateCommandRunner>,
    host_requests: &HostRequestRegistry,
) -> Arc<Extension> {
    let host = GoalsHost { harness, gates };
    register_host_requests(&host, host_requests);
    define_extension(Extension {
        name: GOALS_EXTENSION.to_owned(),
        hooks: vec![hooks::generation_hooks(&host)],
        ..Extension::default()
    })
}
