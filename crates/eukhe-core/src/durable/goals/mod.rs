//! `eukhe.goals`: thread goals and autonomous continuation on the durable
//! Harness (the goal driver and boundary, `crate::goals`' engine half,
//! and the daemon's goal/autonomous continuation loops).
//!
//! State lives in conversation documents (`eukhe.goal`, `eukhe.autonomous`,
//! and the hooks' bookkeeping `eukhe.goal.loop`); the `pi.generation` hooks
//! drive continuation; the kernel's `goal.*` host requests and the `/goal`
//! / `/autonomous` operations mutate the documents through commits. A
//! goal counts what it spends against its token budget; a goal and an
//! autonomous run stop when the session's budget
//! (`crate::durable::budget`) admits no more work. [`watch_goal_updates`] feeds the `goal_update`
//! event.

mod autonomous;
mod docs;
mod hooks;
mod host;
mod observer;
mod ops;
mod state;
mod watch;

#[cfg(test)]
pub(crate) mod tests;

use std::sync::Arc;

use eukhe_durable::harness::define::define_extension;
use eukhe_durable::harness::types::{Extension, HookRegistration};

pub(crate) use autonomous::set_internal_autonomous;
pub use autonomous::{
    autonomous_state, configure_autonomous, set_autonomous, set_run_limits, AutonomousChange,
    AutonomousDocState,
};
pub(crate) use docs::{open_doc, read_doc, write_doc};
pub use docs::{AUTONOMOUS_DOC, GOAL_DOC};
pub use ops::{
    budget_report, clear_goal, complete_goal, continue_goal_after_compaction, goal_state,
    import_legacy_goal, pause_goal, resume_goal, seed_initial_goal, start_goal,
    withdraw_queued_goal_contexts,
};
pub(crate) use ops::{conversation_of, end_claimed_goal, user_input_queued, ClaimEnd};
pub use state::{
    creation_elapsed_seconds, owns_continuation_wakeup, served, terminal_provider_failure,
};
pub use watch::{watch_goal_updates, GoalUpdates};

use self::host::{register_host_requests, GoalsHost};
use super::acceptance::{answer_judge, Judge};
use super::budget::BudgetGate;
use super::directors::{pending_work_hook, DirectorLimits};
use super::HostDeps;
use crate::durable::{HarnessCell, HostRequestRegistry};

/// The extension's name.
pub const GOALS_EXTENSION: &str = "eukhe.goals";

/// The goal extension of one session: the `pi.generation` hooks (with the
/// Director stack's step, its limits from the `directors` settings, the
/// final-answer judge, and the `PendingWork` fact of the run loop's stop
/// Directors), the `goal.get` / `goal.create` / `goal.complete` /
/// `directors.push` host requests registered in `deps.host_requests`, and
/// the run-end failure observer. The `autoresearch.*` host
/// requests register here too: their loop is the autonomous run.
#[must_use]
pub fn extension(deps: &Arc<HostDeps>) -> Arc<Extension> {
    observer::install(deps);
    crate::autoresearch::register_host_requests(deps);
    let settings = Arc::clone(&deps.settings);
    goals_extension(
        deps.harness.clone(),
        Arc::clone(&deps.budget),
        Arc::new(move || DirectorLimits::of(settings.manager().settings())),
        answer_judge(deps.harness.clone(), deps.models.clone()),
        &deps.host_requests,
        vec![pending_work_hook(deps)],
    )
}

/// [`extension`] over explicit services (the budget, the limits and the
/// final-answer judge are the seams the tests script); `beside` registers
/// after the goal's hooks.
pub(crate) fn goals_extension(
    harness: HarnessCell,
    budget: Arc<BudgetGate>,
    limits: Arc<dyn Fn() -> DirectorLimits + Send + Sync>,
    judge: Arc<dyn Judge>,
    host_requests: &HostRequestRegistry,
    beside: Vec<HookRegistration>,
) -> Arc<Extension> {
    let host = GoalsHost {
        harness,
        budget,
        limits,
        judge,
        work: Arc::default(),
    };
    register_host_requests(&host, host_requests);
    let mut hooks = vec![hooks::generation_hooks(&host)];
    hooks.extend(beside);
    define_extension(Extension {
        name: GOALS_EXTENSION.to_owned(),
        hooks,
        ..Extension::default()
    })
}
