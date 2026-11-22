//! `eukhe.autonomous`: the autonomous run and the Director stack's loop on
//! the durable Harness.
//!
//! State lives in conversation documents (`eukhe.autonomous`, the
//! Director stack `eukhe.directors`, and the hooks' bookkeeping
//! `eukhe.goal.loop`, a kind name kept for the sessions that hold it); the
//! `pi.generation` hooks drive continuation; `/auto` and the
//! `directors.push` host request change the documents through commits. An
//! autonomous run stops at its checks, when the session's budget
//! (`crate::durable::budget`) admits no more work, or when its
//! continuations make no progress.

mod docs;
mod hooks;
mod host;
mod ops;
mod run;

#[cfg(test)]
pub(crate) mod tests;

use std::sync::Arc;

use eukhe_durable::harness::define::define_extension;
use eukhe_durable::harness::types::{Extension, HookRegistration};

pub use docs::AUTONOMOUS_DOC;
pub(crate) use docs::{open_doc, read_doc, write_doc};
pub use ops::budget_report;
pub(crate) use ops::{conversation_of, user_input_queued};
pub(crate) use run::set_internal_autonomous;
pub use run::{
    autonomous_state, configure_autonomous, set_autonomous, set_run_limits, AutonomousChange,
    AutonomousDocState,
};

use self::host::{register_host_requests, AutonomousHost};
use super::budget::BudgetGate;
use super::directors::{pending_work_hook, DirectorLimits};
use super::HostDeps;
use crate::durable::{HarnessCell, HostRequestRegistry};

/// The extension's name.
pub const AUTONOMOUS_EXTENSION: &str = "eukhe.autonomous";

/// The autonomous extension of one session: the `pi.generation` hooks
/// (with the Director stack's step, its limits from the `directors`
/// settings, and the `PendingWork` fact of the run loop's stop
/// Directors) and the `directors.push` host request registered in
/// `deps.host_requests`. The `autoresearch.*` host requests register here
/// too: their loop is the autonomous run.
#[must_use]
pub fn extension(deps: &Arc<HostDeps>) -> Arc<Extension> {
    crate::autoresearch::register_host_requests(deps);
    let settings = Arc::clone(&deps.settings);
    autonomous_extension(
        deps.harness.clone(),
        Arc::clone(&deps.budget),
        Arc::new(move || DirectorLimits::of(settings.manager().settings())),
        &deps.host_requests,
        vec![pending_work_hook(deps)],
    )
}

/// [`extension`] over explicit services (the budget and the limits are
/// the seams the tests script); `beside` registers after the run's hooks.
pub(crate) fn autonomous_extension(
    harness: HarnessCell,
    budget: Arc<BudgetGate>,
    limits: Arc<dyn Fn() -> DirectorLimits + Send + Sync>,
    host_requests: &HostRequestRegistry,
    beside: Vec<HookRegistration>,
) -> Arc<Extension> {
    let host = AutonomousHost {
        harness,
        budget,
        limits,
        work: Arc::default(),
    };
    register_host_requests(&host, host_requests);
    let mut hooks = vec![hooks::generation_hooks(&host)];
    hooks.extend(beside);
    define_extension(Extension {
        name: AUTONOMOUS_EXTENSION.to_owned(),
        hooks,
        ..Extension::default()
    })
}
