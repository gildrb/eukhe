//! `eukhe.acceptance`: verified completion on the durable Harness. "Done"
//! is a claim; the harness reports it as success only when every
//! acceptance check was confirmed on the final state.
//!
//! The acceptance of a conversation lives in its `eukhe.acceptance`
//! document: the checks its owner set (a command with an expected exit
//! code, a condition an independent judge decides on evidence, a loop's
//! until-condition, the task's intent an independent judge decides from
//! the user's own messages), each check's last verdict with what the
//! harness observed, the pending claim and the returns in a row. A
//! verdict judges one state: the newest effect, the newest user message
//! and the workspace's fingerprint (`workspace.rs`). The owner (the
//! user's `/accept`, an SDK client's [`set_acceptance`] or the daemon's
//! `set_acceptance` command, the CLI's `--accept-*` flags, a parent's
//! spawn) sets the checks; the worker claims (a final answer,
//! or `goal.complete()` under an active goal) and can read its checks
//! (`acceptance.get`), never change them; the verifier (the
//! `pi.generation` `on_yield` hook) gathers the evidence, records the
//! verdicts and reports the result. Every decision is the compiled core's
//! (`eukhe_bend::rules::verify`, `laws/verify.bend`).
//! [`watch_acceptance_updates`] feeds the `acceptance_update` event.

mod command;
mod docs;
mod evidence;
mod host;
mod ops;
mod verifier;
mod watch;
mod workspace;

#[cfg(test)]
mod tests;

use std::sync::{Arc, Weak};

use eukhe_durable::harness::define::define_extension;
use eukhe_durable::harness::types::Extension;

pub use command::format_acceptance_status;
pub(crate) use command::{parse_accept_command, AcceptCommand, ACCEPT_USAGE};
pub use evidence::{Judge, JudgeQuestion, JudgeReply, JudgeRequest};
pub use ops::{acceptance_exit_code, acceptance_state, seed_acceptance, set_acceptance};
pub(crate) use ops::{claim, Claimed};
pub(crate) use verifier::describe;
pub use watch::{watch_acceptance_updates, AcceptanceUpdates};

use self::evidence::{Gatherer, ModelJudge};
use self::verifier::Verifier;
use super::HostDeps;
use crate::autonomous::{GateCommandRunner, ShellGateRunner};
use crate::durable::{HarnessCell, HostRequestRegistry};

/// The extension's name.
pub const ACCEPTANCE_EXTENSION: &str = "eukhe.acceptance";

/// The `customType` of a verdict's display row: how a claim ended, or
/// that it went back to the worker, with the checks, their verdicts and
/// their evidence in its details. Display-only, never model context.
pub const ACCEPTANCE_CUSTOM_TYPE: &str = "eukhe.acceptance";

/// The acceptance extension of one session: the verifier's
/// `pi.generation` hooks and the `acceptance.get` / `acceptance.set` host
/// requests registered in `deps.host_requests`. Checks run in the session
/// cwd; a judge is one request to the session's models. It installs
/// before `eukhe.goals`: the first continuation of a final answer wins,
/// and a refuted claim's evidence goes ahead of any other continuation.
#[must_use]
pub fn extension(deps: &Arc<HostDeps>) -> Arc<Extension> {
    acceptance_extension(
        deps.harness.clone(),
        Arc::new(ShellGateRunner::new(deps.cwd.clone())),
        Arc::new(ModelJudge {
            harness: deps.harness.clone(),
            models: deps.models.clone(),
        }),
        deps.cwd.clone(),
        &deps.host_requests,
        Some(Arc::downgrade(deps)),
    )
}

/// [`extension`] over explicit services (the command runner and the judge
/// are the seams the tests script).
pub(crate) fn acceptance_extension(
    harness: HarnessCell,
    runner: Arc<dyn GateCommandRunner>,
    judge: Arc<dyn Judge>,
    cwd: std::path::PathBuf,
    host_requests: &HostRequestRegistry,
    deps: Option<Weak<HostDeps>>,
) -> Arc<Extension> {
    host::register_host_requests(&harness, cwd.clone(), host_requests);
    let verifier = Verifier {
        harness: harness.clone(),
        gatherer: Gatherer {
            harness,
            runner,
            judge,
            cwd,
        },
        deps,
    };
    define_extension(Extension {
        name: ACCEPTANCE_EXTENSION.to_owned(),
        hooks: vec![verifier::generation_hooks(&verifier)],
        ..Extension::default()
    })
}
