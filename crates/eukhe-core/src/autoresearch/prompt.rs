//! The `autoresearch` system prompt section (omp `prompt-setup.md` and
//! `prompt.md`): the mode's instructions live in the system prompt, not
//! in a user message. `/autoresearch <goal>` sends the goal alone as the
//! user's message; while the loop's autonomous run is on in a
//! conversation and the Lab's mode is on, each of its requests carries
//! the setup phase (no experiment yet: build and validate the harness,
//! init, baseline) or the loop phase (the experiment's goal, metric and
//! branch; iterate). Like every section, it is recorded as a positional
//! `pi.system` entry, so a resume or replay gives the model the same view,
//! and no transcript shows it.

use std::sync::Arc;

use eukhe_bend::rules::autoresearch::{Direction, Mode, Snapshot};
use eukhe_durable::harness::define::section as define_section;
use eukhe_durable::harness::types::{PromptInput, PromptSection};
use eukhe_durable::session::SessionError;
use futures::FutureExt;

use super::host::{of, ours};
use crate::durable::goals::autonomous_state;
use crate::durable::HostDeps;

/// The section's key (its tag in the prompt).
pub(crate) const SECTION: &str = "autoresearch";

/// The Lab could not be read for the section.
#[derive(Debug, thiserror::Error)]
#[error("autoresearch prompt: {0:#}")]
struct SectionError(anyhow::Error);

/// The `autoresearch` section of a session's requests: present only in a
/// conversation the loop runs in (its autonomous run on with the loop's
/// continuation), so a session that never used autoresearch reads one
/// document per request and touches neither git nor the Lab's store.
pub(crate) fn section(deps: &Arc<HostDeps>) -> Arc<PromptSection> {
    let deps = Arc::downgrade(deps);
    define_section(
        SECTION,
        move |input: &PromptInput, cx| {
            let deps = deps.upgrade();
            let read = Arc::clone(&input.read);
            let conversation = input.conversation_id;
            let cx = cx.clone();
            async move {
                let Some(deps) = deps else {
                    return Ok(None);
                };
                if !ours(&autonomous_state(&*read, conversation, &cx).await?) {
                    return Ok(None);
                }
                let (snapshot, branch) = of(&deps)
                    .view()
                    .await
                    .map_err(|error| SessionError::other(SectionError(error)))?;
                Ok(text(&snapshot, branch.as_deref()))
            }
            .boxed()
        },
        None,
    )
}

/// The section's text for the Lab's `snapshot` on `branch`: `None` while
/// the mode is off. It holds nothing that changes between runs, so the
/// loop's requests keep one recorded section.
pub(crate) fn text(snapshot: &Snapshot, branch: Option<&str>) -> Option<String> {
    if snapshot.mode != Mode::On {
        return None;
    }
    let branch = branch.map_or_else(String::new, |branch| format!(" Branch: `{branch}`."));
    Some(match &snapshot.config {
        None => format!(
            "Autoresearch mode is on and this branch has no experiment yet.{branch} The user's \
message that turned the mode on is the goal. Build the benchmark harness that measures it; \
optimisation starts only after `autoresearch.init`.\n\nFollow the autoresearch skill. Write \
`autoresearch.sh` in the repository root (exit 0 on success, a deterministic workload, one \
`METRIC <name>=<value>` line for the primary metric), validate it with `bash autoresearch.sh`, \
then call `await autoresearch.init(...)` with the goal and run the baseline."
        ),
        Some(config) => {
            let unit = if config.unit.is_empty() {
                String::new()
            } else {
                format!(" ({})", config.unit)
            };
            let better = match config.direction {
                Direction::Lower => "lower",
                Direction::Higher => "higher",
            };
            let cap = config.max_iterations.map_or_else(String::new, |max| {
                format!(" The iteration cap is {max} runs.")
            });
            format!(
                "Autoresearch mode is on: experiment `{name}`.{branch} Goal: {goal}\n\nPrimary \
metric `{metric}`{unit}, {better} is better.{cap}\n\nFollow the autoresearch skill. `await \
autoresearch.state()` is the source of truth for the goal, scope, runs and notes; inspect recent \
git history for context. Log a pending run before you run again. Continue the most promising \
unfinished direction and keep iterating until the user stops you or the iteration cap is \
reached. Preserve correctness; never game the benchmark.",
                name = config.name,
                goal = config.goal,
                metric = config.metric,
            )
        }
    })
}
