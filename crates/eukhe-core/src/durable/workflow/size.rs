//! The limits a run works under: the size's, with the concurrency capped
//! by `subagentMaxConcurrency` (the family-wide spawn cap, which refuses a
//! spawn over it). The rule is the Bend model's `effective`
//! (`bend/workflow.bend`, laws `wf_limits_uncapped` and `wf_limits_capped`),
//! run by the compiled core.

use eukhe_bend::wire::{Reader, Writer};
use eukhe_bend::{expect_core, Entry};
use eukhe_types::workflow::{WorkflowLimits, WorkflowSize};

/// The limits of a run of `size` in a session whose
/// `subagentMaxConcurrency` is `subagent_max_concurrency` (`0`:
/// unlimited): the size's concurrency, at most the cap, and the size's
/// `max_agents`.
#[must_use]
pub fn effective_limits(size: WorkflowSize, subagent_max_concurrency: u32) -> WorkflowLimits {
    let limits = size.limits();
    let decided = (|| -> Result<WorkflowLimits, eukhe_bend::Error> {
        let request = Writer::new()
            .tag(1)
            .u32(limits.concurrency)
            .u32(limits.max_agents)
            .u32(subagent_max_concurrency)
            .finish()?;
        let reply = eukhe_bend::call(Entry::Workflow, &request)?;
        let mut reader = Reader::reply(&reply)?;
        let concurrency = reader.u32()?;
        let max_agents = reader.u32()?;
        reader.end()?;
        Ok(WorkflowLimits {
            concurrency,
            max_agents,
        })
    })();
    expect_core(Entry::Workflow, decided)
}
