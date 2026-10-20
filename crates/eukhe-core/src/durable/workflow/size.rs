//! The limits a run works under: the size's, with the concurrency capped
//! by `subagentMaxConcurrency` (the family-wide spawn cap, which refuses a
//! spawn over it).

use eukhe_types::workflow::{WorkflowLimits, WorkflowSize};

/// The limits of a run of `size` in a session whose
/// `subagentMaxConcurrency` is `subagent_max_concurrency` (`0`:
/// unlimited): the size's concurrency, at most the cap, and the size's
/// `max_agents`.
#[must_use]
pub fn effective_limits(size: WorkflowSize, subagent_max_concurrency: u32) -> WorkflowLimits {
    let limits = size.limits();
    let concurrency = match subagent_max_concurrency {
        0 => limits.concurrency,
        cap => limits.concurrency.min(cap),
    };
    WorkflowLimits {
        concurrency,
        max_agents: limits.max_agents,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_zero_cap_keeps_the_size_and_a_smaller_cap_bounds_it() {
        assert_eq!(
            effective_limits(WorkflowSize::Large, 0),
            WorkflowLimits {
                concurrency: 12,
                max_agents: 25
            }
        );
        assert_eq!(
            effective_limits(WorkflowSize::Medium, 4),
            WorkflowLimits {
                concurrency: 4,
                max_agents: 10
            }
        );
        assert_eq!(
            effective_limits(WorkflowSize::Small, 8),
            WorkflowLimits {
                concurrency: 3,
                max_agents: 5
            }
        );
    }
}
