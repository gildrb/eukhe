//! The resumed-session kernel-state notice (`ipython_state_restored`).
//!
//! A resumed session, or a kernel killed to stop a cell, spawns a fresh
//! Python kernel. The kernel's namespace snapshot (the dill payload in the
//! session's artifact dir) revives the earlier names, and the
//! provisioner's `on_restore` seam reports the outcome here. A full revival
//! changes nothing the model relies on, so it owes no notice; only lost
//! state (a fresh kernel, or names that failed to revive) is told, BEFORE
//! the first turn, so the model re-creates it instead of discovering the
//! gap a turn later.
//!
//! Relationship to the compaction notice (`ipython_state`, #230): two
//! separate surfaces, one shared snapshot machinery. `ipython_state` fires
//! after a compaction on a kernel that SURVIVED the compaction (same
//! process, live namespace, pruning disclosure); `ipython_state_restored`
//! fires when a NEW kernel booted and revived the namespace from disk (a
//! resume, or a fresh session opened over a snapshot-carrying artifact
//! dir). Both read the same per-session snapshot dir and the same
//! `snapshot`/`list_names` kernel requests, but the compaction notice
//! never restores (the kernel never died) and the restore notice never
//! prunes (the fresh kernel owns nothing to prune).
//!
//! TS reference: `agent-session.ts` `_onIpythonStateRestored` (the
//! `onRestore` callback of `IpythonKernelProvisioner`), delivered through
//! `sendCustomMessage(..., { deliverAs: "nextTurn" })`.

use crate::kernel::state_snapshot::RestoreResult;

/// The notice's `customType` (TS `IPYTHON_STATE_RESTORED_CUSTOM_TYPE`).
pub const IPYTHON_STATE_RESTORED_CUSTOM_TYPE: &str = "ipython_state_restored";

/// The notice text for `result`, or `None` when nothing was lost (every
/// snapshot name revived).
#[must_use]
pub fn notice_content(result: &RestoreResult) -> Option<String> {
    let lost = result
        .failed
        .iter()
        .map(|skip| skip.name.as_str())
        .collect::<Vec<_>>()
        .join(", ");
    match (result.restored.is_empty(), lost.is_empty()) {
        (false, true) => None,
        (true, true) => Some(
            "[python-state-restored] The Python kernel restarted without its earlier state; re-create the variables, imports, and data you need.".to_string(),
        ),
        (true, false) => Some(format!(
            "[python-state-restored] The Python kernel restarted without its earlier state; re-create what you need of: {lost}."
        )),
        (false, false) => Some(format!(
            "[python-state-restored] The Python kernel restarted; these names were lost, re-create them if needed: {lost}."
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::state_snapshot::SnapshotSkip;

    fn restore(restored: Vec<&str>, failed: Vec<&str>) -> RestoreResult {
        RestoreResult {
            restored: restored.into_iter().map(str::to_string).collect(),
            failed: failed
                .into_iter()
                .map(|name| SnapshotSkip {
                    name: name.to_string(),
                    reason: "cannot pickle".to_string(),
                })
                .collect(),
            path: std::path::PathBuf::from("/tmp/art/kernel-state.dill"),
        }
    }

    #[test]
    fn full_revival_owes_no_notice() {
        assert_eq!(
            notice_content(&restore(vec!["data", "helper"], vec![])),
            None
        );
    }

    #[test]
    fn fresh_kernel_owes_a_notice() {
        assert!(notice_content(&restore(vec![], vec![])).is_some());
    }

    #[test]
    fn lost_names_are_named() {
        for result in [
            restore(vec!["data"], vec!["sock"]),
            restore(vec![], vec!["sock"]),
        ] {
            let content = notice_content(&result).expect("lost state owes a notice");
            assert!(content.contains("sock"));
            assert!(!content.contains("data"));
        }
    }
}
