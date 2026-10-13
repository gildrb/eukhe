//! The post-compaction kernel-state notice (`ipython_state`).
//!
//! A compaction rebuilds the model context from the session file, but the
//! Python kernel behind the `ipython` tool survives it with its namespace
//! intact. After every compaction that commits while a kernel is running,
//! the session appends a hidden `ipython_state` custom row that tells the
//! model exactly that: which names are still defined, what the
//! per-variable size pruning removed, and that the kernel state does not
//! need rebuilding. The row is model context (it reaches the provider as a
//! user turn) and display-only bookkeeping for humans (`display: false`),
//! and it keeps the session branch from ending on the compaction row — a
//! second `/compact` back-to-back prepares again in update mode instead of
//! skipping as already compacted.

use eukhe_types::custom_type::CustomType;
use std::future::Future;
use std::pin::Pin;

use eukhe_types::session::CustomMessage;

use crate::autonomous::now_millis;
use crate::durable::observe::compaction_trace::trace;
use crate::kernel::provisioner::IpythonKernelProvisioner;

/// How long the namespace listing may take before it is abandoned (TS
/// `KERNEL_STATE_LISTING_TIMEOUT_MS`): a stuck kernel degrades the notice
/// to the no-detail arm rather than hanging the compaction.
pub const KERNEL_STATE_LISTING_TIMEOUT_MS: u64 = 5_000;

/// The kernel-state view the post-compaction notice reads: TS
/// `IpythonKernelProvisioner`'s `hasRunningKernel` /
/// `pruneOversizedVariables` / `listNamespaceNames` trio, narrowed to what
/// the notice needs. Implementations never fail: a missing or broken
/// kernel reports `false`/`None` and the notice adapts (TS wraps every
/// call in `?.` and `.catch(() => null)`). Object-safe on purpose (the
/// session holds `Arc<dyn CompactionKernelProbe>` and tests inject a
/// scripted probe), hence boxed futures.
pub trait CompactionKernelProbe: Send + Sync {
    /// Whether a kernel has finished starting and is currently running.
    fn has_running_kernel(&self) -> bool;
    /// Persist the namespace, then remove variables above the
    /// per-variable snapshot limit; the pruned names, or `None` when no
    /// kernel/snapshot target exists.
    fn prune_oversized_variables(
        &self,
    ) -> Pin<Box<dyn Future<Output = Option<Vec<String>>> + Send + '_>>;
    /// Live user-defined top-level names, or `None` when the listing
    /// failed or no kernel is running.
    fn list_namespace_names(
        &self,
        signal: Option<crate::kernel::cancellation::AbortSignal>,
    ) -> Pin<Box<dyn Future<Output = Option<Vec<String>>> + Send + '_>>;
}

impl CompactionKernelProbe for crate::kernel::provisioner::IpythonKernelProvisioner {
    fn has_running_kernel(&self) -> bool {
        IpythonKernelProvisioner::has_running_kernel(self)
    }
    fn prune_oversized_variables(
        &self,
    ) -> Pin<Box<dyn Future<Output = Option<Vec<String>>> + Send + '_>> {
        Box::pin(async move { IpythonKernelProvisioner::prune_oversized_variables(self).await })
    }
    fn list_namespace_names(
        &self,
        signal: Option<crate::kernel::cancellation::AbortSignal>,
    ) -> Pin<Box<dyn Future<Output = Option<Vec<String>>> + Send + '_>> {
        Box::pin(async move { IpythonKernelProvisioner::list_namespace_names(self, signal).await })
    }
}

/// The notice text (TS `_syncKernelStateAfterCompaction`'s builder): the
/// `[python-state]` header, the persistence statement, the pruning
/// disclosure, and the live-names detail. `names` is `None` when the
/// listing failed on a kernel that is still running (the notice lands
/// without the detail arm, TS `names === null`); `pruned` carries the
/// names removed above the per-variable snapshot limit.
#[must_use]
pub fn notice_content(pruned: Option<&[String]>, names: Option<&[String]>) -> String {
    let detail = match names {
        None => String::new(),
        Some(names) if !names.is_empty() => {
            format!(" These names are still defined: {}.", names.join(", "))
        }
        Some(_) => " You have not defined any names yet.".to_string(),
    };
    let pruned_detail = match pruned {
        Some(pruned) if !pruned.is_empty() => format!(
            " Variables above the per-variable snapshot limit were removed: {}.",
            pruned.join(", ")
        ),
        _ => String::new(),
    };
    format!(
        "[python-state]

Your Python kernel persisted through compaction; its remaining variables, imports, and helpers are still available.{pruned_detail}{detail}"
    )
}

/// The durable notice row: display false, no details (TS appends
/// `appendCustomMessageEntry(customType, content, display, undefined)`).
#[must_use]
pub fn notice_message(content: String) -> CustomMessage {
    CustomMessage {
        custom_type: CustomType::IpythonState,
        content: eukhe_types::ai::UserContent::Text(content),
        display: false,
        details: None,
        timestamp: now_millis(),
        rest: serde_json::Map::default(),
    }
}

/// Capture the notice content after a compaction (TS
/// `_syncKernelStateAfterCompaction`'s probe half): prune, list the live
/// names under the listing timeout, and decide whether the notice lands.
/// `None` when no kernel is running, or when a failed listing belongs to
/// a kernel that stopped mid-probe.
pub async fn capture_notice_content(probe: &dyn CompactionKernelProbe) -> Option<String> {
    if !probe.has_running_kernel() {
        return None;
    }
    let pruned = probe.prune_oversized_variables().await;
    trace(
        "compact.kernel_pruned",
        &serde_json::json!({
            "pruned": pruned.as_ref().map(std::vec::Vec::len),
        }),
    );
    let signal = crate::kernel::cancellation::AbortSignal::new();
    let timer = {
        let signal = signal.clone();
        tokio::spawn(async move {
            tokio::time::sleep(std::time::Duration::from_millis(
                KERNEL_STATE_LISTING_TIMEOUT_MS,
            ))
            .await;
            signal.abort();
        })
    };
    let names = probe.list_namespace_names(Some(signal)).await;
    timer.abort();
    trace(
        "compact.kernel_listed",
        &serde_json::json!({
            "names": names.as_ref().map(std::vec::Vec::len),
        }),
    );
    if names.is_none() && !probe.has_running_kernel() {
        return None;
    }
    Some(notice_content(pruned.as_deref(), names.as_deref()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use eukhe_types::session::AgentMessage as SessionAgentMessage;

    /// A scripted kernel probe: whether a kernel runs, what pruning removed,
    /// and which names the listing reports (TS's structural test double for
    /// `_ipythonKernelProvisioner`).
    struct ScriptedProbe {
        running: std::sync::atomic::AtomicBool,
        pruned: Option<Vec<String>>,
        names: Option<Vec<String>>,
        /// `None` keeps reporting `running` on the post-listing recheck.
        stopped_during_listing: bool,
    }

    impl ScriptedProbe {
        fn running(pruned: Option<Vec<String>>, names: Option<Vec<String>>) -> Self {
            Self {
                running: std::sync::atomic::AtomicBool::new(true),
                pruned,
                names,
                stopped_during_listing: false,
            }
        }
        fn idle() -> Self {
            Self {
                running: std::sync::atomic::AtomicBool::new(false),
                pruned: None,
                names: None,
                stopped_during_listing: false,
            }
        }
    }

    impl CompactionKernelProbe for ScriptedProbe {
        fn has_running_kernel(&self) -> bool {
            self.running.load(std::sync::atomic::Ordering::SeqCst)
        }
        fn prune_oversized_variables(
            &self,
        ) -> Pin<Box<dyn Future<Output = Option<Vec<String>>> + Send + '_>> {
            let pruned = self.pruned.clone();
            Box::pin(async move { pruned })
        }
        fn list_namespace_names(
            &self,
            _signal: Option<crate::kernel::cancellation::AbortSignal>,
        ) -> Pin<Box<dyn Future<Output = Option<Vec<String>>> + Send + '_>> {
            if self.stopped_during_listing {
                self.running
                    .store(false, std::sync::atomic::Ordering::SeqCst);
            }
            let names = self.names.clone();
            Box::pin(async move { names })
        }
    }

    #[test]
    fn notice_content_matches_the_ts_text() {
        // The full TS text (agent-session-compaction.test.ts asserts the
        // same sentence): prune disclosure first, then the live-names
        // detail.
        assert_eq!(
            notice_content(
                Some(&["large_text".to_string()]),
                Some(&["small_value".to_string()]),
            ),
            "[python-state]\n\nYour Python kernel persisted through compaction; its remaining variables, imports, and helpers are still available. Variables above the per-variable snapshot limit were removed: large_text. These names are still defined: small_value."
        );
        // An empty namespace spells the no-names arm.
        assert_eq!(
            notice_content(None, Some(&[])),
            "[python-state]\n\nYour Python kernel persisted through compaction; its remaining variables, imports, and helpers are still available. You have not defined any names yet."
        );
        // A failed listing on a still-running kernel lands the notice
        // without a detail arm (TS `names === null`).
        assert_eq!(
            notice_content(Some(&["large_text".to_string()]), None),
            "[python-state]\n\nYour Python kernel persisted through compaction; its remaining variables, imports, and helpers are still available. Variables above the per-variable snapshot limit were removed: large_text."
        );
        // Several names join comma-separated; nothing pruned keeps the
        // prune sentence out.
        assert_eq!(
            notice_content(None, Some(&["alpha".to_string(), "beta".to_string()])),
            "[python-state]\n\nYour Python kernel persisted through compaction; its remaining variables, imports, and helpers are still available. These names are still defined: alpha, beta."
        );
        // An empty prune list is no disclosure either.
        assert!(notice_content(Some(&[]), Some(&["v".to_string()]))
            .contains("still available. These names"));
    }

    /// The durable row shape (TS `appendCustomMessageEntry(customType,
    /// content, display, undefined)`): display false, no `details` key on
    /// the wire, and the custom role wrapper around it.
    #[test]
    fn notice_row_is_display_false_without_details() {
        let row = notice_message(notice_content(None, Some(&["v".to_string()])));
        assert_eq!(row.custom_type, CustomType::IpythonState);
        assert!(!row.display);
        assert_eq!(row.details, None);
        let wire = serde_json::to_value(SessionAgentMessage::Custom(row)).unwrap();
        assert_eq!(wire["role"], "custom");
        assert_eq!(wire["customType"], "ipython_state");
        assert_eq!(wire["display"], false);
        assert!(wire.get("details").is_none());
        assert_eq!(
            wire["content"],
            "[python-state]\n\nYour Python kernel persisted through compaction; its remaining variables, imports, and helpers are still available. These names are still defined: v."
        );
    }

    /// The capture guards (TS `_syncKernelStateAfterCompaction`'s early
    /// returns): an idle kernel never produces a notice, and a listing
    /// that failed while the kernel stopped mid-probe lands nothing.
    #[tokio::test]
    async fn capture_guards_match_ts() {
        let idle = ScriptedProbe::idle();
        assert_eq!(capture_notice_content(&idle).await, None);
        // A failed listing on a kernel that stopped mid-probe: no notice.
        let stopped = ScriptedProbe {
            names: None,
            stopped_during_listing: true,
            ..ScriptedProbe::running(None, None)
        };
        assert_eq!(capture_notice_content(&stopped).await, None);
        // A failed listing on a still-running kernel: the notice lands
        // without the detail arm.
        let listing_failed = ScriptedProbe::running(None, None);
        let content = capture_notice_content(&listing_failed).await;
        assert_eq!(
            content,
            Some(
                "[python-state]\n\nYour Python kernel persisted through compaction; its remaining variables, imports, and helpers are still available."
                    .to_string()
            )
        );
    }
}
