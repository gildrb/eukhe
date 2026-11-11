//! A session whose Python kernel cannot start: the open-time probe, and the
//! kernel-unavailable notification.
//!
//! The kernel runs on one pinned Python that Eukhe fetches itself the
//! first time it is needed. At open, the probe
//! ([`crate::kernel::kernel_unavailable`]) finds it on disk (a few
//! `stat`s, no network) or starts the fetch. Only when the kernel
//! definitively cannot start (the `eukhe-runtime/` directory is missing,
//! or the pinned Python is not on disk and the fetch failed: the machine is
//! offline) does the session offer no `python` tool, so the model never
//! spends a call on a cell that can only fail; its system prompt says the
//! session has no Python REPL. Every open probes again: once the machine
//! is online, the next open fetches the Python and offers the tool.
//!
//! The user is told by a notification, not by a session entry: the
//! session reports the text ([`crate::durable::HostDeps::kernel_unavailable_notice`],
//! the daemon's connection state carries it), and the interactive client
//! shows it once per install state ([`eukhe_types::kernel_notice`]). A
//! session of an install without the kernel is therefore as empty as any
//! other new session. A host with no notification surface (print, json
//! and rpc mode) shows nothing and leaves the notification to the next
//! interactive client. omp parity: `resolveAdvertisedEvalBackends` drops
//! the Python backend after a definitive failed probe;
//! `resolveFirstLaunchPythonEvalWarning` runs on interactive launches
//! only and its text goes to the UI's startup notifications
//! (`main.ts:2598-2612`, `main.ts:2855-2857`), never into the session.

use std::path::Path;

use crate::kernel::transport::KernelTransport;
use crate::kernel::KernelUnavailable;
use crate::settings::SettingsManager;

/// The `customType` of the row that carried the notice before it became
/// a notification. No open writes it any more; a session stored with one
/// still opens, and the row stays display-only (never model context).
pub const KERNEL_UNAVAILABLE_CUSTOM_TYPE: &str = "kernel_unavailable";

/// The session's probe: `None` when the session names its interpreter
/// (`SessionConfig::kernel_python`) or its kernel runs through a
/// `kernelTransport` wrapper (the sandbox's interpreter, not the host's;
/// a setting that does not parse fails at the kernel's creation), else
/// [`crate::kernel::kernel_unavailable`].
pub(crate) async fn probe(
    kernel_python: Option<&Path>,
    settings: &SettingsManager,
) -> Option<KernelUnavailable> {
    if kernel_python.is_some() {
        return None;
    }
    match KernelTransport::from_setting(settings.get_kernel_transport().as_ref()) {
        Ok(KernelTransport::Local) => crate::kernel::kernel_unavailable().await,
        Ok(_) | Err(_) => None,
    }
}

/// The notice text: why the kernel cannot start, what the session lacks,
/// and the fix.
#[must_use]
pub fn notice_text(unavailable: &KernelUnavailable) -> String {
    match unavailable {
        KernelUnavailable::FetchFailed(reason) => format!(
            "The Python kernel cannot start: {reason}\n\
             This session has no `python` tool; the other tools work. The next session tries the fetch again."
        ),
        KernelUnavailable::RuntimeMissing(reason) => format!(
            "The Python kernel cannot start: {reason}. This session has no `python` tool; the other tools work. \
             With eukhe-runtime/ in place, open the session again."
        ),
    }
}
