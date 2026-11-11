//! A session whose Python kernel cannot start: the open-time probe, and the
//! kernel-unavailable notification.
//!
//! At open, a local probe ([`crate::kernel::kernel_unavailable`]: no
//! network, no interpreter run) decides whether the kernel can start. When
//! it definitively cannot (the `eukhe-runtime/` directory is missing, or
//! the kernel venv is: `eukhe kernel install` never ran), the session
//! offers no `ipython` tool, so the model never spends a call on a cell
//! that can only answer with the install command; its system prompt says
//! the session has no Python REPL. Every open probes again: once the
//! kernel is installed, the next open offers the tool.
//!
//! The user is told by a notification, not by a session entry: the
//! session reports the text ([`crate::durable::HostDeps::kernel_unavailable_notice`],
//! the daemon's connection state carries it), and the interactive client
//! shows it once per install state ([`eukhe_types::kernel_notice`]). A
//! session of an install without the kernel is therefore as empty as any
//! other new session. A host with no notification surface (print, json
//! and rpc mode) shows nothing and leaves the notification to the next
//! interactive client. The Python backend is dropped after a definitive
//! failed probe, and the first-launch Python warning is raised on
//! interactive launches only; its text goes to the UI's startup
//! notifications, never into the session.

use std::path::Path;

use crate::kernel::transport::KernelTransport;
use crate::kernel::{KernelUnavailable, KERNEL_INSTALL_COMMAND};
use crate::settings::SettingsManager;

/// The `customType` of the row that carried the notice before it became
/// a notification. No open writes it any more; a session stored with one
/// still opens, and the row stays display-only (never model context).
pub const KERNEL_UNAVAILABLE_CUSTOM_TYPE: &str = "kernel_unavailable";

/// The session's probe: `None` when the session names its interpreter
/// (`SessionConfig::kernel_python`) or its kernel runs through a
/// `kernelTransport` wrapper (the sandbox's interpreter, not the host
/// venv; a setting that does not parse fails at the kernel's creation),
/// else [`crate::kernel::kernel_unavailable`].
pub(crate) fn probe(
    kernel_python: Option<&Path>,
    settings: &SettingsManager,
) -> Option<KernelUnavailable> {
    if kernel_python.is_some() {
        return None;
    }
    match KernelTransport::from_setting(settings.get_kernel_transport().as_ref()) {
        Ok(KernelTransport::Local) => crate::kernel::kernel_unavailable(),
        Ok(_) | Err(_) => None,
    }
}

/// The notice text: why the kernel cannot start, what the session lacks,
/// and the fix.
#[must_use]
pub fn notice_text(unavailable: &KernelUnavailable) -> String {
    match unavailable {
        KernelUnavailable::NotInstalled(venv) => format!(
            "The Python kernel is not installed, so this session has no `ipython` tool; the other tools work. \
             Run `{KERNEL_INSTALL_COMMAND}` once (it installs into {}), then open the session again. \
             To use your own Python, set EUKHE_KERNEL_PYTHON.",
            venv.display()
        ),
        KernelUnavailable::RuntimeMissing(reason) => format!(
            "The Python kernel cannot start: {reason}. This session has no `ipython` tool; the other tools work. \
             With eukhe-runtime/ in place, run `{KERNEL_INSTALL_COMMAND}` once, then open the session again."
        ),
    }
}
