//! A session whose Python kernel cannot start: the open-time probe, and the
//! kernel-unavailable notice (`kernel_unavailable`).
//!
//! At open, a local probe ([`crate::kernel::kernel_unavailable`]: no
//! network, no interpreter run) decides whether the kernel can start. When
//! it definitively cannot (the `eukhe-runtime/` directory is missing, or
//! the kernel venv is: `eukhe kernel install` never ran), the session
//! offers no `ipython` tool, so the model never spends a call on a cell
//! that can only answer with the install command. The user sees one
//! display-only row naming the fix, once per install state: the first
//! session that finds the kernel unavailable shows it, later sessions do
//! not, until a session finds the kernel usable and a later one finds it
//! gone again. The model does not see the row; its system prompt already
//! says the session has no Python REPL. Every open probes again: once the
//! kernel is installed, the next open offers the tool. omp parity:
//! `resolveAdvertisedEvalBackends` drops the Python backend after a
//! definitive failed probe; `resolveFirstLaunchPythonEvalWarning` warns
//! once, not at every session.

use std::path::Path;

use crate::kernel::transport::KernelTransport;
use crate::kernel::{KernelUnavailable, KERNEL_INSTALL_COMMAND};
use crate::settings::SettingsManager;

/// The notice's `customType` (display-only: never model context).
pub const KERNEL_UNAVAILABLE_CUSTOM_TYPE: &str = "kernel_unavailable";

/// The file in the agent state directory (`~/.eukhe`) that records the
/// notice was shown for the current unavailability: later sessions, and a
/// session reopened, do not show it again.
const NOTICE_SHOWN_MARKER: &str = "kernel-unavailable-shown";

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

/// The notice this open shows, if any: the text while the kernel is
/// unavailable and no session of the install under `state_dir` has shown
/// it since the kernel was last usable. An open that finds the kernel
/// usable forgets the shown notice, so a later loss shows it again.
pub(crate) fn notice_once(
    state_dir: &Path,
    unavailable: Option<&KernelUnavailable>,
) -> Option<String> {
    let marker = state_dir.join(NOTICE_SHOWN_MARKER);
    let Some(unavailable) = unavailable else {
        match std::fs::remove_file(&marker) {
            Ok(()) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => {
                tracing::warn!(%error, marker = %marker.display(), "kernel notice marker not removed");
            }
        }
        return None;
    };
    // Created before the row is written, atomically: two sessions opening
    // at once show one row.
    match std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&marker)
    {
        Ok(_) => {}
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => return None,
        // The row still shows: a notice shown twice beats none.
        Err(error) => {
            tracing::warn!(%error, marker = %marker.display(), "kernel notice marker not written");
        }
    }
    Some(notice_text(unavailable))
}
