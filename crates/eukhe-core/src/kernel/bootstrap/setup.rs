//! The kernel setup decision: what the setup does with the kernel venv it
//! finds, and whether it may download. A session (every path but `eukhe
//! kernel install`) uses only local files; `eukhe kernel install` is the
//! only path that downloads. The model is `bend/kernel_local.bend`; its
//! laws (`LAWS.bend` section `kernel_local`) are proven in `PROOF.bend`.

/// What the kernel setup may fetch.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum KernelSetup {
    /// A session or any other command: use the installed kernel, or build
    /// it from local files only (uv `--offline`). Never downloads.
    Local,
    /// `eukhe kernel install`: may download Python and the hash-locked
    /// kernel packages, each checked against its hash before install.
    Install,
}

/// The kernel venv the setup finds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Found {
    /// Its runtime and the session's Python skills are current.
    Ready,
    /// Its runtime is current; some Python skills are missing or changed.
    SkillsStale,
    /// It is missing, or its runtime is not this build's.
    Stale,
}

/// Where the commands of a build may get their files.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Fetch {
    /// Only from the local uv cache and Python installs (`--offline`).
    Offline,
    /// The Python install and the hash-locked packages may download.
    Download,
}

/// The step the setup takes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SetupStep {
    /// Start the kernel as it is.
    Use,
    /// Install the missing Python skills from their local directories.
    SyncSkills,
    /// Build the venv again, with the files `Fetch` allows.
    Build(Fetch),
}

/// The step for the venv `found` under `setup`.
pub(crate) fn setup_step(found: Found, setup: KernelSetup) -> SetupStep {
    match (found, setup) {
        (Found::Ready, KernelSetup::Local | KernelSetup::Install) => SetupStep::Use,
        (Found::SkillsStale, KernelSetup::Local | KernelSetup::Install) => SetupStep::SyncSkills,
        (Found::Stale, KernelSetup::Local) => SetupStep::Build(Fetch::Offline),
        (Found::Stale, KernelSetup::Install) => SetupStep::Build(Fetch::Download),
    }
}
