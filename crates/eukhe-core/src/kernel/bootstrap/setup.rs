//! The kernel setup decision: what the setup does with the kernel venv it
//! finds, and which of its uv commands may download. A session (every path
//! but `eukhe kernel install`) uses only local files; `eukhe kernel
//! install` is the only path that downloads. The rule is `plan` of
//! `bend/kernel_local.bend`, run by the compiled Bend core
//! (`bend/ffi_kernel_local.bend`, request 0; laws `kernel_plan_exact`,
//! `kernel_session_never_downloads`, `kernel_fetch_verified_before_use` in
//! `laws/kernel_local.bend`).

use eukhe_bend::wire::{Reader, WireError, Writer};
use eukhe_bend::{Entry, Error};

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

/// Where one command of a build may get its files.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Fetch {
    /// Only from the local uv cache and Python installs (`--offline`).
    Offline,
    /// It may download (each file checked against its pinned hash).
    Download,
}

/// The step the setup takes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SetupStep {
    /// Start the kernel as it is.
    Use,
    /// Install the missing Python skills from their local directories.
    SyncSkills,
    /// Build the venv again: the Python install, the venv, the hash-locked
    /// requirements and the runtime, each with the files its `Fetch`
    /// allows; then `uv pip check`; then start.
    Build([Fetch; 4]),
}

/// The step for the venv `found` under `setup`.
pub(crate) fn setup_step(found: Found, setup: KernelSetup) -> SetupStep {
    eukhe_bend::expect_core(Entry::KernelLocal, ask(found, setup))
}

/// One action of the core's plan.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Act {
    /// A command that may download; `true`: every file it gets is checked
    /// against a pinned hash.
    Fetch(bool),
    /// A command that uses local files only.
    Offline,
    /// `uv pip check` of the built venv.
    Check,
    /// The kernel starts.
    Run,
}

fn ask(found: Found, setup: KernelSetup) -> Result<SetupStep, Error> {
    let mut request = Writer::new();
    request
        .tag(0)
        .tag(match found {
            Found::Ready => 0,
            Found::SkillsStale => 1,
            Found::Stale => 2,
        })
        .tag(match setup {
            KernelSetup::Local => 0,
            KernelSetup::Install => 1,
        });
    let reply = eukhe_bend::call(Entry::KernelLocal, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let count = reader.count()?;
    let mut acts = Vec::with_capacity(count.min(8));
    for _ in 0..count {
        acts.push(match reader.tag_of(4, "a setup action")? {
            0 => Act::Fetch(reader.bool()?),
            1 => Act::Offline,
            2 => Act::Check,
            // `tag_of` answers a tag below 4: this is 3.
            _ => Act::Run,
        });
    }
    reader.end()?;
    step_of(&acts).map_err(Error::from)
}

/// The step the plan `acts` describes: the plan shapes the setup runs.
fn step_of(acts: &[Act]) -> Result<SetupStep, WireError> {
    match acts {
        [Act::Run] => Ok(SetupStep::Use),
        [Act::Offline, Act::Run] => Ok(SetupStep::SyncSkills),
        [python, venv, requirements, runtime, Act::Check, Act::Run] => Ok(SetupStep::Build([
            fetch_of(*python)?,
            fetch_of(*venv)?,
            fetch_of(*requirements)?,
            fetch_of(*runtime)?,
        ])),
        _ => Err(not_a_plan()),
    }
}

/// How a build command gets its files: a fetch the core plans is always
/// hash-checked (the build's commands have no other kind).
fn fetch_of(act: Act) -> Result<Fetch, WireError> {
    match act {
        Act::Offline => Ok(Fetch::Offline),
        Act::Fetch(true) => Ok(Fetch::Download),
        Act::Fetch(false) | Act::Check | Act::Run => Err(not_a_plan()),
    }
}

fn not_a_plan() -> WireError {
    WireError::Malformed {
        at: 0,
        expected:
            "a setup plan: start, sync then start, or four build commands, the check, then start",
    }
}
