//! The Python a local kernel runs on: one pinned standalone `CPython`, the
//! same on every machine, which Eukhe fetches into its own directory the
//! first time a kernel is needed ([`toolchain`]: a pinned uv release, then
//! `uv python install` of the pinned version, each checked against its
//! pinned sha256). No Python of the system or of `PATH` is ever used, and
//! nothing has to be installed by hand.
//!
//! The kernel process starts on the standard library alone: the runtime's
//! sources and the session's Python skills reach it on `PYTHONPATH`
//! ([`runtime_python_path`]). Packages install on demand from a lock
//! ([`lock`]). The setup's plan is the compiled Bend core's ([`setup`]);
//! the code injected into each kernel after start is [`runtime_code`]'s.
//!
//! Entry points: [`ensure_kernel_python`] (a kernel start, and `eukhe
//! kernel install`: fetch what is absent), [`kernel_unavailable`] (a
//! session's open: the fetch failed, so the session offers no `python`
//! tool), [`kernel_state`] (`eukhe kernel install --check`: no network).

pub(crate) mod dir_lock;
pub mod lock;
#[cfg(test)]
mod pinned_kernel_tests;
mod runtime_code;
mod runtime_source;
mod setup;
pub(crate) mod toolchain;

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::time::Duration;

use anyhow::anyhow;

pub use lock::{lock_project_packages, project_lock_path, ProjectLockChange};
pub use runtime_code::{
    build_rlm_bootstrap_code, parse_unavailable_python_skills, UnavailablePythonSkills,
    PYTHON_SKILL_IMPORT_ERROR_REPORT_MARKER,
};
pub use runtime_source::resolve_runtime_source_dir;
pub use toolchain::{pinned_python_version, pinned_uv_version, unused_kernel_venv};

/// The command that fetches the kernel's Python now (a kernel start does
/// the same on its own).
pub const KERNEL_INSTALL_COMMAND: &str = "eukhe kernel install";
/// The start of a failed fetch's error.
pub(crate) const KERNEL_FETCH_FAILED: &str = "Eukhe could not fetch its Python kernel";
/// The start of the error of an `EUKHE_KERNEL_PYTHON` that is not a file.
pub(crate) const KERNEL_OVERRIDE_MISSING: &str = "EUKHE_KERNEL_PYTHON points to";
/// How long a session's open waits for the fetch it starts: an offline
/// machine fails well within it (no route, no DNS answer), and the session
/// then offers no `python` tool; a fetch still running after it goes on
/// in the background, and the first cell waits for it.
const OPEN_FETCH_WAIT: Duration = Duration::from_secs(2);

/// The packages of Eukhe's lock the prompt offers, as `(distribution,
/// import name)`: the direct entries of `eukhe-runtime/pyproject.toml`'s
/// `kernel` group a model imports (the lock test keeps both in step).
pub const LOCKED_PACKAGES: [(&str, &str); 13] = [
    ("requests", "requests"),
    ("httpx", "httpx"),
    ("pyyaml", "yaml"),
    ("tomli", "tomli"),
    ("python-dotenv", "dotenv"),
    ("pandas", "pandas"),
    ("numpy", "numpy"),
    ("scipy", "scipy"),
    ("beautifulsoup4", "bs4"),
    ("lxml", "lxml"),
    ("pydantic", "pydantic"),
    ("tyro", "tyro"),
    ("pillow", "PIL"),
];

/// Tests that set the kernel env variables (`EUKHE_KERNEL_PYTHON`,
/// `EUKHE_KERNEL_DIR`, `EUKHE_OFFLINE`, `HOME`, `PATH`) hold this lock: the
/// process env is global.
#[cfg(test)]
pub(crate) static KERNEL_ENV_LOCK: tokio::sync::Mutex<()> = tokio::sync::Mutex::const_new(());

/// One Python skill the kernel should import at bootstrap.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KernelPythonSkill {
    pub name: String,
    pub import_name: String,
    pub package_path: PathBuf,
    pub pyproject_path: PathBuf,
}

/// Progress callback of the setup (`ensure_kernel_python`).
pub type KernelBootstrapProgressHandler = std::sync::Arc<dyn Fn(&str) + Send + Sync>;

#[derive(Default)]
pub struct EnsureKernelPythonOptions {
    pub python_skills: Vec<KernelPythonSkill>,
    pub on_progress: Option<KernelBootstrapProgressHandler>,
}

impl EnsureKernelPythonOptions {
    pub(crate) fn report(&self, message: &str) {
        match &self.on_progress {
            Some(handler) => handler(message),
            None => eprintln!("{message}"),
        }
    }
}

/// What the kernel's on-demand package installs use (`rlm/pip.py`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KernelPackages {
    /// Eukhe's uv.
    pub uv: PathBuf,
    /// Eukhe's package lock.
    pub lock: PathBuf,
    /// The project's lock (it may not exist yet: `eukhe kernel lock`
    /// writes it, also while the kernel runs).
    pub project_lock: PathBuf,
    /// Where the project lock's packages are installed.
    pub project_packages: PathBuf,
}

/// The interpreter a kernel starts on, with what its process needs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KernelPython {
    pub python: PathBuf,
    /// The pinned version; `None` for an `EUKHE_KERNEL_PYTHON` override,
    /// which Eukhe runs as it is.
    pub version: Option<&'static str>,
    /// Put in front of the kernel's `PYTHONPATH`: the runtime's sources
    /// and the session's Python skills.
    pub python_path: Vec<PathBuf>,
    /// `None` for an override: Eukhe installs nothing into it.
    pub packages: Option<KernelPackages>,
}

impl KernelPython {
    /// `env`, the kernel process's environment, made to run on this Python.
    pub fn apply_env(&self, env: &mut HashMap<String, String>) {
        let mut paths = self.python_path.clone();
        if let Some(existing) = env.get("PYTHONPATH").filter(|value| !value.is_empty()) {
            paths.extend(std::env::split_paths(existing));
        }
        if let Ok(joined) = std::env::join_paths(paths) {
            env.insert(
                "PYTHONPATH".to_string(),
                joined.to_string_lossy().into_owned(),
            );
        }
        let package_env = [
            "EUKHE_KERNEL_UV",
            "EUKHE_KERNEL_LOCK",
            "EUKHE_KERNEL_PROJECT_LOCK",
            "EUKHE_KERNEL_PROJECT_PACKAGES",
        ];
        match &self.packages {
            Some(packages) => {
                let values = [
                    &packages.uv,
                    &packages.lock,
                    &packages.project_lock,
                    &packages.project_packages,
                ];
                for (name, value) in package_env.into_iter().zip(values) {
                    env.insert(name.to_string(), value.to_string_lossy().into_owned());
                }
            }
            None => {
                for name in package_env {
                    env.remove(name);
                }
            }
        }
    }

    /// `<python> (Python <version>)`, or `<python> (EUKHE_KERNEL_PYTHON)`.
    #[must_use]
    pub fn describe(&self) -> String {
        match self.version {
            Some(version) => format!("{} (Python {version})", self.python.display()),
            None => format!("{} (EUKHE_KERNEL_PYTHON)", self.python.display()),
        }
    }
}

/// The `EUKHE_KERNEL_PYTHON` override, if set: an interpreter the tests
/// and an embedder name themselves. Eukhe runs it as it is (the runtime on
/// `PYTHONPATH`) and manages nothing of it.
fn override_python() -> Option<PathBuf> {
    std::env::var("EUKHE_KERNEL_PYTHON")
        .ok()
        .filter(|python| !python.is_empty())
        .map(|python| toolchain::expand_home(&python))
}

/// What a kernel puts on its `PYTHONPATH`: the runtime's sources, then
/// each Python skill's package directory and its `src` (both layouts
/// import).
fn runtime_python_path(python_skills: &[KernelPythonSkill]) -> anyhow::Result<Vec<PathBuf>> {
    let mut paths = vec![resolve_runtime_source_dir()?.join("src")];
    for skill in python_skills {
        for path in [skill.package_path.clone(), skill.package_path.join("src")] {
            if !paths.contains(&path) {
                paths.push(path);
            }
        }
    }
    Ok(paths)
}

/// Eukhe's package lock, of the runtime this build runs.
pub(crate) fn runtime_lock_file() -> anyhow::Result<PathBuf> {
    let lock = resolve_runtime_source_dir()?.join(lock::LOCK_FILE);
    if lock.is_file() {
        return Ok(lock);
    }
    Err(anyhow!(
        "the kernel runtime has no {} at {}; reinstall eukhe (a source checkout regenerates it with `make runtime-lock`)",
        lock::LOCK_FILE,
        lock.display()
    ))
}

fn fetch_failure(error: &anyhow::Error) -> anyhow::Error {
    anyhow!(
        "{KERNEL_FETCH_FAILED}: {error:#}.\n\
         The kernel runs on one pinned Python (CPython {}), which Eukhe downloads once with its own uv {} \
         (about 50 MB, from github.com), so the first kernel start needs internet. \
         The next kernel start tries again; `{KERNEL_INSTALL_COMMAND}` fetches it now.",
        pinned_python_version(),
        pinned_uv_version()
    )
}

/// The kernel of an `EUKHE_KERNEL_PYTHON` override.
fn named_kernel(python: PathBuf, python_path: Vec<PathBuf>) -> anyhow::Result<KernelPython> {
    if !python.is_file() {
        return Err(anyhow!(
            "{KERNEL_OVERRIDE_MISSING} {}, which is not a file",
            python.display()
        ));
    }
    Ok(KernelPython {
        python,
        version: None,
        python_path,
        packages: None,
    })
}

fn pinned_kernel(
    toolchain: toolchain::Toolchain,
    lock: PathBuf,
    python_path: Vec<PathBuf>,
    cwd: Option<&Path>,
) -> anyhow::Result<KernelPython> {
    let project = match cwd {
        Some(cwd) => cwd.to_path_buf(),
        None => std::env::current_dir()?,
    };
    let project_lock = project_lock_path(&project);
    let project_packages = toolchain::KernelDir::resolve()?.project_packages(&project_lock);
    Ok(KernelPython {
        python: toolchain.python,
        version: Some(pinned_python_version()),
        python_path,
        packages: Some(KernelPackages {
            uv: toolchain.uv,
            lock,
            project_lock,
            project_packages,
        }),
    })
}

/// Resolve the Python a kernel in `cwd` starts on: the pinned interpreter
/// in Eukhe's directory, fetched first when it (or Eukhe's uv, or the
/// kernel env) is absent, with each stage reported. A machine that has
/// them makes no network request. An `EUKHE_KERNEL_PYTHON` override is run
/// as it is instead.
///
/// # Errors
///
/// Returns an error when the runtime source is missing, when the override
/// names no file, or when the fetch fails (the error says so and names
/// [`KERNEL_INSTALL_COMMAND`]).
pub async fn ensure_kernel_python(
    options: EnsureKernelPythonOptions,
    cwd: Option<&Path>,
) -> anyhow::Result<KernelPython> {
    let python_path = runtime_python_path(&options.python_skills)?;
    if let Some(python) = override_python() {
        return named_kernel(python, python_path);
    }
    let lock = runtime_lock_file()?;
    let toolchain = toolchain::ensure(&lock, &|message| options.report(message))
        .await
        .map_err(|error| fetch_failure(&error))?;
    pinned_kernel(toolchain, lock, python_path, cwd)
}

/// What `eukhe kernel install --check` reports.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KernelFetchState {
    /// A kernel starts at once on this interpreter.
    Ready(KernelPython),
    /// The pinned interpreter (or Eukhe's uv, or the kernel env) is not on
    /// disk yet: the first kernel start fetches it.
    NotFetched,
}

/// The kernel's state on disk for a session in `cwd`, without network and
/// without setting anything up.
///
/// # Errors
///
/// Returns an error when the runtime source is missing, the override
/// names no file, or the kernel directory cannot be made.
pub fn kernel_state(cwd: Option<&Path>) -> anyhow::Result<KernelFetchState> {
    let python_path = runtime_python_path(&[])?;
    if let Some(python) = override_python() {
        return Ok(KernelFetchState::Ready(named_kernel(python, python_path)?));
    }
    let lock = runtime_lock_file()?;
    match toolchain::ready(&lock)? {
        Some(toolchain) => Ok(KernelFetchState::Ready(pinned_kernel(
            toolchain,
            lock,
            python_path,
            cwd,
        )?)),
        None => Ok(KernelFetchState::NotFetched),
    }
}

/// Why a session cannot start the kernel.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KernelUnavailable {
    /// No `eukhe-runtime/` beside the binary (or in the source checkout
    /// it runs from): the text names every place looked at.
    RuntimeMissing(String),
    /// The pinned Python is not on disk and fetching it failed (offline,
    /// a download that does not match its sha256): the fetch's error.
    FetchFailed(String),
}

/// The probe a session runs at open: `Some` only when the kernel cannot
/// start. A machine that has the pinned toolchain answers from a few
/// `stat`s. One that lacks it starts the fetch here: a fetch that fails
/// within [`OPEN_FETCH_WAIT`] (an offline machine) leaves the session
/// without the `python` tool; one that is still running goes on in the
/// background and the session's first cell waits for it, showing its
/// stages. An `EUKHE_KERNEL_PYTHON` override is the user's choice and not
/// judged here: `None`.
pub async fn kernel_unavailable() -> Option<KernelUnavailable> {
    if override_python().is_some() {
        return None;
    }
    let lock = match runtime_lock_file() {
        Ok(lock) => lock,
        Err(error) => return Some(KernelUnavailable::RuntimeMissing(format!("{error:#}"))),
    };
    if matches!(toolchain::ready(&lock), Ok(Some(_))) {
        return None;
    }
    let fetch = tokio::spawn(async move {
        toolchain::ensure(&lock, &|message| tracing::info!("{message}")).await
    });
    match tokio::time::timeout(OPEN_FETCH_WAIT, fetch).await {
        Ok(Ok(Err(error))) => Some(KernelUnavailable::FetchFailed(format!(
            "{:#}",
            fetch_failure(&error)
        ))),
        // Fetched, or still fetching (the dropped handle leaves the task
        // running), or the fetch task was cancelled with its runtime.
        Ok(Ok(Ok(_)) | Err(_)) | Err(_) => None,
    }
}
