//! Kernel Python environment bootstrap: the public entry points
//! [`ensure_kernel_python`] (a session: the installed venv, or one built
//! from local files only) and [`install_kernel_python`] (`eukhe kernel
//! install`: the only path that downloads) resolve the venv that runs
//! `python -m rlm.repl`, deduplicating concurrent bootstraps; the setup
//! decision lives in [`setup`], the venv and version-file machinery in
//! [`venv`], the runtime bootstrap code injected into each kernel in
//! [`runtime_code`].
//!
//! Ported from `core/kernel/bootstrap.ts`.

#[cfg(test)]
mod bridge;
pub(crate) mod dir_lock;
mod disk_memo;
mod runtime_code;
mod setup;
pub(crate) mod venv;

use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use anyhow::{anyhow, Context};

use dir_lock::acquire_bootstrap_lock;
pub use runtime_code::{
    build_rlm_bootstrap_code, parse_unavailable_python_skills, UnavailablePythonSkills,
    PYTHON_SKILL_IMPORT_ERROR_REPORT_MARKER,
};
use venv::{
    bootstrap_venv, ensure_uv, expand_home, has_eukhe_runtime, missing_python_skill_import_labels,
    missing_rlm_extra_import_labels, normalize_python_skills, resolve_writable_kernel_venv_dir,
    sync_python_skills, BootstrapPythonSkill,
};
pub use venv::{
    invalidate_runtime_probe_cache, kernel_venv_dir, kernel_venv_python, resolve_runtime_identity,
};
use venv::{kernel_base_ready, kernel_ready};

use setup::{setup_step, Fetch, Found, KernelSetup, SetupStep};

/// The command that installs the kernel environment.
pub const KERNEL_INSTALL_COMMAND: &str = "eukhe kernel install";
/// The start of a session's setup failure: the kernel is missing or out of
/// date, and local files cannot set it up.
pub(crate) const KERNEL_NOT_INSTALLED: &str = "The Python kernel is not installed";
/// The start of a failed `eukhe kernel install`.
pub(crate) const KERNEL_INSTALL_FAILED: &str = "Failed to install the Python kernel";

/// Tests that set the kernel env variables (`EUKHE_KERNEL_PYTHON`,
/// `EUKHE_KERNEL_VENV`, `HOME`) hold this lock: the process env is global.
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

/// The default extra packages pre-installed in the kernel venv and promised to
/// the model in the system prompt. The installs themselves come from the
/// runtime's `kernel` dependency group, hash-locked in
/// `eukhe-runtime/requirements-kernel.txt`; the distribution column names
/// the locked distribution backing each import.
pub const DEFAULT_RLM_EXTRA_PACKAGES: [(&str, &str, &str); 12] = [
    // (distribution, importName, promptLabel)
    ("requests", "requests", "requests"),
    ("httpx", "httpx", "httpx"),
    ("pyyaml", "yaml", "yaml (PyYAML)"),
    ("tomli", "tomli", "tomli"),
    ("python-dotenv", "dotenv", "dotenv (python-dotenv)"),
    ("pandas", "pandas", "pandas"),
    ("numpy", "numpy", "numpy"),
    ("scipy", "scipy", "scipy"),
    ("beautifulsoup4", "bs4", "bs4 (Beautiful Soup)"),
    ("lxml", "lxml", "lxml"),
    ("pydantic", "pydantic", "pydantic"),
    ("tyro", "tyro", "tyro"),
];

#[must_use]
pub fn default_rlm_extra_import_labels() -> Vec<&'static str> {
    DEFAULT_RLM_EXTRA_PACKAGES
        .iter()
        .map(|(_, _, label)| *label)
        .collect()
}

/// Progress callback for the bootstrap (`ensure_kernel_python`).
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

fn format_setup_failure(error: &anyhow::Error, setup: KernelSetup) -> anyhow::Error {
    match setup {
        KernelSetup::Local => anyhow!(
            "{KERNEL_NOT_INSTALLED}: run `{KERNEL_INSTALL_COMMAND}` once. \
             It downloads Python and the kernel's hash-locked packages (eukhe-runtime/requirements-kernel.txt); after that, eukhe sets up the kernel from local files only. \
             The other tools work without the kernel. \
             To use your own Python, set EUKHE_KERNEL_PYTHON to a Python with a current eukhe-runtime and the default Python packages. \
             Cause: {error:#}"
        ),
        KernelSetup::Install => anyhow!(
            "{KERNEL_INSTALL_FAILED}. {error:#}\n\
             The install downloads Python and the kernel's hash-locked packages (eukhe-runtime/requirements-kernel.txt), so it needs internet. \
             Run `{KERNEL_INSTALL_COMMAND}` again when you are online. \
             To use your own Python, set EUKHE_KERNEL_PYTHON to a Python with a current eukhe-runtime and the default Python packages."
        ),
    }
}

/// One in-flight bootstrap per unique options set, joined by concurrent callers.
type InFlightBootstrap = Option<(
    String,
    Arc<tokio::sync::Mutex<Option<anyhow::Result<PathBuf>>>>,
)>;

static IN_FLIGHT: Mutex<InFlightBootstrap> = Mutex::new(None);

/// Resolve the Python interpreter for a session's kernel: the
/// `EUKHE_KERNEL_PYTHON` override when valid, else the kernel venv python.
/// This makes no network request: a missing or out-of-date venv is built
/// again from local files only (the uv cache and Python installs that
/// [`install_kernel_python`] left), and when that is not possible the
/// error tells the user to run `eukhe kernel install`.
///
/// # Errors
///
/// Returns an error when the `EUKHE_KERNEL_PYTHON` override points to
/// a Python missing the kernel runtime or default packages, when a writable
/// venv directory cannot be resolved, or when the kernel venv cannot be set
/// up from local files (the error names `eukhe kernel install`).
pub async fn ensure_kernel_python(options: EnsureKernelPythonOptions) -> anyhow::Result<PathBuf> {
    resolve_kernel_python(options, KernelSetup::Local).await
}

/// `eukhe kernel install`: make the kernel venv current, downloading
/// Python and the hash-locked kernel packages when the venv is missing or
/// out of date (uv checks each file against its hash before install). A
/// current venv is used as it is, so a second run downloads nothing.
///
/// # Errors
///
/// Returns an error when the `EUKHE_KERNEL_PYTHON` override points to a
/// Python missing the kernel runtime or default packages, when a writable
/// venv directory cannot be resolved, or when the install fails (the
/// failure is formatted with remediation hints).
pub async fn install_kernel_python(options: EnsureKernelPythonOptions) -> anyhow::Result<PathBuf> {
    resolve_kernel_python(options, KernelSetup::Install).await
}

/// The kernel environment as `eukhe kernel install --check` reports it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KernelInstallState {
    /// `EUKHE_KERNEL_PYTHON` names the interpreter: eukhe installs nothing.
    Override(PathBuf),
    /// The kernel venv is current; the path is its interpreter.
    Installed(PathBuf),
    /// The kernel venv exists, but its runtime is not this build's; the
    /// path is the venv.
    OutOfDate(PathBuf),
    /// No kernel venv; the path is where it goes.
    Missing(PathBuf),
}

/// The state of the kernel environment. Makes no network request: it
/// reads the venv and runs its interpreter's readiness probe.
///
/// # Errors
///
/// Returns an error when no writable venv directory can be resolved or the
/// runtime source of this build cannot be read.
pub fn kernel_install_state() -> anyhow::Result<KernelInstallState> {
    if let Ok(override_python) = std::env::var("EUKHE_KERNEL_PYTHON") {
        if !override_python.is_empty() {
            return Ok(KernelInstallState::Override(expand_home(&override_python)));
        }
    }
    let venv = resolve_writable_kernel_venv_dir()?;
    let python = kernel_venv_python(&venv);
    let runtime_identity = resolve_runtime_identity()?;
    if kernel_base_ready(&python.to_string_lossy(), &venv, &runtime_identity) {
        return Ok(KernelInstallState::Installed(python));
    }
    if venv.exists() {
        return Ok(KernelInstallState::OutOfDate(venv));
    }
    Ok(KernelInstallState::Missing(venv))
}

/// The shared flow of [`ensure_kernel_python`] and [`install_kernel_python`].
///
/// # Panics
///
/// The in-flight promise stores its outcome under the same lock that takes
/// it, so the internal `expect` on the stored outcome is unreachable.
async fn resolve_kernel_python(
    options: EnsureKernelPythonOptions,
    setup: KernelSetup,
) -> anyhow::Result<PathBuf> {
    let python_skills = normalize_python_skills(&options.python_skills);
    let key = [
        std::env::var("EUKHE_KERNEL_PYTHON").unwrap_or_default(),
        std::env::var("EUKHE_KERNEL_VENV").unwrap_or_default(),
        std::env::var("HOME").unwrap_or_default(),
        std::env::var("XDG_DATA_HOME").unwrap_or_default(),
        serde_json::to_string(&python_skills).unwrap_or_default(),
        format!("{setup:?}"),
    ]
    .join("\u{0}");

    let shared = {
        let mut in_flight = IN_FLIGHT
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        match in_flight.as_ref() {
            Some((existing_key, promise)) if *existing_key == key => promise.clone(),
            _ => {
                let promise = Arc::new(tokio::sync::Mutex::new(None));
                *in_flight = Some((key, promise.clone()));
                promise
            }
        }
    };
    let mut guard = shared.lock().await;
    if guard.is_none() {
        *guard = Some(ensure_kernel_python_uncached(&options, &python_skills, setup).await);
    }
    let outcome = guard.take().expect("outcome was just stored");
    // Drop the registry entry so a later call re-validates instead of reusing
    // a cached rejection forever.
    let mut in_flight = IN_FLIGHT
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    if matches!(in_flight.as_ref(), Some((_, promise)) if Arc::ptr_eq(promise, &shared)) {
        *in_flight = None;
    }
    outcome
}

async fn ensure_kernel_python_uncached(
    options: &EnsureKernelPythonOptions,
    python_skills: &[BootstrapPythonSkill],
    setup: KernelSetup,
) -> anyhow::Result<PathBuf> {
    if let Ok(override_python) = std::env::var("EUKHE_KERNEL_PYTHON") {
        if !override_python.is_empty() {
            let python = expand_home(&override_python);
            let python_str = python.to_string_lossy().to_string();
            let mut missing = Vec::new();
            if !has_eukhe_runtime(&python_str).await {
                missing.push(
                    "a current eukhe-runtime with callable rlm.spawn, rlm.create_session, rlm.host_request, rlm.progress_note, rlm.rename, and explicit harness CRUD methods".to_string(),
                );
            }
            if missing.is_empty() {
                let missing_extras = missing_rlm_extra_import_labels(&python_str).await;
                if !missing_extras.is_empty() {
                    missing.push(format!(
                        "default Python packages ({})",
                        missing_extras.join(", ")
                    ));
                }
            }
            if missing.is_empty() && !options.python_skills.is_empty() {
                let missing_skills =
                    missing_python_skill_import_labels(&python_str, &options.python_skills).await;
                if !missing_skills.is_empty() {
                    options.report(&format!(
                        "Warning: Python skills unavailable in EUKHE_KERNEL_PYTHON and will be disabled: {}",
                        missing_skills.join(", ")
                    ));
                }
            }
            if missing.is_empty() {
                return Ok(python);
            }
            return Err(anyhow!(
                "EUKHE_KERNEL_PYTHON points to a Python missing {}: {}",
                missing.join(" and "),
                python.display()
            ));
        }
    }

    let venv = resolve_writable_kernel_venv_dir()?;
    let python = kernel_venv_python(&venv);
    let python_str = python.to_string_lossy().to_string();
    let runtime_identity =
        resolve_runtime_identity().map_err(|error| format_setup_failure(&error, setup))?;
    if kernel_ready(&python_str, &venv, &runtime_identity, python_skills) {
        return Ok(python);
    }

    let release_lock = acquire_bootstrap_lock(&venv)
        .await
        .map_err(|error| format_setup_failure(&error, setup))?;
    let result = async {
        let found = if kernel_ready(&python_str, &venv, &runtime_identity, python_skills) {
            Found::Ready
        } else if kernel_base_ready(&python_str, &venv, &runtime_identity) {
            Found::SkillsStale
        } else {
            Found::Stale
        };
        match setup_step(found, setup) {
            SetupStep::Use => {}
            SetupStep::SyncSkills => {
                let uv = ensure_uv()?;
                sync_python_skills(
                    &uv,
                    &venv,
                    &python,
                    &runtime_identity,
                    python_skills,
                    options,
                )
                .await?;
            }
            SetupStep::Build(fetch) => {
                options.report(match fetch {
                    Fetch::Offline => "> setting up python kernel from local files...",
                    Fetch::Download => {
                        "> installing python kernel (downloads Python and the hash-locked packages)..."
                    }
                });
                if venv.exists() {
                    options.report("rebuilding kernel venv");
                    std::fs::remove_dir_all(&venv)
                        .with_context(|| format!("removing {}", venv.display()))?;
                }
                bootstrap_venv(&venv, python_skills, options, fetch).await?;
                options.report("ok ready");
            }
        }
        Ok(python)
    }
    .await;
    drop(release_lock);
    result.map_err(|error| format_setup_failure(&error, setup))
}

// ---------------------------------------------------------------------------
// Runtime bootstrap code (from core/tools/ipython.ts)
// ---------------------------------------------------------------------------
