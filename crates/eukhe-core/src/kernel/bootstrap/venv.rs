//! Venv discovery, build, lock, and the shared `.bootstrap-version` cache:
//! the machine state behind [`super::ensure_kernel_python`]. The version
//! file is a cross-session cache, not a per-session manifest.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::Stdio;
use std::sync::Mutex;

use anyhow::{anyhow, Context};
use sha2::Digest;

use super::{EnsureKernelPythonOptions, KernelPythonSkill, DEFAULT_RLM_EXTRA_PACKAGES};

// The concern children (cut with their concerns; the flows + the shared
// record stay in the composition root).
mod layout;
mod probe;
mod runtime_source;
mod skills;
mod uv;
mod version;

use layout::home_dir;
pub(crate) use layout::{expand_home, resolve_writable_kernel_venv_dir};
pub use layout::{kernel_venv_dir, kernel_venv_python};
pub use probe::invalidate_runtime_probe_cache;
#[cfg(test)]
use probe::{installed_rlm_dir, lock_probe_memo, runtime_probe_key};
// The memo-clear helper and the live-probe package-dir walk exist only behind
// the unix tests (see their gates in probe.rs and tests.rs).
#[cfg(all(test, unix))]
use probe::{clear_in_process_probe_memo_for_tests, installed_package_dir};
pub(crate) use probe::{
    has_eukhe_runtime, missing_python_skill_import_labels, missing_rlm_extra_import_labels,
};
use probe::{has_eukhe_runtime_memoized, installed_runtime_identity};
pub use runtime_source::resolve_runtime_identity;
use runtime_source::{
    collect_python_files, hash_runtime_source, resolve_runtime_source_dir, RUNTIME_LOCK_FILE,
};
#[cfg(test)]
use skills::{file_content_hash, read_python_skill_dependency_names};
use skills::{
    normalize_distribution_name, read_python_skill_project_name, unsatisfied_requirements,
};
pub(crate) use skills::{normalize_python_skills, BootstrapPythonSkill};
pub(crate) use uv::ensure_uv;
#[cfg(test)]
use uv::windows_executable_candidates;
use version::{
    bootstrap_base_version_current, bootstrap_skill_key, bootstrap_version_current,
    read_bootstrap_version, read_bootstrap_version_raw, write_bootstrap_version,
};
#[cfg(test)]
use version::{recorded_skills_cover, BOOTSTRAP_SCHEMA};

const PYTHON_VERSION: &str = "3.11";
/// Flags for every install of a local package (the runtime, the skills):
/// its requirements must already be satisfied by the hash-locked venv, no
/// index is ever consulted, and its build backend (hatchling) comes from
/// the lock instead of an isolated build env resolved from an index.
const LOCAL_INSTALL_FLAGS: [&str; 3] = ["--no-deps", "--no-index", "--no-build-isolation"];
pub(crate) const BOOTSTRAP_LOCK_NAME: &str = ".bootstrap.lock";
pub(crate) const BOOTSTRAP_LOCK_RETRY_MS: u64 = 100;
pub(crate) const BOOTSTRAP_LOCK_STALE_WITHOUT_PID_MS: u64 = 30_000;
#[derive(Debug, Clone, Default, serde::Serialize, serde::Deserialize)]
pub(crate) struct BootstrapVersion {
    schema: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    runtime: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    python_skills: Option<Vec<BootstrapPythonSkill>>,
}

/// `uv pip <subcommand>` against the kernel venv's interpreter, ignoring
/// every `uv.toml`/`pyproject.toml` uv would otherwise discover from the
/// working directory (an arbitrary project must not steer the install).
fn uv_pip_args(subcommand: &str, python: &str) -> Vec<String> {
    ["pip", subcommand, "--no-config", "--python", python]
        .into_iter()
        .map(String::from)
        .collect()
}

async fn run_async(command: &str, args: &[String]) -> anyhow::Result<()> {
    // Run on a blocking thread: the bootstrap is an IO-bound child process.
    let command = command.to_string();
    let args = args.to_vec();
    tokio::task::spawn_blocking(move || {
        let mut child = std::process::Command::new(&command);
        child.args(&args).stdin(Stdio::null());
        // Hidden window on Windows (TS `spawnHidden`).
        crate::platform::process::set_no_window(&mut child);
        let status = child
            .status()
            .with_context(|| format!("failed to spawn {command}"))?;
        if status.success() {
            Ok(())
        } else {
            Err(anyhow!(
                "{} {} failed with exit code {}",
                command,
                args.join(" "),
                status.code().unwrap_or(-1)
            ))
        }
    })
    .await
    .map_err(|e| anyhow!("bootstrap task join failed: {e}"))?
}

/// `uv pip check` against the venv (offline): `Ok(None)` when every
/// installed distribution's requirements are satisfied, else uv's
/// incompatibility report.
async fn uv_pip_check(uv: &str, python: &str) -> anyhow::Result<Option<String>> {
    let command = uv.to_string();
    let args = uv_pip_args("check", python);
    let output = tokio::task::spawn_blocking(move || {
        let mut child = std::process::Command::new(&command);
        child.args(&args).stdin(Stdio::null());
        // Hidden window on Windows (TS `spawnHidden`).
        crate::platform::process::set_no_window(&mut child);
        child
            .output()
            .with_context(|| format!("failed to spawn {command}"))
    })
    .await
    .map_err(|e| anyhow!("bootstrap task join failed: {e}"))??;
    if output.status.success() {
        return Ok(None);
    }
    let mut report = String::from_utf8_lossy(&output.stdout).into_owned();
    report.push_str(&String::from_utf8_lossy(&output.stderr));
    Ok(Some(report))
}

/// The uv invocations that build a fresh kernel venv from the local runtime
/// source: a uv-managed Python, a bare venv (no `--seed`: seeding resolves
/// unpinned pip/setuptools from an index), the runtime's hash-locked
/// requirements (exact pins, `--require-hashes`, wheels only, so no sdist
/// build script ever runs), then the runtime itself from its local
/// directory with [`LOCAL_INSTALL_FLAGS`]. Nothing here names a package an
/// index could resolve to unreviewed code.
fn venv_build_commands(venv: &Path, python: &str, runtime_source: &Path) -> Vec<Vec<String>> {
    let mut requirements = uv_pip_args("install", python);
    requirements.extend(
        ["--require-hashes", "--only-binary", ":all:", "-r"]
            .into_iter()
            .map(String::from),
    );
    requirements.push(
        runtime_source
            .join(RUNTIME_LOCK_FILE)
            .to_string_lossy()
            .into_owned(),
    );
    let mut runtime = uv_pip_args("install", python);
    runtime.extend(LOCAL_INSTALL_FLAGS.into_iter().map(String::from));
    runtime.push(runtime_source.to_string_lossy().into_owned());
    vec![
        ["python", "install", "--no-config", PYTHON_VERSION]
            .into_iter()
            .map(String::from)
            .collect(),
        vec![
            "venv".to_string(),
            "--no-config".to_string(),
            venv.to_string_lossy().into_owned(),
            "--python".to_string(),
            PYTHON_VERSION.to_string(),
        ],
        requirements,
        runtime,
    ]
}

pub(crate) async fn bootstrap_venv(
    venv: &Path,
    python_skills: &[BootstrapPythonSkill],
    options: &EnsureKernelPythonOptions,
) -> anyhow::Result<()> {
    // The runtime source first: a broken install reports its root cause,
    // not a missing uv.
    let source_dir = resolve_runtime_source_dir()?;
    let runtime_identity = hash_runtime_source(&source_dir)?;
    std::fs::create_dir_all(venv.parent().unwrap_or(Path::new("/")))?;
    let uv = ensure_uv()?;
    let python = kernel_venv_python(venv);
    let python_str = python.to_string_lossy().to_string();
    for command in venv_build_commands(venv, &python_str, &source_dir) {
        run_async(&uv, &command).await?;
    }
    if let Some(report) = uv_pip_check(&uv, &python_str).await? {
        return Err(anyhow!(
            "the kernel venv built from {} has unsatisfied requirements:\n{report}",
            source_dir.join(RUNTIME_LOCK_FILE).display()
        ));
    }
    sync_python_skills(
        &uv,
        venv,
        &python,
        &runtime_identity,
        python_skills,
        options,
    )
    .await
}

/// One editable install of `skills` with [`LOCAL_INSTALL_FLAGS`]: a skill's
/// declared dependencies are never resolved, only checked afterwards
/// against the hash-locked venv.
fn skill_install_args(python: &str, skills: &[&BootstrapPythonSkill]) -> Vec<String> {
    let mut args = uv_pip_args("install", python);
    args.extend(LOCAL_INSTALL_FLAGS.into_iter().map(String::from));
    for skill in skills {
        args.push("--editable".to_string());
        args.push(skill.package_path.clone());
    }
    args
}

/// Install/refresh the editable Python skills recorded in the version file.
/// The version file is a shared cache, not a per-session manifest: records
/// from other sessions carry over, and only skills missing or changed are
/// installed. Skills install without their dependencies; a skill whose
/// declared dependencies the hash-locked venv does not satisfy is
/// uninstalled again. Per-skill failures warn and continue: one broken
/// skill must not cost the kernel.
pub(crate) async fn sync_python_skills(
    uv: &str,
    venv: &Path,
    python: &Path,
    runtime_identity: &str,
    python_skills: &[BootstrapPythonSkill],
    options: &EnsureKernelPythonOptions,
) -> anyhow::Result<()> {
    let version = read_bootstrap_version(venv);
    // Previously installed skills still present on disk: their records carry
    // over so sessions with different skill sets share one venv cache
    // instead of forcing reinstalls of each other's skills. Records for
    // skills whose package path disappeared (a retired release dir, a
    // deleted project) cannot serve a future install and are dropped.
    let current_python_skills: HashMap<String, BootstrapPythonSkill> = version
        .as_ref()
        .and_then(|v| v.python_skills.clone())
        .unwrap_or_default()
        .into_iter()
        .filter(|recorded| Path::new(&recorded.package_path).is_dir())
        .map(|s| (bootstrap_skill_key(&s), s))
        .collect();
    let python_str = python.to_string_lossy().to_string();
    let mut installed: HashMap<String, BootstrapPythonSkill> = current_python_skills;
    let mut missing: Vec<&BootstrapPythonSkill> = Vec::new();
    for skill in python_skills {
        let key = bootstrap_skill_key(skill);
        if installed.get(&key).is_some_and(|existing| {
            existing.pyproject_path == skill.pyproject_path
                && existing.pyproject_hash == skill.pyproject_hash
        }) {
            continue;
        }
        missing.push(skill);
    }
    let mut newly_installed: Vec<&BootstrapPythonSkill> = Vec::new();
    if !missing.is_empty() {
        // One uv invocation installs the whole batch of missing skills: a
        // fresh kernel bootstrap otherwise pays one process plus build-backend
        // startup per metadata-only editable install (measured: nine serial
        // installs ~1.9s, one batched invocation ~0.4s, warm uv cache). A
        // batch failure falls back to the per-skill loop so one broken skill
        // still costs only its own warning and never blocks the rest.
        if run_async(uv, &skill_install_args(&python_str, &missing))
            .await
            .is_ok()
        {
            newly_installed.clone_from(&missing);
        } else {
            for skill in &missing {
                match run_async(uv, &skill_install_args(&python_str, &[skill])).await {
                    Ok(()) => newly_installed.push(skill),
                    Err(error) => options.report(&format!(
                        "Warning: Python skill {} failed to install and will be unavailable: {error}",
                        skill.import_name
                    )),
                }
            }
        }
    }
    if !newly_installed.is_empty() {
        let report = uv_pip_check(uv, &python_str).await?.unwrap_or_default();
        let unsatisfied = unsatisfied_requirements(&report);
        let mut attributed = false;
        for skill in newly_installed {
            let project = read_python_skill_project_name(skill);
            let Some(lines) = unsatisfied.get(&normalize_distribution_name(&project)) else {
                // A changed pyproject (hash moved) replaces the stale record.
                installed.insert(bootstrap_skill_key(skill), skill.clone());
                continue;
            };
            attributed = true;
            let mut uninstall = uv_pip_args("uninstall", &python_str);
            uninstall.push(project);
            let removal = match run_async(uv, &uninstall).await {
                Ok(()) => String::new(),
                Err(error) => format!(" (removing it failed: {error})"),
            };
            options.report(&format!(
                "Warning: Python skill {} needs packages the hash-locked kernel venv does not provide and will be unavailable{removal}:\n{}",
                skill.import_name,
                lines.join("\n")
            ));
        }
        if !attributed && !report.is_empty() {
            options.report(&format!(
                "Warning: the kernel venv has unsatisfied requirements:\n{report}"
            ));
        }
    }
    let mut merged: Vec<BootstrapPythonSkill> = installed.into_values().collect();
    merged.sort_by(|a, b| {
        a.package_path
            .cmp(&b.package_path)
            .then(a.import_name.cmp(&b.import_name))
    });
    write_bootstrap_version(venv, runtime_identity, &merged)
}

pub(crate) fn kernel_base_ready(python: &str, venv: &Path, runtime_identity: &str) -> bool {
    let (version, raw) = read_bootstrap_version_raw(venv);
    bootstrap_base_version_current(version, runtime_identity)
        && has_eukhe_runtime_memoized(
            python,
            runtime_identity,
            &raw,
            &installed_runtime_identity(Path::new(python), venv),
            venv,
        )
}

pub(crate) fn kernel_ready(
    python: &str,
    venv: &Path,
    runtime_identity: &str,
    python_skills: &[BootstrapPythonSkill],
) -> bool {
    let (version, raw) = read_bootstrap_version_raw(venv);
    bootstrap_version_current(version.as_ref(), runtime_identity, python_skills)
        && has_eukhe_runtime_memoized(
            python,
            runtime_identity,
            &raw,
            &installed_runtime_identity(Path::new(python), venv),
            venv,
        )
}

#[cfg(test)]
mod tests;
