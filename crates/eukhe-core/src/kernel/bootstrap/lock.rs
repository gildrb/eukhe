//! The package locks a kernel installs from, and `eukhe kernel lock`.
//!
//! Eukhe's lock (`eukhe-runtime/requirements-kernel.txt`: exact versions
//! with hashes) ships with Eukhe; the kernel installs a package of it the
//! first time a cell imports it (`eukhe-runtime/src/rlm/pip.py`). A package
//! outside it is refused until the project locks it: [`lock_project_packages`]
//! resolves the requirement once, with Eukhe's lock and the project's
//! existing lock as constraints (their pins never move), and records the
//! new exact versions and hashes in `<project>/.eukhe/requirements-kernel.txt`.
//! That file is the project's to commit: every machine then installs the
//! same files.

use std::collections::BTreeMap;
use std::ffi::OsString;
use std::path::{Path, PathBuf};

use anyhow::{bail, Context};

use super::toolchain;

/// The hash-locked requirements file, in `eukhe-runtime/` (Eukhe's lock)
/// and in a project's `.eukhe/` (the project's).
pub(crate) const LOCK_FILE: &str = "requirements-kernel.txt";
/// The project-local configuration directory.
const PROJECT_DIR: &str = ".eukhe";
const PROJECT_LOCK_HEADER: &str = "\
# This project's kernel package lock, written by `eukhe kernel lock <package>`.
# The Python kernel installs these exact versions, checked against these
# hashes, the first time a cell imports them. Commit this file.
";

/// The project lock of the project at `cwd` (it may not exist).
#[must_use]
pub fn project_lock_path(cwd: &Path) -> PathBuf {
    cwd.join(PROJECT_DIR).join(LOCK_FILE)
}

/// The canonical distribution name (PEP 503).
fn normalize(name: &str) -> String {
    let mut normalized = String::with_capacity(name.len());
    let mut separator = false;
    for ch in name.chars() {
        if matches!(ch, '-' | '_' | '.') {
            separator = true;
            continue;
        }
        if separator && !normalized.is_empty() {
            normalized.push('-');
        }
        separator = false;
        normalized.extend(ch.to_lowercase());
    }
    normalized
}

/// One pinned requirement of a lock: its text as the lock has it (the pin
/// line and its hash lines; comments dropped).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Pinned {
    pub(crate) name: String,
    pub(crate) version: String,
    text: String,
}

/// The pinned requirements of a hashed requirements file, in file order.
pub(crate) fn parse_lock(text: &str) -> Vec<Pinned> {
    let mut pins: Vec<Pinned> = Vec::new();
    let mut open = false;
    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        if line.starts_with([' ', '\t']) {
            if let Some(pin) = pins.last_mut().filter(|_| open) {
                pin.text.push('\n');
                pin.text.push_str(line.trim_end());
            }
            continue;
        }
        let Some((name, rest)) = trimmed.split_once("==") else {
            open = false;
            continue;
        };
        let version = rest
            .split([' ', ';', '\\'])
            .next()
            .unwrap_or_default()
            .to_owned();
        pins.push(Pinned {
            name: normalize(name.trim()),
            version,
            text: line.trim_end().to_owned(),
        });
        open = true;
    }
    pins
}

/// What `eukhe kernel lock` did.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProjectLockChange {
    /// The project lock file.
    pub lock: PathBuf,
    /// `name version` of each package the lock gained, sorted.
    pub added: Vec<String>,
}

/// The project lock's new text: its pins and `resolved`'s that Eukhe's lock
/// does not hold, by name; and the `name version` of each one added.
fn merge_project_lock(runtime: &str, project: &str, resolved: &str) -> (String, Vec<String>) {
    let in_runtime: Vec<String> = parse_lock(runtime)
        .into_iter()
        .map(|pin| pin.name)
        .collect();
    let mut pins: BTreeMap<(String, String), Pinned> = BTreeMap::new();
    let key = |pin: &Pinned| {
        // A name pinned per platform keeps one requirement per marker.
        let marker = pin.text.lines().next().unwrap_or_default().to_owned();
        (pin.name.clone(), marker)
    };
    for pin in parse_lock(project) {
        pins.insert(key(&pin), pin);
    }
    let before: Vec<String> = pins.keys().map(|(name, _)| name.clone()).collect();
    let mut added = Vec::new();
    for pin in parse_lock(resolved) {
        if in_runtime.contains(&pin.name) {
            continue;
        }
        if !before.contains(&pin.name) {
            added.push(format!("{} {}", pin.name, pin.version));
        }
        pins.insert(key(&pin), pin);
    }
    added.sort();
    added.dedup();
    let mut text = String::from(PROJECT_LOCK_HEADER);
    for pin in pins.values() {
        text.push_str(&pin.text);
        text.push('\n');
    }
    (text, added)
}

/// `eukhe kernel lock <requirement>...` in the project at `cwd`: resolve
/// the requirements for the pinned Python (every platform), with Eukhe's
/// lock and the project's lock as constraints, and add the new packages'
/// exact versions and hashes to the project lock. Fetches the kernel
/// toolchain first when it is absent; `report` gets its stages.
///
/// # Errors
///
/// Returns an error when the runtime or the toolchain is unavailable, when
/// uv cannot resolve the requirements (no network, a requirement that
/// conflicts with a locked version, a package without a wheel), or when
/// the project lock cannot be written.
pub async fn lock_project_packages(
    cwd: &Path,
    requirements: &[String],
    report: &(dyn Fn(&str) + Send + Sync),
) -> anyhow::Result<ProjectLockChange> {
    if requirements.is_empty() {
        bail!("name at least one package to lock");
    }
    let runtime_lock = super::runtime_lock_file()?;
    let toolchain = toolchain::ensure(&runtime_lock, report).await?;
    let project_lock = project_lock_path(cwd);
    let kernel_dir = toolchain::KernelDir::resolve()?;
    let token = uuid::Uuid::new_v4();
    let input = kernel_dir.path().join(format!("lock-{token}.in"));
    let output = kernel_dir.path().join(format!("lock-{token}.txt"));
    std::fs::write(&input, requirements.join("\n") + "\n")
        .with_context(|| format!("writing {}", input.display()))?;
    let mut args: Vec<OsString> = [
        "pip",
        "compile",
        "--no-config",
        "--universal",
        "--generate-hashes",
        "--no-header",
        "--no-annotate",
        "--only-binary",
        ":all:",
        "--python",
    ]
    .into_iter()
    .map(OsString::from)
    .collect();
    args.push(toolchain.python.clone().into_os_string());
    args.extend(["-c".into(), runtime_lock.clone().into_os_string()]);
    if project_lock.is_file() {
        args.extend(["-c".into(), project_lock.clone().into_os_string()]);
    }
    args.extend([
        input.clone().into_os_string(),
        "-o".into(),
        output.clone().into_os_string(),
    ]);
    report(&format!("Resolving {}...", requirements.join(", ")));
    let compiled = toolchain::run_uv(&toolchain.uv, &args).await;
    let resolved = std::fs::read_to_string(&output);
    for scratch in [&input, &output] {
        let _best_effort = std::fs::remove_file(scratch);
    }
    compiled?;
    let resolved = resolved.context("reading uv's resolution")?;
    let runtime = std::fs::read_to_string(&runtime_lock)
        .with_context(|| format!("reading {}", runtime_lock.display()))?;
    let project = match std::fs::read_to_string(&project_lock) {
        Ok(text) => text,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => String::new(),
        Err(error) => {
            return Err(error).with_context(|| format!("reading {}", project_lock.display()))
        }
    };
    let (text, added) = merge_project_lock(&runtime, &project, &resolved);
    if !added.is_empty() {
        if let Some(parent) = project_lock.parent() {
            std::fs::create_dir_all(parent)
                .with_context(|| format!("creating {}", parent.display()))?;
        }
        std::fs::write(&project_lock, text)
            .with_context(|| format!("writing {}", project_lock.display()))?;
    }
    Ok(ProjectLockChange {
        lock: project_lock,
        added,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const A: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    const B: &str = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";

    #[test]
    fn a_lock_parses_to_its_pins() {
        let text = format!(
            "# header\nPy_YAML==6.0.3 \\\n    --hash=sha256:{A} \\\n    --hash=sha256:{B}\n    # via x\n\
             colorama==0.4.6 ; sys_platform == 'win32' \\\n    --hash=sha256:{A}\n-e .\n    --hash=sha256:{B}\n"
        );
        let pins = parse_lock(&text);
        assert_eq!(
            pins.iter()
                .map(|pin| (pin.name.as_str(), pin.version.as_str()))
                .collect::<Vec<_>>(),
            [("py-yaml", "6.0.3"), ("colorama", "0.4.6")]
        );
        assert_eq!(
            pins[0].text,
            format!("Py_YAML==6.0.3 \\\n    --hash=sha256:{A} \\\n    --hash=sha256:{B}")
        );
    }

    /// A project lock gains the packages Eukhe's lock does not hold and
    /// keeps its own; a package of Eukhe's lock is never copied into it.
    #[test]
    fn a_project_lock_gains_only_what_eukhes_lock_lacks() {
        let runtime = format!("numpy==2.5.4 \\\n    --hash=sha256:{A}\n");
        let project = format!("{PROJECT_LOCK_HEADER}rich==14.0.0 \\\n    --hash=sha256:{A}\n");
        let resolved = format!(
            "numpy==2.5.4 \\\n    --hash=sha256:{A}\nrich==14.0.0 \\\n    --hash=sha256:{A}\n\
             xarray==2026.1.0 \\\n    --hash=sha256:{B}\n"
        );
        let (text, added) = merge_project_lock(&runtime, &project, &resolved);
        assert_eq!(added, ["xarray 2026.1.0"]);
        assert_eq!(
            text,
            format!(
                "{PROJECT_LOCK_HEADER}rich==14.0.0 \\\n    --hash=sha256:{A}\nxarray==2026.1.0 \\\n    --hash=sha256:{B}\n"
            )
        );
        let (again, added) = merge_project_lock(&runtime, &text, &resolved);
        assert_eq!((again, added), (text, Vec::new()));
    }

    /// Every package the prompt offers is in Eukhe's lock, and the lock
    /// pins every requirement to one exact version with a sha256.
    #[test]
    fn eukhes_lock_holds_every_offered_package_with_hashes() {
        let lock = std::fs::read_to_string(
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../eukhe-runtime")
                .join(LOCK_FILE),
        )
        .expect("the checkout's lock");
        let pins = parse_lock(&lock);
        for (distribution, _) in super::super::LOCKED_PACKAGES {
            assert!(
                pins.iter().any(|pin| pin.name == *distribution),
                "{distribution} is offered but not locked"
            );
        }
        assert!(pins.len() >= super::super::LOCKED_PACKAGES.len());
        for pin in &pins {
            assert!(
                pin.text.contains("--hash=sha256:") && !pin.version.is_empty(),
                "{} is not hash-pinned",
                pin.name
            );
        }
    }
}
