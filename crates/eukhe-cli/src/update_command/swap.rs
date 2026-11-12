//! The installer's layout change, done as install.sh does it: a new payload
//! `<root>/eukhe-<version>` from a stage directory beside it, then the
//! launcher replaced by rename. Until that rename the launcher still execs
//! the running payload, so a failure at any earlier step leaves the install
//! as it was. The previous payload stays for a daemon that still runs it.

use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{bail, Context, Result};

use super::install::{launcher_dir, launcher_script, Installer, PAYLOAD_PREFIX};

/// A stage directory in the install root; removed when dropped.
pub(super) struct Stage {
    dir: PathBuf,
}

impl Stage {
    /// `<root>/.stage-eukhe-<version>.<pid>`, the name install.sh stages in.
    pub(super) fn create(install: &Installer, version: &str) -> Result<Self> {
        let dir = install
            .root
            .join(format!(".stage-eukhe-{version}.{}", std::process::id()));
        std::fs::create_dir(&dir).with_context(|| format!("cannot create {}", dir.display()))?;
        Ok(Self { dir })
    }

    pub(super) fn path(&self, name: &str) -> PathBuf {
        self.dir.join(name)
    }
}

impl Drop for Stage {
    fn drop(&mut self) {
        if let Err(error) = std::fs::remove_dir_all(&self.dir) {
            eprintln!(
                "warning: cannot remove the stage directory {}: {error}",
                self.dir.display()
            );
        }
    }
}

/// Unpacks the verified `tarball` into the stage and checks that its
/// `eukhe` runs and reports `version`; returns the staged payload.
pub(super) fn unpack(stage: &Stage, tarball: &Path, version: &str) -> Result<PathBuf> {
    let payload = stage.path("payload");
    let file = std::fs::File::open(tarball)
        .with_context(|| format!("cannot open {}", tarball.display()))?;
    let mut archive = tar::Archive::new(flate2::read::GzDecoder::new(file));
    archive.set_preserve_permissions(true);
    archive
        .unpack(&payload)
        .with_context(|| format!("cannot unpack {}", tarball.display()))?;
    let binary = payload.join("eukhe");
    if !binary.is_file() {
        bail!("the release tarball has no eukhe binary");
    }
    // The staged manifest decides the reported version, as it will once
    // installed; an inherited EUKHE_PACKAGE_DIR must not answer instead.
    let output = Command::new(&binary)
        .arg("--version")
        .env("EUKHE_PACKAGE_DIR", &payload)
        .output()
        .with_context(|| {
            format!(
                "the downloaded eukhe does not run on this machine ({})",
                binary.display()
            )
        })?;
    let reported = String::from_utf8_lossy(&output.stdout).trim().to_string();
    if !output.status.success() || reported != version {
        bail!("the downloaded eukhe reports {reported:?}, expected {version:?}");
    }
    Ok(payload)
}

/// Moves the staged payload to `<root>/eukhe-<version>` and points the
/// launcher at it. A payload of that version already there that reports it
/// is kept, as install.sh keeps it.
pub(super) fn switch(
    stage: &Stage,
    staged: &Path,
    install: &Installer,
    version: &str,
) -> Result<PathBuf> {
    let name = format!("{PAYLOAD_PREFIX}{version}");
    let payload = install.root.join(&name);
    if payload.exists() {
        if reports(&payload, version) {
            eprintln!(
                "eukhe {version} is already unpacked: kept {}",
                payload.display()
            );
        } else {
            // A broken earlier copy: moved into the stage, removed with it.
            let replaced = stage.path("replaced");
            std::fs::rename(&payload, &replaced)
                .with_context(|| format!("cannot move {} aside", payload.display()))?;
            std::fs::rename(staged, &payload)
                .with_context(|| format!("cannot move the new payload to {}", payload.display()))?;
        }
    } else {
        std::fs::rename(staged, &payload)
            .with_context(|| format!("cannot move the new payload to {}", payload.display()))?;
    }
    let dir = launcher_dir(install);
    let temp = dir.join(format!(".eukhe-installer.{}", std::process::id()));
    write_launcher(&temp, &install.launcher_root.join(&name))
        .with_context(|| format!("cannot write {}", temp.display()))?;
    if let Err(error) = std::fs::rename(&temp, &install.launcher) {
        let removed = std::fs::remove_file(&temp);
        return Err(error).with_context(|| match removed {
            Ok(()) => format!("cannot replace {}", install.launcher.display()),
            Err(remove) => format!(
                "cannot replace {} (and cannot remove {}: {remove})",
                install.launcher.display(),
                temp.display()
            ),
        });
    }
    Ok(payload)
}

/// Removes the payloads other than `current` and the running one, as
/// install.sh prunes; reports what it could not remove.
pub(super) fn prune(install: &Installer, current: &Path) -> Vec<String> {
    let entries = match std::fs::read_dir(&install.root) {
        Ok(entries) => entries,
        Err(error) => return vec![format!("cannot list {}: {error}", install.root.display())],
    };
    entries
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| {
            path.is_dir()
                && path
                    .file_name()
                    .and_then(|name| name.to_str())
                    .is_some_and(|name| name.starts_with(PAYLOAD_PREFIX))
                && path != current
                && path != &install.payload
        })
        .filter_map(|path| {
            std::fs::remove_dir_all(&path)
                .err()
                .map(|error| format!("cannot remove {}: {error}", path.display()))
        })
        .collect()
}

fn write_launcher(temp: &Path, payload: &Path) -> std::io::Result<()> {
    use std::os::unix::fs::PermissionsExt;
    std::fs::write(temp, launcher_script(payload))?;
    std::fs::set_permissions(temp, std::fs::Permissions::from_mode(0o755))
}

/// Whether the payload's `eukhe` reports `version`.
fn reports(payload: &Path, version: &str) -> bool {
    Command::new(payload.join("eukhe"))
        .arg("--version")
        .env("EUKHE_PACKAGE_DIR", payload)
        .output()
        .is_ok_and(|output| {
            output.status.success() && String::from_utf8_lossy(&output.stdout).trim() == version
        })
}
