//! The installer's layout change, done as install.sh does it: a new payload
//! `<root>/eukhe-<version>` from a stage directory beside it, then the
//! launcher replaced by rename. Until that rename the launcher still execs
//! the running payload, so a failure at any earlier step, or a crash, leaves
//! the install as it was. A payload placed but not yet switched to is a
//! staged update (`/restart` switches to it). The previous payload stays for
//! a daemon that still runs it.

use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{bail, Context, Result};

use super::install::{launcher_dir, launcher_script, Installer, PAYLOAD_PREFIX};
use super::Voice;

/// The stage directory name's prefix (`.stage-eukhe-<version>.<pid>`).
const STAGE_PREFIX: &str = ".stage-eukhe-";

/// A stage directory in the install root; removed when dropped.
pub(super) struct Stage {
    dir: PathBuf,
    voice: Voice,
}

impl Stage {
    /// `<root>/.stage-eukhe-<version>.<pid>`, the name install.sh stages in.
    pub(super) fn create(install: &Installer, version: &str, voice: Voice) -> Result<Self> {
        let dir = install
            .root
            .join(format!("{STAGE_PREFIX}{version}.{}", std::process::id()));
        std::fs::create_dir(&dir).with_context(|| format!("cannot create {}", dir.display()))?;
        Ok(Self { dir, voice })
    }

    pub(super) fn path(&self, name: &str) -> PathBuf {
        self.dir.join(name)
    }
}

impl Drop for Stage {
    fn drop(&mut self) {
        if let Err(error) = std::fs::remove_dir_all(&self.dir) {
            self.voice.warn(&format!(
                "cannot remove the stage directory {}: {error}",
                self.dir.display()
            ));
        }
    }
}

/// Where [`place`] left the payload.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Placed {
    /// The staged payload moved into the root.
    Moved,
    /// A payload of that version already there, which reports it, was kept.
    Kept,
}

/// Unpacks the verified `.tar.xz` `tarball` into the stage and checks that its
/// `eukhe` runs and reports `version`; returns the staged payload.
pub(super) fn unpack(stage: &Stage, tarball: &Path, version: &str) -> Result<PathBuf> {
    let payload = stage.path("payload");
    let file = std::fs::File::open(tarball)
        .with_context(|| format!("cannot open {}", tarball.display()))?;
    let mut archive = tar::Archive::new(liblzma::read::XzDecoder::new(file));
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

/// Moves the staged payload to `<root>/eukhe-<version>`; the launcher still
/// execs the running payload. A payload of that version already there that
/// reports it is kept, as install.sh keeps it.
pub(super) fn place(
    stage: &Stage,
    staged: &Path,
    install: &Installer,
    version: &str,
) -> Result<(PathBuf, Placed)> {
    let payload = payload_path(install, version);
    if payload.exists() {
        if reports(&payload, version) {
            return Ok((payload, Placed::Kept));
        }
        // A broken earlier copy: moved into the stage, removed with it.
        let replaced = stage.path("replaced");
        std::fs::rename(&payload, &replaced)
            .with_context(|| format!("cannot move {} aside", payload.display()))?;
    }
    std::fs::rename(staged, &payload)
        .with_context(|| format!("cannot move the new payload to {}", payload.display()))?;
    Ok((payload, Placed::Moved))
}

/// Points the launcher at `<root>/eukhe-<version>` by rename.
pub(super) fn point_launcher(install: &Installer, version: &str) -> Result<()> {
    let name = format!("{PAYLOAD_PREFIX}{version}");
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
    Ok(())
}

/// `<root>/eukhe-<version>`.
pub(super) fn payload_path(install: &Installer, version: &str) -> PathBuf {
    install.root.join(format!("{PAYLOAD_PREFIX}{version}"))
}

/// The payload of `version` in the root, when one is there and reports it.
pub(super) fn placed_payload(install: &Installer, version: &str) -> Option<PathBuf> {
    let payload = payload_path(install, version);
    reports(&payload, version).then_some(payload)
}

/// The newest version above `running` whose payload sits in the root and
/// reports it: an update an earlier launch staged.
pub(super) fn newest_placed(install: &Installer, running: &str) -> Option<String> {
    let versions: Vec<String> = std::fs::read_dir(&install.root)
        .ok()?
        .filter_map(Result::ok)
        .filter_map(|entry| {
            let name = entry.file_name().into_string().ok()?;
            name.strip_prefix(PAYLOAD_PREFIX).map(str::to_string)
        })
        .filter(|version| super::is_newer(running, version))
        .collect();
    let newest = versions
        .iter()
        .fold(None::<&String>, |newest, version| match newest {
            Some(newest) if !super::is_newer(newest, version) => Some(newest),
            Some(_) | None => Some(version),
        })?;
    placed_payload(install, newest).map(|_| newest.clone())
}

/// Removes the stage directories a crashed update or install left (their
/// process is gone); reports what it could not remove.
pub(super) fn sweep_stages(install: &Installer) -> Vec<String> {
    let entries = match std::fs::read_dir(&install.root) {
        Ok(entries) => entries,
        Err(error) => return vec![format!("cannot list {}: {error}", install.root.display())],
    };
    entries
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.is_dir() && stage_owner(path).is_some_and(owner_gone))
        .filter_map(|path| {
            std::fs::remove_dir_all(&path)
                .err()
                .map(|error| format!("cannot remove {}: {error}", path.display()))
        })
        .collect()
}

/// The pid a stage directory is named after (`.stage-eukhe-<version>.<pid>`).
fn stage_owner(path: &Path) -> Option<u32> {
    let name = path.file_name()?.to_str()?.strip_prefix(STAGE_PREFIX)?;
    name.rsplit_once('.')?.1.parse().ok()
}

/// Whether the stage directory's owner no longer stages: no process `pid`
/// runs (a failed probe keeps the directory), or it is this process, which
/// sweeps before it stages (a process an earlier one `exec`ed into keeps
/// its pid).
fn owner_gone(pid: u32) -> bool {
    pid == std::process::id()
        || matches!(
            eukhe_types::platform::process::is_process_alive(pid),
            Ok(false)
        )
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
