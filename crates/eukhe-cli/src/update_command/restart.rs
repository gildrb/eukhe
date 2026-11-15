//! `/restart` for this install ([`Restarter`]): the update the launch check
//! staged is applied by pointing the launcher at it, and the restart runs
//! the launcher, so it starts the payload the install runs now. Outside an
//! install of the release installer the restart runs this executable
//! again. A build reads another's identity by running it with
//! [`BUILD_IDENTITY_FLAG`].

use std::path::Path;
use std::process::Command;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;

use eukhe_client::restart::{Identity, Restarter, Target, STAGED_NOTICE};
use tokio::sync::watch;

use super::install::Installer;
use super::{swap, Voice};

/// The hidden argument that prints this build's version and identity as
/// one JSON line, for the build that restarts into it.
pub(crate) const BUILD_IDENTITY_FLAG: &str = "--build-identity";

/// What [`BUILD_IDENTITY_FLAG`] prints.
#[derive(serde::Serialize, serde::Deserialize)]
struct Printed {
    version: String,
    identity: Identity,
}

/// Prints this build's version and identity (the answer to
/// [`BUILD_IDENTITY_FLAG`]).
pub(crate) fn print_build_identity() -> i32 {
    let printed = Printed {
        version: crate::config::version().to_string(),
        identity: Identity::this(),
    };
    match serde_json::to_string(&printed) {
        Ok(line) => {
            println!("{line}");
            0
        }
        Err(error) => {
            eprintln!("Error: {error}");
            1
        }
    }
}

/// The `/restart` seam of one process: the install it may update, and the
/// update its launch check staged there.
pub(super) struct InstallRestarter {
    /// The install of the release installer this user can write; `None`
    /// for every other install.
    install: Option<Installer>,
    /// The version staged in `install`, until `/restart` applies it.
    staged: watch::Sender<Option<String>>,
    /// The staged notice was shown.
    notice_taken: AtomicBool,
}

impl InstallRestarter {
    pub(super) fn new(install: Option<Installer>) -> Self {
        Self {
            install,
            staged: watch::Sender::new(None),
            notice_taken: AtomicBool::new(false),
        }
    }

    /// The launch check staged `version`.
    pub(super) fn stage(&self, version: String) {
        self.staged.send_replace(Some(version));
    }

    /// Points the install's launcher at the staged version, if one is
    /// staged and still there, and prunes the payloads nothing runs.
    fn apply_staged(&self, install: &Installer) -> Result<(), String> {
        let Some(version) = self.staged.borrow().clone() else {
            return Ok(());
        };
        let Some(payload) = swap::placed_payload(install, &version) else {
            // Something else removed it (an `eukhe update` meanwhile): the
            // launcher names what the install runs now.
            tracing::warn!("the staged eukhe {version} is gone; restarting on the installed one");
            self.staged.send_replace(None);
            return Ok(());
        };
        swap::point_launcher(install, &version)
            .map_err(|error| format!("cannot apply the downloaded update: {error:#}"))?;
        self.staged.send_replace(None);
        for warning in swap::prune(install, &payload) {
            Voice::Log.warn(&warning);
        }
        Ok(())
    }
}

impl Restarter for InstallRestarter {
    fn staged(&self) -> watch::Receiver<Option<String>> {
        self.staged.subscribe()
    }

    fn take_notice(&self) -> Option<String> {
        self.staged.borrow().as_ref()?;
        (!self.notice_taken.swap(true, Ordering::SeqCst)).then(|| STAGED_NOTICE.to_string())
    }

    fn prepare(&self) -> Result<Target, String> {
        match &self.install {
            Some(install) => {
                self.apply_staged(install)?;
                target_of(&install.launcher)
            }
            None => this_target(),
        }
    }

    fn release_wait(&self) -> Duration {
        Duration::from_millis(eukhe_daemon::timeouts::derived().launcher_shutdown_wait_ms)
    }
}

/// This executable, as it runs now.
fn this_target() -> Result<Target, String> {
    let exe =
        std::env::current_exe().map_err(|error| format!("cannot find this executable: {error}"))?;
    Ok(Target {
        exe,
        version: crate::config::version().to_string(),
        identity: Some(Identity::this()),
    })
}

/// The build `exe` runs, as it reports itself: its identity, or only its
/// version when it predates [`BUILD_IDENTITY_FLAG`].
fn target_of(exe: &Path) -> Result<Target, String> {
    let identified = Command::new(exe)
        .arg(BUILD_IDENTITY_FLAG)
        .output()
        .ok()
        .filter(|output| output.status.success())
        .and_then(|output| serde_json::from_slice::<Printed>(&output.stdout).ok());
    if let Some(printed) = identified {
        return Ok(Target {
            exe: exe.to_path_buf(),
            version: printed.version,
            identity: Some(printed.identity),
        });
    }
    let output = Command::new(exe)
        .arg("--version")
        .output()
        .map_err(|error| format!("cannot run {}: {error}", exe.display()))?;
    if !output.status.success() {
        return Err(format!(
            "{} --version failed ({})",
            exe.display(),
            output.status
        ));
    }
    Ok(Target {
        exe: exe.to_path_buf(),
        version: String::from_utf8_lossy(&output.stdout).trim().to_string(),
        identity: None,
    })
}
