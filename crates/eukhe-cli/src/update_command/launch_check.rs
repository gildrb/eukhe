//! The update check of an interactive launch. It runs on a thread of its
//! own, so the first frame never waits for it: it reads the newest release
//! as `eukhe update` does and, when that is newer than this build,
//! downloads, checks and unpacks it beside the install, leaving the
//! launcher on the running payload (`stage_release`). `/restart` switches
//! to it. A launch checks only an install of the release installer that
//! this user can write, outside CI and offline mode, with
//! `update.autoDownload` on; every other launch skips the check without a
//! word.

use std::sync::Arc;

use eukhe_client::restart::SharedRestarter;

use super::install::{InstallKind, Installer};
use super::restart::InstallRestarter;
use super::{detect, is_newer, releases, stage_release, swap, Voice, PLATFORM};

/// Why a launch does not check for an update.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Skip {
    /// `update.autoDownload` is off.
    TurnedOff,
    /// A CI run (`CI` set to a true value).
    Ci,
    /// Offline mode (`--offline`, `EUKHE_OFFLINE`).
    Offline,
    /// No release ships for this platform.
    NoRelease,
    /// Another tool owns the install (Nix, mise, an app bundle, a cargo
    /// build, a binary placed by hand), or this user cannot write it.
    NotOurs,
}

/// What a launch does about updates.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Check {
    Skip(Skip),
    /// Check, and stage a newer release into this install.
    Run {
        install: Installer,
        platform: &'static str,
    },
}

/// What the check is decided on.
struct Facts {
    /// The `update.autoDownload` setting.
    auto_download: bool,
    /// `CI` is set to a true value.
    ci: bool,
    /// Offline mode is on.
    offline: bool,
    /// The release platform of this build.
    platform: Option<&'static str>,
    /// The running install.
    install: InstallKind,
}

/// Whether and where a launch checks.
fn decide(facts: Facts) -> Check {
    let skip = [
        (!facts.auto_download).then_some(Skip::TurnedOff),
        facts.ci.then_some(Skip::Ci),
        facts.offline.then_some(Skip::Offline),
    ]
    .into_iter()
    .flatten()
    .next();
    if let Some(skip) = skip {
        return Check::Skip(skip);
    }
    let Some(platform) = facts.platform else {
        return Check::Skip(Skip::NoRelease);
    };
    match facts.install {
        InstallKind::Installer(install) => Check::Run { install, platform },
        InstallKind::ReadOnly { .. }
        | InstallKind::Nix { .. }
        | InstallKind::Mise { .. }
        | InstallKind::AppBundle { .. }
        | InstallKind::DevBuild { .. }
        | InstallKind::Unknown { .. } => Check::Skip(Skip::NotOurs),
    }
}

/// The `/restart` seam of an interactive launch, with the launch's update
/// check started behind it when the launch checks.
pub(crate) fn launch_restarter(auto_download: bool) -> SharedRestarter {
    let install = match detect() {
        Ok(install) => install,
        Err(error) => {
            tracing::warn!("cannot read the running install: {error:#}");
            return Arc::new(InstallRestarter::new(None));
        }
    };
    let writable = match &install {
        InstallKind::Installer(install) => Some(install.clone()),
        InstallKind::ReadOnly { .. }
        | InstallKind::Nix { .. }
        | InstallKind::Mise { .. }
        | InstallKind::AppBundle { .. }
        | InstallKind::DevBuild { .. }
        | InstallKind::Unknown { .. } => None,
    };
    let restarter = Arc::new(InstallRestarter::new(writable));
    let check = decide(Facts {
        auto_download,
        ci: crate::config::is_truthy_env_flag(std::env::var("CI").ok().as_deref()),
        offline: crate::config::is_truthy_env_flag(
            std::env::var(crate::config::ENV_OFFLINE).ok().as_deref(),
        ),
        platform: PLATFORM,
        install,
    });
    match check {
        Check::Skip(skip) => tracing::debug!(?skip, "the launch update check is skipped"),
        Check::Run { install, platform } => spawn(install, platform, Arc::clone(&restarter)),
    }
    restarter
}

/// Run the check on its own thread and runtime; a staged release lands in
/// `restarter`. A failure (offline, a refused checksum) is logged only.
fn spawn(install: Installer, platform: &'static str, restarter: Arc<InstallRestarter>) {
    let spawned = std::thread::Builder::new()
        .name("update-check".to_string())
        .spawn(move || {
            for warning in swap::sweep_stages(&install) {
                Voice::Log.warn(&warning);
            }
            let running = crate::config::version();
            // An update an earlier launch staged needs no network.
            if let Some(version) = swap::newest_placed(&install, running) {
                restarter.stage(version);
            }
            let runtime = match tokio::runtime::Builder::new_current_thread()
                .enable_all()
                .build()
            {
                Ok(runtime) => runtime,
                Err(error) => {
                    tracing::warn!("the launch update check cannot start a runtime: {error}");
                    return;
                }
            };
            match runtime.block_on(stage_newest(&install, platform, running)) {
                Ok(Some(version)) => restarter.stage(version),
                Ok(None) => {}
                Err(error) => tracing::info!("the launch update check stopped: {error:#}"),
            }
        });
    if let Err(error) = spawned {
        tracing::warn!("cannot start the launch update check: {error}");
    }
}

/// The newest release, staged into `install` when it is newer than the
/// `running` build (an earlier launch may have staged it already); its
/// version.
async fn stage_newest(
    install: &Installer,
    platform: &str,
    running: &str,
) -> anyhow::Result<Option<String>> {
    let releases = releases(running)?;
    let latest = releases.latest().await?;
    if !is_newer(running, &latest.version) {
        return Ok(None);
    }
    if swap::placed_payload(install, &latest.version).is_none() {
        stage_release(&releases, &latest, platform, install, Voice::Log).await?;
    }
    Ok(Some(latest.version))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn installer() -> Installer {
        Installer {
            root: PathBuf::from("/home/u/.local/share/eukhe"),
            payload: PathBuf::from("/home/u/.local/share/eukhe/eukhe-0.10.1"),
            launcher: PathBuf::from("/home/u/.local/bin/eukhe"),
            launcher_root: PathBuf::from("/home/u/.local/share/eukhe"),
        }
    }

    fn facts(install: InstallKind) -> Facts {
        Facts {
            auto_download: true,
            ci: false,
            offline: false,
            platform: Some("linux-x64"),
            install,
        }
    }

    #[test]
    fn only_a_writable_installer_install_is_checked() {
        let exe = PathBuf::from("/x/eukhe");
        let kinds = [
            InstallKind::Installer(installer()),
            InstallKind::ReadOnly {
                dir: PathBuf::from("/opt"),
                install: installer(),
            },
            InstallKind::Nix { exe: exe.clone() },
            InstallKind::Mise { exe: exe.clone() },
            InstallKind::AppBundle {
                app: PathBuf::from("/Applications/Eukhe.app"),
            },
            InstallKind::DevBuild {
                workspace: PathBuf::from("/src/eukhe"),
            },
            InstallKind::Unknown { exe },
        ];
        let checks: Vec<Check> = kinds.into_iter().map(|kind| decide(facts(kind))).collect();
        let not_ours = Check::Skip(Skip::NotOurs);
        assert_eq!(
            checks,
            vec![
                Check::Run {
                    install: installer(),
                    platform: "linux-x64"
                },
                not_ours.clone(),
                not_ours.clone(),
                not_ours.clone(),
                not_ours.clone(),
                not_ours.clone(),
                not_ours,
            ]
        );
    }

    #[test]
    fn the_setting_ci_offline_and_platform_each_skip_the_check() {
        let installer = || InstallKind::Installer(installer());
        let checks = [
            Facts {
                auto_download: false,
                ..facts(installer())
            },
            Facts {
                ci: true,
                ..facts(installer())
            },
            Facts {
                offline: true,
                ..facts(installer())
            },
            Facts {
                platform: None,
                ..facts(installer())
            },
        ]
        .map(decide);
        assert_eq!(
            checks,
            [
                Check::Skip(Skip::TurnedOff),
                Check::Skip(Skip::Ci),
                Check::Skip(Skip::Offline),
                Check::Skip(Skip::NoRelease),
            ]
        );
    }
}
