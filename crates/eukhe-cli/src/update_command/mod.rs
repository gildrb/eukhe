//! `eukhe update`: replaces an install of the release installer with the
//! newest `eukhe-v*` release of gildrb/eukhe. The tarball is checked against
//! the release's SHA256SUMS, unpacked beside the install and run once
//! before the launcher switches to it. Installs another tool owns (Nix,
//! mise, an app bundle, a cargo build) or a directory this user cannot
//! write get the command that updates them, and nothing changes. An
//! interactive launch runs the same check in the background and stages the
//! release without switching (`launch_check`); `/restart` switches to it
//! (`restart`).

mod install;
mod launch_check;
mod release;
mod restart;
mod swap;

use std::path::Path;

use anyhow::{bail, Result};
use eukhe_client::daemon_build::{relation, Build, Relation};

use crate::daemon_discovery::{current_state_root, discover_daemons, DaemonStatus};
use install::{classify, launcher_dir, InstallKind, Installer, Places};
use release::{Pin, Release, Releases, PLATFORM};

pub(crate) use launch_check::launch_restarter;
pub(crate) use restart::{print_build_identity, BUILD_IDENTITY_FLAG};

/// Where the update steps report: the terminal of `eukhe update`, or the
/// log of a background check that must not write over the TUI.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Voice {
    Terminal,
    Log,
}

impl Voice {
    fn say(self, line: &str) {
        match self {
            Voice::Terminal => println!("{line}"),
            Voice::Log => tracing::info!("{line}"),
        }
    }

    fn warn(self, line: &str) {
        match self {
            Voice::Terminal => eprintln!("warning: {line}"),
            Voice::Log => tracing::warn!("{line}"),
        }
    }
}

/// The releases of gildrb/eukhe; `EUKHE_RELEASES_URL` names a mirror with
/// the same layout (`latest/download/<asset>`, `download/<tag>/<asset>`).
const RELEASES_URL: &str = "https://github.com/gildrb/eukhe/releases";
const ENV_RELEASES_URL: &str = "EUKHE_RELEASES_URL";

/// The release main pins (the Nix flake's), which install.sh also checks a
/// tarball of the newest release against; `EUKHE_RELEASE_PIN_URL` names
/// another copy.
const PIN_URL: &str = "https://raw.githubusercontent.com/gildrb/eukhe/main/nix/release.json";
const ENV_PIN_URL: &str = "EUKHE_RELEASE_PIN_URL";

/// The release installer.
const INSTALL_COMMAND: &str = "curl -fsSL https://eukhe.com/install | sh";

/// What `eukhe update` was asked to do.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Mode {
    /// Print the running and the newest version.
    Check,
    /// Install the newest version.
    Install,
}

/// Runs `eukhe update`; returns the exit code.
pub(crate) fn run(mode: Mode) -> i32 {
    let running = crate::config::version();
    let install = match mode {
        Mode::Check => None,
        Mode::Install => match detect() {
            Ok(InstallKind::Installer(install)) => Some(install),
            Ok(other) => {
                eprintln!("{}", refusal(&other));
                return 1;
            }
            Err(error) => {
                eprintln!("Error: {error:#}");
                return 1;
            }
        },
    };
    let runtime = match tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
    {
        Ok(runtime) => runtime,
        Err(error) => {
            eprintln!("Error: cannot start the async runtime: {error}");
            return 1;
        }
    };
    match runtime.block_on(update(running, install.as_ref())) {
        Ok(installed) => {
            // Outside the runtime: the daemon probe runs one of its own.
            if let Some(note) = installed.as_deref().and_then(daemon_note) {
                println!("{note}");
            }
            0
        }
        Err(error) => {
            eprintln!("Error: {error:#}");
            1
        }
    }
}

/// The kind of the running install.
fn detect() -> Result<InstallKind> {
    let exe = std::env::current_exe()?;
    let exe = exe.canonicalize().unwrap_or(exe);
    Ok(classify(&exe, &Places::of_process()))
}

/// Whether `latest` is a newer version than `running` (the daemon build
/// order of `eukhe-client`: a `-dev` build ranks below the releases of its
/// series).
fn is_newer(running: &str, latest: &str) -> bool {
    let running = Build {
        version: running,
        id: "running",
    };
    let latest = Build {
        version: latest,
        id: "latest",
    };
    relation(running, latest) == Relation::Newer
}

/// The releases this build reads: the mirror and the pin the environment
/// names, else gildrb/eukhe's.
fn releases(running: &str) -> Result<Releases> {
    let url = |key: &str, default: &str| {
        std::env::var(key)
            .ok()
            .filter(|url| !url.is_empty())
            .unwrap_or_else(|| default.to_string())
    };
    Releases::new(
        &url(ENV_RELEASES_URL, RELEASES_URL),
        &url(ENV_PIN_URL, PIN_URL),
        running,
    )
}

/// Checks for, and with an install, installs the newest release; returns
/// the version it installed.
async fn update(running: &str, install: Option<&Installer>) -> Result<Option<String>> {
    let Some(platform) = PLATFORM else {
        bail!("no eukhe release ships for this platform (releases: darwin-arm64, linux-x64, linux-arm64)");
    };
    let releases = releases(running)?;
    let latest = releases.latest().await?;
    println!("Current version: {running}");
    println!("Latest release:  {}", latest.version);
    if !is_newer(running, &latest.version) {
        println!("eukhe is up to date");
        return Ok(None);
    }
    let Some(install) = install else {
        println!("Update available: run \"eukhe update\"");
        return Ok(None);
    };
    apply(&releases, &latest, platform, install).await?;
    println!("Updated eukhe {running} -> {}", latest.version);
    Ok(Some(latest.version))
}

/// Stage, switch, prune.
async fn apply(
    releases: &Releases,
    latest: &Release,
    platform: &str,
    install: &Installer,
) -> Result<()> {
    let payload = stage_release(releases, latest, platform, install, Voice::Terminal).await?;
    swap::point_launcher(install, &latest.version)?;
    println!("  payload:  {}", payload.display());
    println!("  launcher: {}", install.launcher.display());
    for warning in swap::prune(install, &payload) {
        Voice::Terminal.warn(&warning);
    }
    Ok(())
}

/// Download, check and unpack `latest` into `<root>/eukhe-<version>`; the
/// launcher still execs the running payload. Returns the payload.
async fn stage_release(
    releases: &Releases,
    latest: &Release,
    platform: &str,
    install: &Installer,
    voice: Voice,
) -> Result<std::path::PathBuf> {
    let name = latest.archive(platform);
    let sha256 = releases.checksum(latest, &name).await?;
    let stage = swap::Stage::create(install, &latest.version, voice)?;
    let archive = stage.path(&name);
    voice.say(&format!("Downloading {name}"));
    // The pin is fetched while the archive downloads; it is judged first.
    // The download is checked against `sha256`, so a pin that agrees with
    // it agrees with the archive.
    let (pin, download) = tokio::join!(
        releases.pin(latest, &name, &sha256),
        releases.download(latest, &name, &sha256, &archive),
    );
    let verified = match pin? {
        Pin::Same => "SHA256SUMS and nix/release.json".to_string(),
        Pin::OtherVersion(version) => format!("SHA256SUMS (nix/release.json pins {version})"),
        Pin::Unavailable(why) => {
            voice.warn(&format!("{why}: SHA256SUMS verification only"));
            "SHA256SUMS".to_string()
        }
    };
    download?;
    voice.say(&format!("Verified sha256 {sha256} against {verified}"));
    let staged = swap::unpack(&stage, &archive, &latest.version)?;
    let (payload, placed) = swap::place(&stage, &staged, install, &latest.version)?;
    match placed {
        swap::Placed::Moved => {}
        swap::Placed::Kept => voice.say(&format!(
            "eukhe {} is already unpacked: kept {}",
            latest.version,
            payload.display()
        )),
    }
    Ok(payload)
}

/// The note for running daemons of another version: they keep running the
/// binary they started from.
fn daemon_note(version: &str) -> Option<String> {
    let mut versions: Vec<String> = discover_daemons(&current_state_root(None))
        .into_iter()
        .filter(|daemon| matches!(daemon.status, DaemonStatus::Current | DaemonStatus::Stale))
        .filter_map(|daemon| daemon.version)
        .filter(|running| running != version)
        .collect();
    versions.sort();
    versions.dedup();
    if versions.is_empty() {
        return None;
    }
    Some(format!(
        "A running daemon (eukhe {}) keeps the old version until it restarts: the next interactive \"eukhe\" replaces it once it has no work, and \"eukhe shutdown\" stops it and its agents now.",
        versions.join(", ")
    ))
}

/// The refusal for an install this command does not change: what owns it
/// and the command that updates it.
fn refusal(kind: &InstallKind) -> String {
    match kind {
        InstallKind::Installer(install) => format!(
            "Error: {} is an install of the release installer",
            install.payload.display()
        ),
        InstallKind::ReadOnly { dir, install } => format!(
            "Error: {} is not writable by this user. Update the install as a user that can write it:\n  curl -fsSL https://eukhe.com/install | EUKHE_INSTALL_ROOT={} EUKHE_INSTALL_BIN_DIR={} sh",
            dir.display(),
            shell_word(&install.root),
            shell_word(launcher_dir(install)),
        ),
        InstallKind::Nix { exe } => format!(
            "Error: Nix manages this eukhe ({}). Update the flake input that provides it, then rebuild:\n  nix flake update eukhe\nA nix profile install: nix profile upgrade eukhe",
            exe.display()
        ),
        InstallKind::Mise { exe } => format!(
            "Error: mise manages this eukhe ({}). Update it with:\n  mise upgrade github:gildrb/eukhe",
            exe.display()
        ),
        InstallKind::AppBundle { app } => format!(
            "Error: this eukhe ships inside {}. Update the app to update it.",
            app.display()
        ),
        InstallKind::DevBuild { workspace } => format!(
            "Error: this eukhe is a cargo build of {}. Update it with:\n  git -C {} pull && cargo build --release --manifest-path {}",
            workspace.display(),
            shell_word(workspace),
            shell_word(&workspace.join("Cargo.toml")),
        ),
        InstallKind::Unknown { exe } => format!(
            "Error: {} is not an install of the release installer. Install eukhe with:\n  {INSTALL_COMMAND}",
            exe.display()
        ),
    }
}

/// `path` as one shell word.
fn shell_word(path: &Path) -> String {
    let text = path.display().to_string();
    if text
        .bytes()
        .all(|b| b.is_ascii_alphanumeric() || b"/._-+~:@".contains(&b))
    {
        text
    } else {
        format!("'{}'", text.replace('\'', r"'\''"))
    }
}

#[cfg(test)]
mod tests {
    use super::{is_newer, shell_word};
    use std::path::Path;

    #[test]
    fn only_a_higher_version_is_newer() {
        let cases = [
            ("0.10.69", "0.10.70"),
            ("0.10.70", "0.10.70"),
            ("0.10.71", "0.10.70"),
            ("0.10.9", "0.10.10"),
            ("0.10.70", "0.11.0"),
            ("0.10.70-dev", "0.10.70"),
            ("0.10.70", "0.10.70-dev"),
        ]
        .map(|(running, latest)| is_newer(running, latest));
        assert_eq!(cases, [true, false, false, true, true, true, false]);
    }

    #[test]
    fn a_path_with_a_space_is_quoted() {
        assert_eq!(
            [
                shell_word(Path::new("/home/u/.local/bin")),
                shell_word(Path::new("/home/u/my apps")),
            ],
            [
                "/home/u/.local/bin".to_string(),
                "'/home/u/my apps'".to_string()
            ]
        );
    }
}
