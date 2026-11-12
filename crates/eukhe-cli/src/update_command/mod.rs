//! `eukhe update`: replaces an install of the release installer with the
//! newest `eukhe-v*` release of gildrb/eukhe. The tarball is checked against
//! the release's SHA256SUMS, unpacked beside the install and run once
//! before the launcher switches to it. Installs another tool owns (Nix,
//! mise, an app bundle, a cargo build) or a directory this user cannot
//! write get the command that updates them, and nothing changes. Only this
//! command fetches releases: nothing checks at startup or in the
//! background.

mod install;
mod release;
mod swap;

use std::path::Path;

use anyhow::{bail, Result};
use eukhe_client::daemon_build::{relation, Build, Relation};

use crate::daemon_discovery::{current_state_root, discover_daemons, DaemonStatus};
use install::{classify, launcher_dir, InstallKind, Installer, Places};
use release::{Release, Releases, PLATFORM};

/// The releases of gildrb/eukhe; `EUKHE_RELEASES_URL` names a mirror with
/// the same layout (`latest/download/<asset>`, `download/<tag>/<asset>`).
const RELEASES_URL: &str = "https://github.com/gildrb/eukhe/releases";
const ENV_RELEASES_URL: &str = "EUKHE_RELEASES_URL";

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
        Ok(()) => 0,
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

async fn update(running: &str, install: Option<&Installer>) -> Result<()> {
    let Some(platform) = PLATFORM else {
        bail!("no eukhe release ships for this platform (releases: darwin-arm64, linux-x64, linux-arm64)");
    };
    let base = std::env::var(ENV_RELEASES_URL)
        .ok()
        .filter(|base| !base.is_empty())
        .unwrap_or_else(|| RELEASES_URL.to_string());
    let releases = Releases::new(&base, running)?;
    let latest = releases.latest().await?;
    println!("Current version: {running}");
    println!("Latest release:  {}", latest.version);
    if !is_newer(running, &latest.version) {
        println!("eukhe is up to date");
        return Ok(());
    }
    let Some(install) = install else {
        println!("Update available: run \"eukhe update\"");
        return Ok(());
    };
    apply(&releases, &latest, platform, install).await?;
    println!("Updated eukhe {running} -> {}", latest.version);
    if let Some(note) = daemon_note(&latest.version) {
        println!("{note}");
    }
    Ok(())
}

/// Download, check, unpack, switch, prune.
async fn apply(
    releases: &Releases,
    latest: &Release,
    platform: &str,
    install: &Installer,
) -> Result<()> {
    let tarball = latest.tarball(platform);
    let sha256 = releases.checksum(latest, &tarball).await?;
    let stage = swap::Stage::create(install, &latest.version)?;
    let archive = stage.path(&tarball);
    println!("Downloading {tarball}");
    releases
        .download(latest, &tarball, &sha256, &archive)
        .await?;
    println!("Verified sha256 {sha256}");
    let staged = swap::unpack(&stage, &archive, &latest.version)?;
    let payload = swap::switch(&stage, &staged, install, &latest.version)?;
    println!("  payload:  {}", payload.display());
    println!("  launcher: {}", install.launcher.display());
    for warning in swap::prune(install, &payload) {
        eprintln!("warning: {warning}");
    }
    Ok(())
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
