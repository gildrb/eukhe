//! What installed the running `eukhe`, read from the resolved path of the
//! executable: the release installer (`install.sh`: a payload
//! `<root>/eukhe-<version>/eukhe` and a launcher script that execs it), or a
//! tool that owns the file (Nix, mise, an app bundle, a cargo build).

use std::ffi::OsStr;
use std::path::{Path, PathBuf};

/// The release installer's payload directory prefix (`eukhe-<version>`).
pub(super) const PAYLOAD_PREFIX: &str = "eukhe-";

/// The Nix store: what lives there is read-only and owned by Nix.
const NIX_STORE: &str = "/nix/store";

/// An install of the release installer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Installer {
    /// The payload root (`EUKHE_INSTALL_ROOT`), resolved.
    pub root: PathBuf,
    /// The running payload, `<root>/eukhe-<version>`, resolved.
    pub payload: PathBuf,
    /// The launcher script that execs the running payload.
    pub launcher: PathBuf,
    /// The root as the launcher spells it: the new launcher keeps that form.
    pub launcher_root: PathBuf,
}

/// What installed the running executable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum InstallKind {
    /// The release installer, with a writable root and launcher directory.
    Installer(Installer),
    /// The release installer, but `dir` (the root or the launcher's
    /// directory) is not writable by this user.
    ReadOnly { dir: PathBuf, install: Installer },
    /// A Nix store path.
    Nix { exe: PathBuf },
    /// A mise-managed install (under mise's installs directory).
    Mise { exe: PathBuf },
    /// A binary inside the app bundle `app`.
    AppBundle { app: PathBuf },
    /// A cargo build in the `target` directory of the checkout `workspace`.
    DevBuild { workspace: PathBuf },
    /// None of the above: a binary placed by hand.
    Unknown { exe: PathBuf },
}

/// The places detection reads besides the executable's own path.
#[derive(Debug, Clone, Default)]
pub(super) struct Places {
    /// mise's data directory (`MISE_DATA_DIR`, else `$XDG_DATA_HOME/mise`,
    /// else `~/.local/share/mise`).
    pub mise_data_dir: Option<PathBuf>,
    /// Directories that may hold the installer's launcher, in search order.
    pub launcher_dirs: Vec<PathBuf>,
}

impl Places {
    /// The places of this process: its environment and `PATH`.
    pub(super) fn of_process() -> Self {
        let home = eukhe_types::platform::home_dir();
        let env_dir = |key: &str| {
            std::env::var_os(key)
                .filter(|value| !value.is_empty())
                .map(PathBuf::from)
        };
        let mise_data_dir = env_dir("MISE_DATA_DIR")
            .or_else(|| env_dir("XDG_DATA_HOME").map(|dir| dir.join("mise")))
            .or_else(|| home.as_ref().map(|home| home.join(".local/share/mise")));
        let mut launcher_dirs: Vec<PathBuf> = Vec::new();
        let candidates = env_dir("EUKHE_INSTALL_BIN_DIR")
            .into_iter()
            .chain(home.as_ref().map(|home| home.join(".local/bin")))
            .chain(
                std::env::var_os("PATH")
                    .map_or_default(|path| std::env::split_paths(&path).collect::<Vec<_>>()),
            );
        for dir in candidates {
            if !dir.as_os_str().is_empty() && !launcher_dirs.contains(&dir) {
                launcher_dirs.push(dir);
            }
        }
        Self {
            mise_data_dir,
            launcher_dirs,
        }
    }
}

/// The kind of install whose executable resolves to `exe` (already
/// canonical).
pub(super) fn classify(exe: &Path, places: &Places) -> InstallKind {
    if exe.starts_with(NIX_STORE) {
        return InstallKind::Nix {
            exe: exe.to_path_buf(),
        };
    }
    if let Some(app) = exe.ancestors().find(|dir| {
        dir.extension() == Some(OsStr::new("app")) && exe.starts_with(dir.join("Contents"))
    }) {
        return InstallKind::AppBundle {
            app: app.to_path_buf(),
        };
    }
    if let Some(mise) = &places.mise_data_dir {
        let installs = mise.join("installs");
        let installs = installs.canonicalize().unwrap_or(installs);
        if exe.starts_with(&installs) {
            return InstallKind::Mise {
                exe: exe.to_path_buf(),
            };
        }
    }
    if let Some(workspace) = exe
        .ancestors()
        .filter(|dir| dir.file_name() == Some(OsStr::new("target")))
        .filter_map(Path::parent)
        .find(|workspace| workspace.join("Cargo.toml").is_file())
    {
        return InstallKind::DevBuild {
            workspace: workspace.to_path_buf(),
        };
    }
    match installer_install(exe, places) {
        Some(install) => {
            let read_only = [install.root.as_path(), launcher_dir(&install)]
                .into_iter()
                .find(|dir| !writable(dir))
                .map(Path::to_path_buf);
            match read_only {
                Some(dir) => InstallKind::ReadOnly { dir, install },
                None => InstallKind::Installer(install),
            }
        }
        None => InstallKind::Unknown {
            exe: exe.to_path_buf(),
        },
    }
}

/// The directory of the install's launcher.
pub(super) fn launcher_dir(install: &Installer) -> &Path {
    install.launcher.parent().unwrap_or(Path::new("/"))
}

/// The installer's install that runs `exe`: its payload directory is named
/// `eukhe-<version>` and a launcher in `places` execs it.
fn installer_install(exe: &Path, places: &Places) -> Option<Installer> {
    let payload = exe.parent()?;
    let named = payload
        .file_name()?
        .to_str()?
        .strip_prefix(PAYLOAD_PREFIX)
        .is_some_and(|version| !version.is_empty());
    if !named || exe.file_name() != Some(OsStr::new("eukhe")) {
        return None;
    }
    let root = payload.parent()?;
    places.launcher_dirs.iter().find_map(|dir| {
        let launcher = dir.join("eukhe");
        let written = launcher_payload(&launcher)?;
        (written.canonicalize().ok()? == payload).then(|| Installer {
            root: root.to_path_buf(),
            payload: payload.to_path_buf(),
            launcher_root: written.parent().unwrap_or(root).to_path_buf(),
            launcher,
        })
    })
}

/// The launcher install.sh writes for `payload`: the script, byte for byte.
pub(super) fn launcher_script(payload: &Path) -> String {
    format!(
        "#!/bin/sh\n# eukhe launcher written by install.sh; the payload sits beside itself\nexec \"{}/eukhe\" \"$@\"\n",
        payload.display()
    )
}

/// The payload a launcher script of install.sh execs, if `launcher` is one.
fn launcher_payload(launcher: &Path) -> Option<PathBuf> {
    // A launcher is three short lines; a large file is some other `eukhe`.
    const MAX_LAUNCHER_BYTES: u64 = 4096;
    if std::fs::metadata(launcher).ok()?.len() > MAX_LAUNCHER_BYTES {
        return None;
    }
    let script = std::fs::read_to_string(launcher).ok()?;
    let mut lines = script.lines();
    if lines.next() != Some("#!/bin/sh") {
        return None;
    }
    lines.find_map(|line| {
        line.strip_prefix("exec \"")?
            .strip_suffix("/eukhe\" \"$@\"")
            .map(PathBuf::from)
    })
}

/// Whether this user can create a file in `dir` (a probe file, removed at
/// once).
fn writable(dir: &Path) -> bool {
    let probe = dir.join(format!(".eukhe-update-probe.{}", std::process::id()));
    match std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&probe)
    {
        Ok(_) => std::fs::remove_file(&probe).is_ok(),
        Err(_) => false,
    }
}

#[cfg(test)]
mod tests {
    use super::{classify, launcher_script, InstallKind, Installer, Places};
    use std::path::{Path, PathBuf};

    fn places(launcher_dirs: Vec<PathBuf>) -> Places {
        Places {
            mise_data_dir: Some(PathBuf::from("/home/u/.local/share/mise")),
            launcher_dirs,
        }
    }

    /// An installer layout in `dir`: `root/eukhe-0.10.69/eukhe` and the
    /// launcher `bin/eukhe`.
    fn installer_layout(dir: &Path) -> (PathBuf, PathBuf) {
        let root = dir.join("root");
        let payload = root.join("eukhe-0.10.69");
        std::fs::create_dir_all(&payload).unwrap();
        std::fs::write(payload.join("eukhe"), "binary").unwrap();
        let bin = dir.join("bin");
        std::fs::create_dir_all(&bin).unwrap();
        std::fs::write(bin.join("eukhe"), launcher_script(&payload)).unwrap();
        (root.canonicalize().unwrap(), bin.canonicalize().unwrap())
    }

    #[test]
    fn tool_owned_paths_are_named_by_their_tool() {
        let dir = tempfile::tempdir().unwrap();
        let workspace = dir.path().canonicalize().unwrap();
        std::fs::write(workspace.join("Cargo.toml"), "").unwrap();
        let none = places(vec![]);
        let kinds = [
            "/nix/store/abc-eukhe-0.10.70/bin/eukhe",
            "/Applications/Eukhe.app/Contents/MacOS/eukhe",
            "/home/u/.local/share/mise/installs/github-gildrb-eukhe/0.10.70/eukhe",
            "/usr/local/bin/eukhe",
        ]
        .map(|exe| classify(Path::new(exe), &none));
        assert_eq!(
            kinds,
            [
                InstallKind::Nix {
                    exe: PathBuf::from("/nix/store/abc-eukhe-0.10.70/bin/eukhe")
                },
                InstallKind::AppBundle {
                    app: PathBuf::from("/Applications/Eukhe.app")
                },
                InstallKind::Mise {
                    exe: PathBuf::from(
                        "/home/u/.local/share/mise/installs/github-gildrb-eukhe/0.10.70/eukhe"
                    )
                },
                InstallKind::Unknown {
                    exe: PathBuf::from("/usr/local/bin/eukhe")
                },
            ]
        );
        assert_eq!(
            classify(&workspace.join("target/release/eukhe"), &none),
            InstallKind::DevBuild { workspace }
        );
    }

    #[test]
    fn an_installer_payload_with_its_launcher_is_an_installer_install() {
        let dir = tempfile::tempdir().unwrap();
        let (root, bin) = installer_layout(dir.path());
        let exe = root.join("eukhe-0.10.69/eukhe");
        assert_eq!(
            classify(
                &exe,
                &places(vec![PathBuf::from("/nonexistent"), bin.clone()])
            ),
            InstallKind::Installer(Installer {
                payload: root.join("eukhe-0.10.69"),
                launcher: bin.join("eukhe"),
                launcher_root: root.clone(),
                root,
            })
        );
    }

    #[test]
    fn a_payload_without_a_launcher_that_execs_it_is_unknown() {
        let dir = tempfile::tempdir().unwrap();
        let (root, bin) = installer_layout(dir.path());
        std::fs::write(bin.join("eukhe"), launcher_script(Path::new("/elsewhere"))).unwrap();
        let exe = root.join("eukhe-0.10.69/eukhe");
        assert_eq!(
            classify(&exe, &places(vec![bin])),
            InstallKind::Unknown { exe }
        );
    }

    #[test]
    fn a_read_only_root_is_refused() {
        use std::os::unix::fs::PermissionsExt;
        let dir = tempfile::tempdir().unwrap();
        let (root, bin) = installer_layout(dir.path());
        std::fs::set_permissions(&root, std::fs::Permissions::from_mode(0o555)).unwrap();
        let kind = classify(
            &root.join("eukhe-0.10.69/eukhe"),
            &places(vec![bin.clone()]),
        );
        std::fs::set_permissions(&root, std::fs::Permissions::from_mode(0o755)).unwrap();
        assert_eq!(
            kind,
            InstallKind::ReadOnly {
                dir: root.clone(),
                install: Installer {
                    payload: root.join("eukhe-0.10.69"),
                    launcher: bin.join("eukhe"),
                    launcher_root: root.clone(),
                    root,
                },
            }
        );
    }
}
