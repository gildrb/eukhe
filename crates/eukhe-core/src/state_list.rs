//! The state list (the state table of the confinement design,
//! `spec/security/SPEC.md` §3 "state list"): every part of Eukhe's state,
//! as paths of this install. Programs an agent runs are kept from each
//! part; the path policy builds its protected and secret classes from it
//! ([`crate::durable::path_policy`]).
//!
//! Parts of §4 that are no path of the install are not listed: check
//! definitions (contract paths of a run), Eukhe's processes, and aliases of
//! a part (hard links, bind mounts), which are classed by device and inode
//! when a profile is built.

use std::ffi::OsString;
use std::path::{Path, PathBuf};

use eukhe_types::platform::dirs::{expand_tilde, work_root_of, RUN_DIR_NAME};

use crate::auth::AUTH_FILE_NAME;

/// The dashboard's pairing token file in the agent dir.
pub const DASHBOARD_TOKEN_FILE: &str = "dashboard-token";

/// The environment variables that move the AWS shared files (Bedrock's
/// credentials) away from `~/.aws`.
const AWS_FILE_ENV: [&str; 2] = ["AWS_SHARED_CREDENTIALS_FILE", "AWS_CONFIG_FILE"];

/// What one [`StatePart`] holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StateKind {
    /// The agent dir (`~/.eukhe`, or `EUKHE_CODING_AGENT_DIR`): the store,
    /// the record and its anchors, the spend ledgers, the settings, the cron
    /// jobs, the agent profiles.
    AgentDir,
    /// The daemon's and workers' sockets and their locks (`<agent
    /// dir>/run`).
    RunDir,
    /// A credentials file or store Eukhe reads: `auth.json`, the dashboard
    /// token, the Prime CLI config, the AWS shared files (Bedrock).
    Credentials,
    /// The copies and snapshots of agents' work (`<agent dir>-work`): child
    /// workspaces, check copies, kernel snapshots. A run's own copy is its
    /// scope; every other copy is state.
    WorkRoot,
    /// The directory of Eukhe's running executable.
    Executables,
    /// A directory whose entries run later with the user's full access:
    /// launchd agents (macOS), systemd user units and XDG autostart entries
    /// (Linux). The user's crontab is reached only through `crontab`, a
    /// setuid program, never as a path of the user.
    AutoStart,
}

/// One part of Eukhe's state: what it holds and where.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StatePart {
    pub kind: StateKind,
    /// The part's path; a directory part covers everything under it.
    pub path: PathBuf,
}

/// Where this install keeps what [`state_list`] names.
pub struct Install<'a> {
    pub agent_dir: &'a Path,
    /// The home directory; `None` when it does not resolve (the parts
    /// under it are then not listed).
    pub home: Option<&'a Path>,
    /// The running executable's path; `None` when it does not resolve.
    pub executable: Option<&'a Path>,
    /// The base of a relative path in an environment variable.
    pub cwd: &'a Path,
    /// The value of an environment variable; `None` when unset.
    pub env: &'a dyn Fn(&str) -> Option<OsString>,
}

impl Install<'_> {
    /// The value of the environment variable `name` as a path (`~`
    /// expanded, a relative path against [`Self::cwd`]); `None` when unset
    /// or empty.
    fn env_path(&self, name: &str) -> Option<PathBuf> {
        let value = (self.env)(name).filter(|value| !value.is_empty())?;
        Some(self.cwd.join(expand_tilde(&value.to_string_lossy())))
    }
}

/// Every part of Eukhe's state for `install`.
#[must_use]
pub fn state_list(install: &Install<'_>) -> Vec<StatePart> {
    let part = |kind, path| StatePart { kind, path };
    let agent_dir = install.agent_dir;
    let mut parts = vec![
        part(StateKind::AgentDir, agent_dir.to_path_buf()),
        part(StateKind::RunDir, agent_dir.join(RUN_DIR_NAME)),
        part(StateKind::Credentials, agent_dir.join(AUTH_FILE_NAME)),
        part(StateKind::Credentials, agent_dir.join(DASHBOARD_TOKEN_FILE)),
        part(
            StateKind::Credentials,
            crate::auth::default_prime_cli_config_path(),
        ),
    ];
    if let Some(home) = install.home {
        parts.push(part(StateKind::Credentials, home.join(".aws")));
    }
    parts.extend(
        AWS_FILE_ENV
            .iter()
            .filter_map(|name| install.env_path(name))
            .map(|path| part(StateKind::Credentials, path)),
    );
    if let Some(work_root) = work_root_of(agent_dir) {
        parts.push(part(StateKind::WorkRoot, work_root));
    }
    if let Some(dir) = install.executable.and_then(Path::parent) {
        parts.push(part(StateKind::Executables, dir.to_path_buf()));
    }
    parts.extend(
        auto_start_dirs(install)
            .into_iter()
            .map(|path| part(StateKind::AutoStart, path)),
    );
    parts
}

/// The auto-start directories of this platform.
#[cfg(target_os = "macos")]
fn auto_start_dirs(install: &Install<'_>) -> Vec<PathBuf> {
    install
        .home
        .map(|home| home.join("Library/LaunchAgents"))
        .into_iter()
        .collect()
}

/// The auto-start directories of this platform: under `XDG_CONFIG_HOME`,
/// else `~/.config`.
#[cfg(not(target_os = "macos"))]
fn auto_start_dirs(install: &Install<'_>) -> Vec<PathBuf> {
    let config = install
        .env_path("XDG_CONFIG_HOME")
        .or_else(|| install.home.map(|home| home.join(".config")));
    config
        .map(|config| vec![config.join("systemd/user"), config.join("autostart")])
        .unwrap_or_default()
}

/// [`state_list`] of the running install with agent dir `agent_dir`: the
/// home directory, executable, working directory and environment of this
/// process.
#[must_use]
pub fn current_state_list(agent_dir: &Path) -> Vec<StatePart> {
    let home = eukhe_types::platform::home_dir();
    let executable = std::env::current_exe().ok();
    let cwd = std::env::current_dir().unwrap_or_default();
    state_list(&Install {
        agent_dir,
        home: home.as_deref(),
        executable: executable.as_deref(),
        cwd: &cwd,
        env: &|name| std::env::var_os(name),
    })
}

#[cfg(test)]
mod tests;
