//! Home-directory resolution shared by every crate that expands `~`.
//!
//! The TS product resolves the home directory with Node's `os.homedir()`
//! (or `process.env.HOME || homedir()` in the package manager, which keeps
//! the same first step): `HOME` when set. When nothing resolves it
//! throws - this port returns `None` and each caller owns its fallback
//! (an explicit error in the daemon, a documented degraded value elsewhere),
//! so the decision stays visible at the point of use instead of a shared
//! silent default.

use std::path::PathBuf;

/// The user's home directory, Node `os.homedir()` semantics.
/// `HOME` when set and non-empty (matching the TS
/// `process.env.HOME || homedir()` order). `None` means no home resolved;
/// the per-call-site fallback replaces the TS `os.homedir()` throw.
#[must_use]
pub fn home_dir() -> Option<PathBuf> {
    std::env::var_os("HOME")
        .filter(|home| !home.is_empty())
        .map(PathBuf::from)
}

/// `EUKHE_CODING_AGENT_DIR`: the agent state directory override (a
/// wire-internal identifier kept byte-compatible with the TS product).
pub const ENV_AGENT_DIR: &str = "EUKHE_CODING_AGENT_DIR";

/// The user's agent state directory under the home directory. eukhe keeps
/// its state apart from an installed Eukhe (`.eukhe`): its own
/// settings, sessions, daemon, kernel venv, and chat memory. Project-local
/// configuration stays `<project>/.eukhe`.
pub const AGENT_DIR_NAME: &str = ".eukhe";

/// The agent state directory (TS `getAgentDir`): the env override with a
/// leading `~`/`~/` expanded against [`home_dir`], else `<home>/.eukhe`.
/// `None` when no override is set and the home directory does not resolve
/// (each caller owns its fallback).
#[must_use]
pub fn agent_dir() -> Option<PathBuf> {
    if let Some(dir) = std::env::var_os(ENV_AGENT_DIR).filter(|dir| !dir.is_empty()) {
        return Some(expand_tilde(&dir.to_string_lossy()));
    }
    home_dir().map(|home| home.join(AGENT_DIR_NAME))
}

/// Expand a leading `~`/`~/` against [`home_dir`]; other values pass
/// through (TS `expandTildePath`: `~foo` is not an expansion).
fn expand_tilde(path: &str) -> PathBuf {
    if let Some(rest) = path.strip_prefix("~/") {
        return home_dir().map_or_else(|| PathBuf::from(path), |home| home.join(rest));
    }
    if path == "~" {
        return home_dir().unwrap_or_else(|| PathBuf::from(path));
    }
    PathBuf::from(path)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;

    /// Environment mutations are process-global: every test takes this lock
    /// and restores the previous values on exit.
    static ENV_LOCK: Mutex<()> = Mutex::new(());

    /// Run `body` with the named variables set to the given values (`None`
    /// removes them), restoring the previous state afterwards.
    fn with_env(names: &[(&str, Option<&str>)], body: impl FnOnce()) {
        let _guard = ENV_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let previous: Vec<(&str, Option<std::ffi::OsString>)> = names
            .iter()
            .map(|(name, _)| (*name, std::env::var_os(name)))
            .collect();
        for (name, value) in names {
            match value {
                Some(value) => std::env::set_var(name, value),
                None => std::env::remove_var(name),
            }
        }
        body();
        for (name, value) in previous {
            match value {
                Some(value) => std::env::set_var(name, value),
                None => std::env::remove_var(name),
            }
        }
    }

    #[test]
    fn agent_dir_env_override_expands_tilde() {
        with_env(
            &[
                ("HOME", Some("/home/tester")),
                ("EUKHE_CODING_AGENT_DIR", Some("~/state")),
            ],
            || {
                assert_eq!(agent_dir(), Some(PathBuf::from("/home/tester/state")));
            },
        );
    }

    #[test]
    fn agent_dir_env_override_passthrough() {
        with_env(
            &[
                ("HOME", None),
                ("EUKHE_CODING_AGENT_DIR", Some("/opt/state")),
            ],
            || {
                assert_eq!(agent_dir(), Some(PathBuf::from("/opt/state")));
            },
        );
    }

    #[test]
    fn agent_dir_default_under_home() {
        with_env(
            &[
                ("HOME", Some("/home/tester")),
                ("EUKHE_CODING_AGENT_DIR", None),
            ],
            || {
                assert_eq!(agent_dir(), Some(PathBuf::from("/home/tester/.eukhe")));
            },
        );
    }

    #[test]
    fn agent_dir_without_home_is_none() {
        with_env(&[("HOME", None), ("EUKHE_CODING_AGENT_DIR", None)], || {
            assert_eq!(agent_dir(), None);
        });
    }

    #[test]
    fn home_dir_follows_home() {
        with_env(&[("HOME", Some("/home/tester"))], || {
            assert_eq!(home_dir(), Some(PathBuf::from("/home/tester")));
        });
    }

    #[test]
    fn home_dir_unset_is_none() {
        with_env(&[("HOME", None)], || {
            assert_eq!(home_dir(), None);
        });
    }

    #[test]
    fn home_dir_empty_is_none() {
        with_env(&[("HOME", Some(""))], || {
            assert_eq!(home_dir(), None);
        });
    }
}
