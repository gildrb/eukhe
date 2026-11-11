//! The daemon socket a client connects to, resolved the way the `eukhe`
//! CLI does, for hosts that link neither the CLI nor the daemon.

use std::ffi::OsStr;
use std::path::{Path, PathBuf};

use eukhe_types::platform::daemon_socket::default_daemon_socket_path;
use eukhe_types::platform::dirs::expand_tilde;

/// `EUKHE_DAEMON_SOCKET`: the daemon socket path when no explicit one is
/// given.
pub const ENV_DAEMON_SOCKET: &str = "EUKHE_DAEMON_SOCKET";

/// The daemon socket path: `explicit` (the `--daemon-socket` flag) wins,
/// then a non-empty [`ENV_DAEMON_SOCKET`], then the per-user default
/// (`$TMPDIR/eukhe-<uid>/daemon.sock`). A leading `~`/`~/` expands against
/// the home dir. A relative path resolves against the current directory
/// (TS `normalizeSocketPath`), so the daemon binds, and the OS listener
/// census reports, the same absolute path every client and `shutdown`
/// resolve.
#[must_use]
pub fn resolve_daemon_socket_path(explicit: Option<&Path>) -> PathBuf {
    let socket_path = explicit
        .map(|path| expand_tilde_os(path.as_os_str()))
        .or_else(|| {
            std::env::var_os(ENV_DAEMON_SOCKET)
                .filter(|value| !value.is_empty())
                .as_deref()
                .map(expand_tilde_os)
        })
        .unwrap_or_else(default_daemon_socket_path);
    if socket_path.is_relative() {
        std::env::current_dir()
            .unwrap_or_else(|_| PathBuf::from("."))
            .join(socket_path)
    } else {
        socket_path
    }
}

/// [`expand_tilde`] over a raw path: a tilde-prefixed UTF-8 value expands
/// against the home dir; anything else passes through as the original
/// bytes (a lossy conversion would rewrite a non-UTF-8 socket path and
/// point the client at a socket nobody serves).
fn expand_tilde_os(value: &OsStr) -> PathBuf {
    match value.to_str() {
        Some(path) if path.starts_with('~') => expand_tilde(path),
        Some(_) | None => PathBuf::from(value),
    }
}

#[cfg(test)]
mod tests {
    use std::ffi::OsString;
    use std::os::unix::ffi::OsStrExt;
    use std::sync::Mutex;

    use super::*;

    /// Environment mutations are process-global: every test takes this lock
    /// and restores the previous values on exit.
    static ENV_LOCK: Mutex<()> = Mutex::new(());

    /// `body`'s result with the named variables set (`None` removes them),
    /// the previous values restored afterwards.
    fn with_env<T>(names: &[(&str, Option<&OsStr>)], body: impl FnOnce() -> T) -> T {
        let _guard = ENV_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let previous: Vec<(&str, Option<OsString>)> = names
            .iter()
            .map(|(name, _)| (*name, std::env::var_os(name)))
            .collect();
        for (name, value) in names {
            match value {
                Some(value) => std::env::set_var(name, value),
                None => std::env::remove_var(name),
            }
        }
        let result = body();
        for (name, value) in previous {
            match value {
                Some(value) => std::env::set_var(name, value),
                None => std::env::remove_var(name),
            }
        }
        result
    }

    /// Flag over env over default; `~` and relative paths on both the flag
    /// and the env; an empty env is no env. `TMPDIR` stays as it is: the
    /// other tests of this binary make their temp dirs under it.
    #[test]
    fn the_socket_is_the_flag_then_the_env_then_the_default() {
        let os = |value: &'static str| Some(OsStr::new(value));
        let cwd = std::env::current_dir().unwrap();
        let resolved = |env: Option<&OsStr>, explicit: Option<&str>| {
            with_env(
                &[(ENV_DAEMON_SOCKET, env), ("HOME", os("/home/tester"))],
                || resolve_daemon_socket_path(explicit.map(Path::new)),
            )
        };
        let uid = eukhe_types::platform::access::current_uid();
        let default = std::env::var_os("TMPDIR")
            .map_or_else(|| PathBuf::from("/tmp"), PathBuf::from)
            .join(format!("eukhe-{uid}/daemon.sock"));
        assert_eq!(
            [
                resolved(os("/env/d.sock"), None),
                resolved(os("/env/d.sock"), Some("/flag/d.sock")),
                resolved(None, Some("/flag/d.sock")),
                resolved(None, None),
                resolved(os(""), None),
                resolved(os("~/env.sock"), None),
                resolved(os("~"), None),
                resolved(os("~other/env.sock"), None),
                resolved(None, Some("~/flag.sock")),
                resolved(os("rel/env.sock"), None),
                resolved(None, Some("rel/flag.sock")),
                resolved(os("/env/d.sock"), Some("")),
            ],
            [
                PathBuf::from("/env/d.sock"),
                PathBuf::from("/flag/d.sock"),
                PathBuf::from("/flag/d.sock"),
                default.clone(),
                default,
                PathBuf::from("/home/tester/env.sock"),
                PathBuf::from("/home/tester"),
                cwd.join("~other/env.sock"),
                PathBuf::from("/home/tester/flag.sock"),
                cwd.join("rel/env.sock"),
                cwd.join("rel/flag.sock"),
                cwd.clone(),
            ]
        );
    }

    /// Without `HOME` a tilde path stays as written (relative, so under
    /// the cwd).
    #[test]
    fn a_tilde_without_home_stays() {
        let cwd = std::env::current_dir().unwrap();
        let resolved = with_env(&[(ENV_DAEMON_SOCKET, None), ("HOME", None)], || {
            resolve_daemon_socket_path(Some(Path::new("~/flag.sock")))
        });
        assert_eq!(resolved, cwd.join("~/flag.sock"));
    }

    /// A non-UTF-8 env value names its socket by its own bytes.
    #[test]
    fn a_non_utf8_env_socket_keeps_its_bytes() {
        let raw = OsStr::from_bytes(b"/env/\xff.sock");
        assert_eq!(
            with_env(&[(ENV_DAEMON_SOCKET, Some(raw))], || {
                resolve_daemon_socket_path(None)
            }),
            PathBuf::from(raw)
        );
    }
}
