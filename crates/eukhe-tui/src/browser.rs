//! Browser launch for clicked hyperlinks (TS `tui.ts` `openHyperlink`'s
//! platform table — darwin `open`, otherwise `xdg-open`).
//!
//! Terminals gate their native link handling while mouse reporting is
//! active (Ghostty only refreshes link hover when reporting is off or
//! shift is held), so clicks the TUI consumes must open their OSC 8
//! targets themselves. eukhe-tui stays eukhe-types-only: this is the TUI
//! package's own opener (the composition root's login flows carry theirs
//! in eukhe-core), exactly like TS where tui.ts and the login dialog each
//! build the same command table.
//!
//! The opener always resolves to an absolute path: `Command::new` would
//! search the inherited `PATH` for a bare name, where a doctored
//! environment could redirect a click into an arbitrary program, so the
//! platform tables pin the system tool locations instead (macOS's `open`
//! is fixed, the xdg-utils slots cover the mainstream Linux layouts and
//! NixOS's root-managed profiles, and a tool that is not there is a failed
//! launch — never a `PATH` hunt).

use std::path::PathBuf;
use std::process::{Command, Stdio};

/// The xdg-utils locations a desktop Linux carries `xdg-open` in (the
/// fixed tool slots — searched in order, the first that exists wins).
/// NixOS has no FHS copy (its `/usr/bin` is at most an envfs mount that
/// resolves through `PATH`), so its system and default profiles follow.
#[cfg(not(target_os = "macos"))]
const XDG_OPEN_SLOTS: [&str; 5] = [
    "/usr/bin/xdg-open",
    "/usr/local/bin/xdg-open",
    "/bin/xdg-open",
    "/run/current-system/sw/bin/xdg-open",
    "/nix/var/nix/profiles/default/bin/xdg-open",
];

/// The absolute opener path and its argument list for one URL, or `None`
/// when the platform's tool is not installed (the one arm per compiled
/// target).
fn opener(url: &str) -> Option<(PathBuf, Vec<String>)> {
    #[cfg(target_os = "macos")]
    {
        Some((PathBuf::from("/usr/bin/open"), vec![url.to_string()]))
    }
    #[cfg(not(target_os = "macos"))]
    {
        // NixOS's per-user profile (where `users.users.<name>.packages`
        // and home-manager install) is root-managed too; a `USER` that is
        // not a plain name could walk out of it, so it never forms a slot.
        let per_user_slot = std::env::var("USER")
            .ok()
            .filter(|user| !user.is_empty() && !user.contains('/') && user != "." && user != "..")
            .map(|user| PathBuf::from(format!("/etc/profiles/per-user/{user}/bin/xdg-open")));
        let path = XDG_OPEN_SLOTS
            .into_iter()
            .map(PathBuf::from)
            .chain(per_user_slot)
            .find(|path| path.is_file())?;
        Some((path, vec![url.to_string()]))
    }
}

/// Open `url` in the user's browser. Fire-and-forget like TS
/// `openHyperlink` (`execFile` with a swallowed callback): the link
/// stays visible in the transcript, so a failed launch (no desktop
/// session, no opener) never fails the click. The child is reaped on a
/// parked thread — TS's `execFile` waits for exit, and an unwaited spawn
/// would leak one zombie per click in the long-running TUI.
pub(crate) fn open_in_browser(url: &str) {
    let Some((program, args)) = opener(url) else {
        return;
    };
    let Ok(mut child) = Command::new(program)
        .args(&args)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
    else {
        return;
    };
    std::thread::spawn(move || {
        let _ = child.wait();
    });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_opener_resolves_an_absolute_path_and_targets_the_url() {
        let Some((program, args)) = opener("https://example.com/docs") else {
            // Only the xdg-utils slots can come up empty (macOS's `open`
            // is a fixed path): a Linux host without xdg-utils installed
            // has no opener to resolve.
            #[cfg(not(target_os = "macos"))]
            {
                eprintln!(
                    "no xdg-open in {XDG_OPEN_SLOTS:?} or the NixOS per-user profile; skipping the opener resolution check"
                );
                return;
            }
            #[cfg(target_os = "macos")]
            panic!("the platform opener");
        };
        assert!(
            program.is_absolute(),
            "the opener never resolves through PATH: {program:?}"
        );
        assert!(args.iter().any(|arg| arg.contains("example.com")));
    }
}
