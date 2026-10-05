//! Browser launch for OAuth login URLs: the platform opener (the TS
//! login dialog's command table — macOS `open`, Linux `xdg-open`).

use std::process::{Command, Stdio};

/// The opener program for one URL.
#[cfg(target_os = "macos")]
const OPENER: &str = "open";

/// The opener program for one URL.
#[cfg(target_os = "linux")]
const OPENER: &str = "xdg-open";

/// Open `url` in the user's browser. Fire-and-forget like the TS dialog
/// (`execFileHidden` with a swallowed callback): the caller also shows the
/// URL itself, so a failed launch (no desktop session, no opener) never
/// fails the login. The spawn result is deliberately not an error surface.
pub fn open_in_browser(url: &str) {
    let _ = Command::new(OPENER)
        .arg(url)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn();
}
