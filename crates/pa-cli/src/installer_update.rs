//! The `update` body. Upstream's update runs the official installer, which
//! would replace eukhe with upstream Prime Agent; eukhe updates through its
//! package manager instead, so the command names that route. The TUI's
//! `/update` reaches the same answer through the installer core
//! (`client_update.rs`).

use pa_core::update::installer;
use pa_core::update::version::UpdateChannel;

/// One parsed `prime-agent update` invocation.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct UpdateOptions {
    /// `--check`: print the latest release of the update channel vs the
    /// running binary's version, without installing.
    pub check: bool,
    /// `--nightly` / `--stable`: switch the update channel (persisted once
    /// the update completes).
    pub channel: Option<UpdateChannel>,
}

/// The saved `updateChannel` setting (`/nightly on|off`, `--nightly`,
/// `--stable`).
fn saved_channel() -> Option<UpdateChannel> {
    let cwd = std::env::current_dir().ok()?;
    let saved = pa_core::settings::SettingsManager::create(&cwd, crate::config::get_agent_dir())
        .get_update_channel()?;
    Some(match saved {
        pa_core::settings::UpdateChannel::Stable => UpdateChannel::Stable,
        pa_core::settings::UpdateChannel::Nightly => UpdateChannel::Nightly,
    })
}

/// The installer's channel name for an update channel.
fn installer_channel(channel: UpdateChannel) -> &'static str {
    match channel {
        UpdateChannel::Stable => "stable",
        UpdateChannel::Nightly => "beta",
    }
}

/// The update channel: the flag, else the saved `updateChannel` setting,
/// else the install marker's channel, else the one the running version
/// implies (a `-beta*` build is a nightly install).
fn resolve_channel(
    flag: Option<UpdateChannel>,
    saved: Option<UpdateChannel>,
    marker: Option<&str>,
    running: &str,
) -> UpdateChannel {
    flag.or(saved)
        .or(marker.map(|marker| match marker {
            "stable" => UpdateChannel::Stable,
            _ => UpdateChannel::Nightly,
        }))
        .unwrap_or_else(|| pa_core::update::version::resolve_update_channel(running, None))
}

/// The channel `update`, `update --check`, and `/update` follow.
fn update_channel(flag: Option<UpdateChannel>) -> UpdateChannel {
    resolve_channel(
        flag,
        saved_channel(),
        installer::installed_channel(&installer::install_prefix()),
        crate::config::version(),
    )
}

/// The installer's channel name for [`update_channel`].
#[must_use]
pub fn requested_installer_channel(flag: Option<UpdateChannel>) -> &'static str {
    installer_channel(update_channel(flag))
}

/// Run the update command. eukhe never runs the upstream installer (it
/// would replace this build with upstream Prime Agent): `update` names the
/// package-manager route and fails; `--check` reports the running version
/// and the same route. Returns the process exit code.
pub fn run(options: &UpdateOptions) -> i32 {
    if options.check {
        println!("Running:  {}", crate::config::version());
        println!("{}", installer::EXTERNAL_UPDATES);
        return 0;
    }
    eprintln!("Error: {}", installer::EXTERNAL_UPDATES);
    1
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_channel_resolves_flag_then_saved_then_marker_then_version() {
        use UpdateChannel::{Nightly, Stable};
        assert_eq!(
            resolve_channel(Some(Stable), Some(Nightly), Some("beta"), "1.2.3-beta.1"),
            Stable
        );
        assert_eq!(
            resolve_channel(None, Some(Nightly), Some("stable"), "1.2.3"),
            Nightly
        );
        assert_eq!(
            resolve_channel(None, None, Some("stable"), "1.2.3-beta.1"),
            Stable
        );
        assert_eq!(resolve_channel(None, None, Some("beta"), "1.2.3"), Nightly);
        assert_eq!(resolve_channel(None, None, None, "1.2.3-beta.1"), Nightly);
        assert_eq!(resolve_channel(None, None, None, "1.2.3"), Stable);
    }

    #[test]
    fn the_nightly_channel_runs_the_installer_on_beta() {
        assert_eq!(installer_channel(UpdateChannel::Nightly), "beta");
        assert_eq!(installer_channel(UpdateChannel::Stable), "stable");
    }
}
