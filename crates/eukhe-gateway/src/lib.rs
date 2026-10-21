//! Signal gateway: one `signal-cli` child carries chat messages between a
//! phone and the eukhe daemon. The phone shares the CLI's session.

mod answer;
mod commands;
mod gateway;
mod link;
mod sessions;
mod setup;
mod signal;
mod style;
#[cfg(test)]
mod testing;

use std::path::PathBuf;

use eukhe_tui::saved_sessions::DaemonLauncher;
pub use setup::{link_device, linked_accounts, restart_service, service_installed};

/// Gateway configuration, built by the composition root (`eukhe gateway`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GatewayConfig {
    /// The daemon supervisor socket.
    pub socket_path: PathBuf,
    /// The sessions directory the CLI uses: the gateway lists and opens
    /// sessions there.
    pub session_dir: PathBuf,
    /// The working directory of sessions that `/new` creates (and of the
    /// first session when none exists).
    pub new_session_cwd: PathBuf,
    /// The model Signal messages run on; `None` keeps the session's model.
    pub model: Option<SignalModel>,
    pub signal: SignalConfig,
}

/// A model of the catalog, as `set_model` names it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignalModel {
    pub provider: String,
    pub model_id: String,
}

impl std::fmt::Display for SignalModel {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{}/{}", self.provider, self.model_id)
    }
}

/// The `signal-cli` account the gateway runs as.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignalConfig {
    /// The `signal-cli` executable.
    pub cli_path: PathBuf,
    /// The account (`+<country><number>`, or the ACI of a numberless account).
    pub account: String,
    /// Senders (numbers or ACIs) that may drive the session. "Note to Self"
    /// messages of `account` are always accepted.
    pub allow: Vec<String>,
}

/// Run the gateway until SIGINT or SIGTERM: relay the allowed Signal
/// senders' messages into the daemon session the CLI uses, and the agent's
/// replies back. On a signal it stops the typing indicator and detaches.
///
/// # Errors
///
/// Returns `Err` when `signal-cli` cannot start, when the first daemon
/// connection fails, or when the signal handlers cannot install. Later
/// daemon failures reconnect with backoff instead.
#[tracing::instrument(skip_all, fields(account = %config.signal.account))]
pub async fn run(config: GatewayConfig, launcher: impl DaemonLauncher) -> anyhow::Result<()> {
    gateway::Gateway::start(config, launcher)
        .await?
        .serve()
        .await
}
