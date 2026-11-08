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

use std::path::PathBuf;
use std::sync::Arc;

use eukhe_client::saved_sessions::DaemonLauncher;
use eukhe_tui::client_settings::{ClientSettings, ModelRoleSource};
use eukhe_types::model_roles::ModelRole;
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
    pub signal: SignalConfig,
    /// `gateway.rootHeartbeat`: the heartbeat schedule of the root session
    /// (the `/heartbeat` schedule forms, such as `every 30 minutes`).
    /// Set, the phone's messages go to the persistent session named
    /// `root` (made when missing) and the gateway's start creates or
    /// replaces its heartbeat. `None` routes to the newest session.
    pub root_heartbeat: Option<String>,
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

/// The model Signal messages run on, as the settings hold it now: the
/// gateway role's model (`gateway.signal.model`, else `modelRoles.all`;
/// a phone `/model N` or the `/model` hub changes it while the gateway
/// runs). `None` keeps the session's model.
///
/// # Errors
///
/// The setting is not `provider/model-id` (a provider name has no `/`, a
/// model id may).
pub fn signal_model(settings: &dyn ClientSettings) -> anyhow::Result<Option<SignalModel>> {
    let Some(role) = settings.model_role(ModelRole::Gateway, "") else {
        return Ok(None);
    };
    let Some(selector) = role.selector else {
        return Ok(None);
    };
    match selector.split_once('/') {
        Some((provider, model_id)) if !provider.is_empty() && !model_id.is_empty() => {
            Ok(Some(SignalModel {
                provider: provider.to_owned(),
                model_id: model_id.to_owned(),
            }))
        }
        Some(_) | None => {
            let setting = match role.source {
                ModelRoleSource::AllRoles => "modelRoles.all",
                ModelRoleSource::Global | ModelRoleSource::Project | ModelRoleSource::Unset => {
                    "gateway.signal.model"
                }
            };
            anyhow::bail!(
                "{setting} is {selector:?}; set it to provider/model-id (see eukhe model list) or remove it"
            )
        }
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
/// replies back. `settings` is the settings store `/model` reads (the
/// all-roles model). On a signal it stops the typing indicator and
/// detaches.
///
/// # Errors
///
/// Returns `Err` when `signal-cli` cannot start, when the first daemon
/// connection fails, or when the signal handlers cannot install. Later
/// daemon failures reconnect with backoff instead.
#[tracing::instrument(skip_all, fields(account = %config.signal.account))]
pub async fn run(
    config: GatewayConfig,
    launcher: impl DaemonLauncher,
    settings: Arc<dyn ClientSettings>,
) -> anyhow::Result<()> {
    gateway::Gateway::start(config, launcher, settings)
        .await?
        .serve()
        .await
}
