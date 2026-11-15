//! `/restart`: a client starts again on the build its install runs now and
//! reopens its session. The composition root names that build
//! ([`Restarter::prepare`], which first applies an update a launch check
//! staged); [`plan`] decides what happens to the daemon the client is
//! attached to. The daemon moves only by an idle shutdown, which the
//! supervisor refuses while any session holds work, so a restart never
//! stops a run: a busy daemon keeps running, and the client starts again
//! alone when the new build speaks the daemon's protocol, or stays.

use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;

use eukhe_types::daemon::{
    DaemonCommand, DAEMON_PROTOCOL_VERSION, DAEMON_SCHEMA_ID, IDLE_SHUTDOWN_CAPABILITY,
};
use serde_json::Value;

use crate::daemon_build::{replacement_verdict, Build, Caller, Relation, Replacement};
use crate::daemon_client::DaemonClient;
use crate::launcher::socket_released;

/// What a build tells a daemon about itself: the build a daemon's hello
/// reports and the wire it speaks.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Identity {
    /// The compiled version (the hello `appVersion`).
    pub build_version: String,
    /// The build id (the hello `runtime.buildId`).
    pub build_id: String,
    /// The wire protocol version (the hello `protocol.version`).
    pub protocol_version: u64,
    /// The wire schema (the hello `schemaId`).
    pub schema_id: String,
}

impl Identity {
    /// This build's identity.
    #[must_use]
    pub fn this() -> Self {
        Self {
            build_version: eukhe_build_info::VERSION.to_string(),
            build_id: eukhe_build_info::DAEMON_BUILD_ID.to_string(),
            protocol_version: DAEMON_PROTOCOL_VERSION,
            schema_id: DAEMON_SCHEMA_ID.to_string(),
        }
    }

    fn build(&self) -> Build<'_> {
        Build {
            version: &self.build_version,
            id: &self.build_id,
        }
    }

    /// Whether a daemon that greeted with `hello` speaks this build's wire.
    fn speaks(&self, hello: &Value) -> bool {
        hello
            .get("protocol")
            .and_then(|protocol| protocol.get("version"))
            .and_then(Value::as_u64)
            == Some(self.protocol_version)
            && hello.get("schemaId").and_then(Value::as_str) == Some(self.schema_id.as_str())
    }
}

/// The build a restart starts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Target {
    /// The executable the restart runs.
    pub exe: PathBuf,
    /// The product version it reports.
    pub version: String,
    /// Its identity; `None` for a build that reports none (a release
    /// before `/restart`).
    pub identity: Option<Identity>,
}

/// The composition root's side of `/restart`, for every client surface
/// with slash commands.
///
/// An implementation owns the install: it knows the update a launch check
/// staged and applies it. `staged` never blocks; `prepare` may run the
/// target build once to read its identity.
pub trait Restarter: Send + Sync {
    /// The version of the update staged for `/restart`, once there is one.
    fn staged(&self) -> tokio::sync::watch::Receiver<Option<String>>;

    /// The staged update's notice, the first time it is asked for; `None`
    /// before an update is staged and after the notice was taken once.
    fn take_notice(&self) -> Option<String>;

    /// Applies the staged update, if any, and names the build a restart
    /// starts.
    ///
    /// # Errors
    ///
    /// Why this client cannot restart, said to the user as it is.
    fn prepare(&self) -> Result<Target, String>;

    /// How long a daemon that agreed to stop may take to release its socket.
    fn release_wait(&self) -> Duration;
}

/// A shared [`Restarter`].
pub type SharedRestarter = Arc<dyn Restarter>;

/// The notice a client shows once an update is staged.
pub const STAGED_NOTICE: &str = "/restart to apply the downloaded update";

/// What a restart does.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Plan {
    /// Start the target now: the daemon is its build, one it attaches to,
    /// or it stopped.
    Start,
    /// Start the target now; the daemon has work and keeps running its
    /// build until an interactive start finds it idle.
    StartBesideBusyDaemon { daemon_version: String },
    /// Stay: the daemon has work and the target cannot attach to it.
    WaitForIdle { daemon_version: String },
    /// Stay: the daemon is a build the target never replaces and cannot
    /// attach to.
    Blocked { daemon_version: String },
}

/// What an idle shutdown left.
enum IdleStop {
    Stopped,
    Busy,
}

/// What a restart onto `target` does with the daemon `client` is attached
/// to. A daemon the target would replace is asked to stop if idle (the
/// client's connection ends when it agrees); every other daemon is kept.
pub async fn plan(client: &DaemonClient, target: &Target, release_wait: Duration) -> Plan {
    let daemon = client.daemon_build();
    let daemon_version = daemon.version.to_string();
    let speaks = target
        .identity
        .as_ref()
        .is_some_and(|identity| identity.speaks(client.hello()));
    let verdict = target
        .identity
        .as_ref()
        .map_or(Replacement::Replace, |identity| {
            replacement_verdict(identity.build(), daemon, Caller::Interactive)
        });
    match verdict {
        Replacement::Keep(Relation::Same) => Plan::Start,
        Replacement::Keep(Relation::Older | Relation::Newer | Relation::Other) => {
            if speaks {
                Plan::Start
            } else {
                Plan::Blocked { daemon_version }
            }
        }
        Replacement::Replace => match stop_if_idle(client, release_wait).await {
            IdleStop::Stopped => Plan::Start,
            IdleStop::Busy if speaks => Plan::StartBesideBusyDaemon { daemon_version },
            IdleStop::Busy => Plan::WaitForIdle { daemon_version },
        },
    }
}

/// Ask the daemon to stop only when idle; the supervisor decides it
/// atomically with the stop. A daemon without the idle shutdown would stop
/// unconditionally: it is not asked and counts as busy. An agreed stop
/// waits up to `release_wait` for the socket to free.
async fn stop_if_idle(client: &DaemonClient, release_wait: Duration) -> IdleStop {
    if !client.supports_server_capability(IDLE_SHUTDOWN_CAPABILITY) {
        return IdleStop::Busy;
    }
    let answer = client
        .request(DaemonCommand::Shutdown {
            id: None,
            force: None,
            if_idle: Some(true),
            rest: serde_json::Map::default(),
        })
        .await;
    match answer {
        Ok(response) if response.success => {
            // A socket still held after the wait is the next start's to
            // free (its takeover).
            socket_released(client.socket_path(), release_wait).await;
            IdleStop::Stopped
        }
        Ok(_) => IdleStop::Busy,
        // No answer: the daemon may stop before it answers, so the socket
        // decides.
        Err(_) => {
            if socket_released(client.socket_path(), release_wait).await {
                IdleStop::Stopped
            } else {
                IdleStop::Busy
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn a_daemon_speaks_a_build_only_with_its_protocol_and_schema() {
        let identity = Identity::this();
        let hello = |version: u64, schema: &str| json!({"protocol": {"version": version}, "schemaId": schema});
        assert_eq!(
            [
                identity.speaks(&hello(DAEMON_PROTOCOL_VERSION, DAEMON_SCHEMA_ID)),
                identity.speaks(&hello(DAEMON_PROTOCOL_VERSION, "protocol-7-schema-0-x")),
                identity.speaks(&hello(DAEMON_PROTOCOL_VERSION + 1, DAEMON_SCHEMA_ID)),
                identity.speaks(&json!({})),
            ],
            [true, false, false, false]
        );
    }
}
