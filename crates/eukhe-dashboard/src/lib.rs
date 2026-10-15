//! Web dashboard (`eukhe dashboard`): a small loopback HTTP server that
//! ships a build-free web app (plain HTML/CSS/JS embedded in the binary)
//! and bridges each browser tab over a WebSocket to the eukhe daemon. The
//! tab chats with the root session the CLI and the Signal gateway use and
//! browses the chat memory's tree. A daemon-wire client like the TUI: it
//! never links the session engine.
//!
//! It binds 127.0.0.1 only and has no authentication of its own: whoever
//! reaches the loopback port is the owner. Exposure beyond the machine is
//! the user's own forwarder's business.

mod assets;
mod bridge;
mod http;
mod protocol;
mod sessions;

use std::future::Future;
use std::net::{Ipv4Addr, SocketAddr};
use std::path::PathBuf;

use anyhow::Context;
use serde_json::{Map, Value};

/// Dashboard configuration, built by the composition root
/// (`eukhe dashboard`).
#[derive(Debug, Clone, PartialEq)]
pub struct DashboardConfig {
    /// The daemon supervisor socket.
    pub socket_path: PathBuf,
    /// The sessions directory the CLI uses: the dashboard lists and opens
    /// sessions there.
    pub session_dir: PathBuf,
    /// The working directory of sessions the dashboard creates (and of the
    /// first session when none exists).
    pub new_session_cwd: PathBuf,
    /// Fields every session create config carries besides `sessionDir` and
    /// `cwd` (the CLI's verification seams; empty in the product).
    pub create_config: Map<String, Value>,
}

/// Starts the eukhe daemon on the dashboard's socket when no daemon of
/// this build listens there. The composition root implements it with the
/// CLI's launcher (this crate does not link the CLI). `ensure` returns
/// once a daemon accepts connections on the socket and fails when none
/// can start. The dashboard calls it for every browser connection, so it
/// must return quickly when a daemon already runs.
pub trait DaemonLauncher: Send + Sync + 'static {
    fn ensure(&self) -> impl Future<Output = anyhow::Result<()>> + Send;
}

/// The port the dashboard listens on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Port {
    /// A free port the system picks.
    Free,
    /// Exactly this port; binding fails when it is taken.
    Fixed(u16),
}

/// Bind the dashboard's listener on 127.0.0.1 (never another interface).
///
/// # Errors
///
/// The port is taken or the socket cannot be bound.
#[tracing::instrument]
pub async fn bind(port: Port) -> anyhow::Result<tokio::net::TcpListener> {
    let port_number = match port {
        Port::Free => 0,
        Port::Fixed(port) => port,
    };
    let address = SocketAddr::from((Ipv4Addr::LOCALHOST, port_number));
    tokio::net::TcpListener::bind(address)
        .await
        .with_context(|| format!("listen on {address}"))
}

/// Serve the dashboard on `listener` until the task is dropped: the app's
/// files, and one daemon bridge per browser WebSocket.
///
/// # Errors
///
/// Accepting connections fails.
#[tracing::instrument(skip_all)]
pub async fn serve(
    listener: tokio::net::TcpListener,
    config: DashboardConfig,
    launcher: impl DaemonLauncher,
) -> anyhow::Result<()> {
    http::serve(
        listener,
        std::sync::Arc::new(config),
        std::sync::Arc::new(launcher),
    )
    .await
}
