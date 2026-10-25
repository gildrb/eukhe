//! Web dashboard (`eukhe dashboard`): a small loopback HTTP server that
//! ships a web app (built from `ui/` into `web/`, embedded in the binary)
//! and bridges each browser tab over a WebSocket to the eukhe daemon. The
//! tab chats with the root session the CLI and the Signal gateway use and
//! browses the chat memory's tree. A daemon-wire client like the TUI: it
//! never links the session engine.
//!
//! It binds 127.0.0.1 only. A tab pairs first: the first frame of its
//! socket must hold the pairing token (the fragment of the URL that
//! `eukhe dashboard` prints), and each later frame runs only while that
//! token is still the current one. A request must also name a loopback
//! host or a host the user allowed (a forwarder such as `tailscale
//! serve`), and a WebSocket upgrade must come from the app's own origin,
//! so other web pages in the user's browser cannot drive it.

mod access;
mod assets;
mod bridge;
mod command_policy;
mod http;
mod pairing;
mod protocol;

pub use pairing::{opener_page, pairing_token, PairingToken, Rotation};

use std::net::{Ipv4Addr, SocketAddr};
use std::path::PathBuf;

use anyhow::Context;
use serde_json::{Map, Value};

use eukhe_tui::saved_sessions::DaemonLauncher;

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
    /// Host names besides loopback the dashboard answers to (the name a
    /// forwarder such as `tailscale serve` exposes it under), compared
    /// without the port and case-insensitively.
    pub allowed_hosts: Vec<String>,
    /// The file of the pairing token (in the agent dir, mode 0600). Every
    /// check reads it again, so a rotation takes effect at once.
    pub token_path: PathBuf,
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
