//! Daemon-wire client for Eukhe frontends.
//!
//! A frontend (the terminal UI, the web dashboard, the Signal gateway, an
//! external host such as a native app) talks to the Eukhe daemon over the
//! versioned `eukhe.daemon` wire protocol and never links the session
//! engine. This crate is that client:
//!
//! - [`daemon_client`]: the supervisor connection ([`DaemonClient`]), its
//!   `daemon_hello` handshake, requests matched by envelope id, and the
//!   event stream ([`DaemonClientEvent`]).
//! - [`direct_transport`]: the direct link to a session worker's socket,
//!   upgraded from the supervisor connection.
//! - [`daemon_build`]: the order of eukhe builds and the replacement
//!   verdict on the daemon found on a socket.
//! - [`saved_sessions`]: the saved-session catalog, the resident-session
//!   create and attach requests, and the [`DaemonLauncher`] seam that starts
//!   a daemon before a connection.
//! - [`launcher`]: [`ProcessLauncher`], the [`DaemonLauncher`] that starts a
//!   supervisor command (`eukhe --mode daemon ...`, or a bundled
//!   `eukhe-daemon supervisor ...`) detached and waits until it greets.
//!
//! [`DaemonClient`]: daemon_client::DaemonClient
//! [`DaemonClientEvent`]: daemon_client::DaemonClientEvent
//! [`DaemonLauncher`]: saved_sessions::DaemonLauncher
//! [`ProcessLauncher`]: launcher::ProcessLauncher

pub mod daemon_build;
pub mod daemon_client;
pub mod direct_transport;
pub mod launcher;
pub mod saved_sessions;
