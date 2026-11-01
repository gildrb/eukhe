//! The daemon-attached ACP transport's typed failures. Each Display is the
//! exact text the ACP reply (`internal_error` details) or the startup
//! error carries.

use std::sync::Arc;

/// A failed exchange on the supervisor socket.
#[derive(Debug, thiserror::Error)]
pub(crate) enum DaemonLinkError {
    #[error("timed out connecting to the daemon socket")]
    ConnectTimeout,
    #[error(transparent)]
    Connect(anyhow::Error),
    #[error("the daemon did not send its handshake")]
    HandshakeTimeout,
    #[error("the daemon connection closed before the handshake")]
    HandshakeClosed,
    /// The command envelope does not serialize.
    #[error(transparent)]
    Encode(serde_json::Error),
    #[error("the daemon connection is closed")]
    Closed,
    #[error("timed out waiting for the daemon response")]
    ResponseTimeout,
    #[error("the daemon connection closed mid-request")]
    ClosedMidRequest,
}

/// A failed daemon command: the exchange, the daemon's refusal, or an
/// answer without the shape the command promises.
#[derive(Debug, thiserror::Error)]
pub(crate) enum DaemonCommandError {
    #[error(transparent)]
    Link(#[from] DaemonLinkError),
    /// The daemon answered `success: false`: its error text, verbatim.
    #[error("{}", message.as_deref().unwrap_or("unknown error"))]
    Refused { message: Option<String> },
    /// The command's arguments do not serialize.
    #[error(transparent)]
    Encode(serde_json::Error),
    /// The answer's data does not decode.
    #[error(transparent)]
    Decode(serde_json::Error),
    #[error("the daemon returned no session input pause id")]
    NoPauseId,
    #[error("get_rlm_children answered no children array")]
    NoChildrenArray,
    /// The stop targets a session this connection no longer hosts.
    #[error("Unknown ACP session: {session_id}")]
    UnknownSession { session_id: String },
}

/// Why an ACP request against the hosted session was refused before it
/// reached the daemon (the TS checks' order and texts).
#[derive(Debug, thiserror::Error)]
pub(crate) enum AcpRefusal {
    #[error("Unknown ACP session: {session_id}")]
    UnknownSession { session_id: String },
    #[error("ACP session is closing: {session_id}")]
    Closing { session_id: String },
    #[error("ACP session is already closing: {session_id}")]
    AlreadyClosing { session_id: String },
    #[error("ACP session is cancelling: {session_id}")]
    Cancelling { session_id: String },
    /// A failed stop fences the session (TS `entry.stopFailure`).
    #[error("ACP session stop failed: {source}")]
    StopFailed {
        #[source]
        source: Arc<DaemonCommandError>,
    },
    #[error("A prompt turn is already running for this ACP session")]
    TurnRunning,
}
