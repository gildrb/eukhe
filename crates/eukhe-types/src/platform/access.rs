//! Local access: only this uid reaches eukhe's own state. The private
//! modes every file and directory eukhe creates under its home gets (the
//! compiled core's `made_mode`, checked by `eukhe_bend::rules::fsmode`'s
//! test), the uid of this process, and the vocabulary of the peer rule
//! (the rule itself runs as the compiled core:
//! `eukhe_bend::rules::fsmode::peer_verdict`, `bend/fsmode.bend`).

/// The mode of a file eukhe creates under its home: owner read and write.
pub const PRIVATE_FILE_MODE: u32 = 0o600;
/// The mode of a directory eukhe creates under its home: owner only.
pub const PRIVATE_DIR_MODE: u32 = 0o700;

/// The real uid of this process.
#[must_use]
pub fn current_uid() -> u32 {
    nix::unistd::getuid().as_raw()
}

/// What a socket listener does with a connected peer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PeerVerdict {
    /// The peer runs as this uid: its frames are read.
    Accept,
    /// The peer runs as another uid: the connection closes before a frame
    /// is read.
    Drop,
}

/// The peer rule a listener applies to each connected peer: the verdict
/// for a peer of the first uid, in a process of the second.
pub type PeerRule = fn(u32, u32) -> PeerVerdict;

/// What a client does with the listener of an abstract endpoint (Linux),
/// where a process of any user can bind a free name first.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ServerVerdict {
    /// The listener runs as this uid and is the process recorded for the
    /// endpoint: the client talks to it.
    Served,
    /// The listener runs as another uid.
    OtherUid,
    /// No pid is recorded for the endpoint.
    NoRecord,
    /// The listener is not the recorded process.
    OtherPid,
}

/// The server rule a client applies to the listener of an abstract
/// endpoint: the verdict for a listener of the first uid and the third
/// pid, for a client of the second uid, when the fourth is the pid
/// recorded for the endpoint (0: none).
pub type ServerRule = fn(u32, u32, u32, u32) -> ServerVerdict;

/// The rules of both ends of eukhe's sockets (the compiled core's:
/// `eukhe_bend::rules::server_peer::PEER_RULES`).
#[derive(Clone, Copy, Debug)]
pub struct PeerRules {
    /// Whom a listener serves, and whom a client accepts behind a socket
    /// file (the file's dir keeps other users out).
    pub peer: PeerRule,
    /// Whom a client accepts behind an abstract endpoint.
    pub server: ServerRule,
}
