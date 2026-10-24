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
