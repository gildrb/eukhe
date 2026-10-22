//! Local access: only this uid reaches eukhe's own state. The private
//! modes every file and directory eukhe creates under its home gets, the
//! uid of this process, and the peer rule of the daemon sockets (Bend
//! model: `bend/fsmode.bend`, laws `LAWS.bend` section `fsmode`).

/// The mode of a file eukhe creates under its home: owner read and write.
pub const PRIVATE_FILE_MODE: u32 = 0o600;
/// The mode of a directory eukhe creates under its home: owner only.
pub const PRIVATE_DIR_MODE: u32 = 0o700;
/// The group and other write bits. A socket dir with either can have its
/// socket replaced by another user, so the daemon refuses it. Read and
/// search bits only let another user try to connect: the socket is 0600
/// and the peer rule drops every peer of another uid.
pub const GROUP_OTHER_WRITE_BITS: u32 = 0o022;

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

/// The peer rule of every eukhe socket: accept a peer only when its uid is
/// `own_uid`.
#[must_use]
pub fn peer_verdict(peer_uid: u32, own_uid: u32) -> PeerVerdict {
    if peer_uid == own_uid {
        PeerVerdict::Accept
    } else {
        PeerVerdict::Drop
    }
}
