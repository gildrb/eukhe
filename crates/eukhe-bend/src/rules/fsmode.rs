//! Who reaches eukhe's own state (`bend/fsmode.bend`, entry
//! `bend/ffi_fsmode.bend`; `laws/fsmode.bend`): the check of the socket
//! dir, the peer rule of every socket listener, the modes of what eukhe
//! creates and the working dir of a session create. Each function encodes
//! the facts Rust read, calls [`Entry::Fsmode`] and decodes the verdict.

use eukhe_types::platform::access::PeerVerdict;

use crate::wire::{Reader, Writer};
use crate::{call, expect_core, Entry, Error};

/// What `symlink_metadata` found at the socket dir.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Node {
    Missing,
    Dir,
    Link,
    Other,
}

/// Why the socket dir is refused.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Why {
    /// It is a symbolic link.
    Link,
    /// It is not a directory.
    NotDir,
    /// Another uid owns it.
    Owner,
    /// A group or other user may write in it.
    Mode,
}

/// The verdict on a socket dir.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DirVerdict {
    /// It is missing: create it with this mode, then check it again.
    Create(u32),
    /// Bind in it.
    Use,
    /// Refuse it.
    Refuse(Why),
}

/// The verdict on the socket dir where `symlink_metadata` found `node`,
/// owned by `owner_uid` with permission bits `mode` (`mode & 0o7777`; 0
/// for a missing dir), for a process of `own_uid`.
#[must_use]
pub fn socket_dir(node: Node, owner_uid: u32, own_uid: u32, mode: u32) -> DirVerdict {
    expect_core(
        Entry::Fsmode,
        socket_dir_call(node, owner_uid, own_uid, mode),
    )
}

fn socket_dir_call(
    node: Node,
    owner_uid: u32,
    own_uid: u32,
    mode: u32,
) -> Result<DirVerdict, Error> {
    let mut request = Writer::new();
    request
        .tag(0)
        .tag(match node {
            Node::Missing => 0,
            Node::Dir => 1,
            Node::Link => 2,
            Node::Other => 3,
        })
        .u32(owner_uid)
        .u32(own_uid)
        .u32(mode);
    let reply = call(Entry::Fsmode, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let verdict = match reader.tag_of(3, "a socket dir verdict")? {
        0 => DirVerdict::Create(mode_of(&mut reader)?),
        1 => DirVerdict::Use,
        // `tag_of` answers a tag below 3: this is 2.
        _ => DirVerdict::Refuse(match reader.tag_of(4, "why a socket dir is refused")? {
            0 => Why::Link,
            1 => Why::NotDir,
            2 => Why::Owner,
            // `tag_of` answers a tag below 4: this is 3.
            _ => Why::Mode,
        }),
    };
    reader.end()?;
    Ok(verdict)
}

/// A mode as its user, group and other digits.
fn mode_of(reader: &mut Reader<'_>) -> Result<u32, Error> {
    let mut mode = 0;
    for _ in 0..3 {
        mode = mode * 8 + reader.tag_of(8, "an octal digit of a mode")?;
    }
    Ok(mode)
}

/// The peer rule of every eukhe socket: whether a peer of `peer_uid` is
/// accepted by a process of `own_uid`.
#[must_use]
pub fn peer_verdict(peer_uid: u32, own_uid: u32) -> PeerVerdict {
    expect_core(Entry::Fsmode, peer_call(peer_uid, own_uid))
}

fn peer_call(peer_uid: u32, own_uid: u32) -> Result<PeerVerdict, Error> {
    let mut request = Writer::new();
    request.tag(1).u32(peer_uid).u32(own_uid);
    let reply = call(Entry::Fsmode, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let verdict = if reader.bool()? {
        PeerVerdict::Accept
    } else {
        PeerVerdict::Drop
    };
    reader.end()?;
    Ok(verdict)
}

/// What eukhe creates under its home.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Made {
    Dir,
    File,
}

/// The mode of what eukhe creates.
#[must_use]
pub fn made_mode(made: Made) -> u32 {
    expect_core(Entry::Fsmode, made_call(made))
}

fn made_call(made: Made) -> Result<u32, Error> {
    let mut request = Writer::new();
    request.tag(2).tag(match made {
        Made::Dir => 0,
        Made::File => 1,
    });
    let reply = call(Entry::Fsmode, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let bits = mode_of(&mut reader)?;
    reader.end()?;
    Ok(bits)
}

/// What `metadata` found at a named working dir.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stat {
    Absent,
    File,
    Dir,
}

/// The verdict on a session create's working dir.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cwd {
    /// The session runs in it.
    Opened,
    /// The create names none (or an empty one).
    NeedsCwd,
    /// Nothing is at the path.
    Gone,
    /// The path is not a directory.
    NotDir,
}

/// The verdict on the working dir `cwd` a create names, where `metadata`
/// found `stat`.
///
/// # Errors
///
/// [`Error`] when the path does not fit the wire (more than
/// [`crate::wire::STR_MAX`] chars), or from an inconsistent build.
pub fn session_cwd(cwd: Option<&str>, stat: Stat) -> Result<Cwd, Error> {
    let mut request = Writer::new();
    request.tag(3);
    match cwd {
        None => request.none(),
        Some(path) => request.some().str(path),
    };
    request.tag(match stat {
        Stat::Absent => 0,
        Stat::File => 1,
        Stat::Dir => 2,
    });
    let reply = call(Entry::Fsmode, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let verdict = match reader.tag_of(4, "a working dir verdict")? {
        0 => Cwd::Opened,
        1 => Cwd::NeedsCwd,
        2 => Cwd::Gone,
        // `tag_of` answers a tag below 4: this is 3.
        _ => Cwd::NotDir,
    };
    reader.end()?;
    Ok(verdict)
}

#[cfg(test)]
mod tests {
    use eukhe_types::platform::access::{PRIVATE_DIR_MODE, PRIVATE_FILE_MODE};

    use super::*;

    /// Each decision comes from the compiled core, and the private modes
    /// eukhe-types holds as constants are the core's.
    #[test]
    fn the_local_access_decisions_come_from_the_compiled_core() {
        assert_eq!(
            (
                socket_dir(Node::Missing, 0, 1000, 0),
                socket_dir(Node::Dir, 1000, 1000, 0o755),
                socket_dir(Node::Dir, 1000, 1000, 0o720),
                peer_verdict(1000, 0),
                made_mode(Made::Dir),
                made_mode(Made::File),
                session_cwd(Some(""), Stat::Absent).expect("a short path"),
            ),
            (
                DirVerdict::Create(0o700),
                DirVerdict::Use,
                DirVerdict::Refuse(Why::Mode),
                PeerVerdict::Drop,
                PRIVATE_DIR_MODE,
                PRIVATE_FILE_MODE,
                Cwd::NeedsCwd,
            )
        );
    }
}
