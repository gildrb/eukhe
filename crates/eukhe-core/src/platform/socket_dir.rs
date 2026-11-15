//! The check a socket dir passes before a bind ([`prepare_socket_dir`],
//! whose verdict is the compiled core's: `bend/fsmode.bend`, law
//! `socket_dir_owned`). Daemon sockets and the chat lock endpoints bind
//! only in a dir that passes it.

use std::os::unix::fs::{DirBuilderExt, MetadataExt};
use std::path::Path;

use anyhow::{anyhow, Context as _, Result};
use eukhe_bend::rules::fsmode::{self, DirVerdict, Node, Why};
use eukhe_types::platform::access::current_uid;

/// What [`prepare_socket_dir`] did with a safe socket dir.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SocketDir {
    /// The dir was missing: it is created with the mode the core gives
    /// (0700), then checked.
    Created,
    /// The dir exists and passes the check.
    Used,
}

/// Make `dir` ready to hold sockets. The verdict is the compiled core's
/// (`eukhe_bend::rules::fsmode::socket_dir`, laws `socket_dir_owned`,
/// `socket_dir_write_bits` and `fsmode_ffi_answers`): a missing dir (and its
/// missing parents) is created with mode 0700 in one step, with no window. An existing dir,
/// and the dir after a create, must be a real directory (not a symbolic
/// link), owned by this process's uid, with no group or other write bit.
/// Else the bind is refused: another user could replace the socket in
/// that dir and read every frame. Read and search bits are harmless: the
/// socket is 0600 and the peer rule drops other uids.
///
/// # Errors
///
/// Returns an error that names the dir, what was found and what to do
/// when the dir is not safe, or when it cannot be inspected or created.
pub fn prepare_socket_dir(dir: &Path) -> Result<SocketDir> {
    let found = match std::fs::symlink_metadata(dir) {
        Ok(found) => Some(found),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
        Err(error) => {
            return Err(error).with_context(|| format!("inspect the socket dir {}", dir.display()))
        }
    };
    match verdict(found.as_ref()) {
        DirVerdict::Use => Ok(SocketDir::Used),
        DirVerdict::Refuse(why) => Err(refused(dir, why, found.as_ref())),
        DirVerdict::Create(mode) => {
            std::fs::DirBuilder::new()
                .recursive(true)
                .mode(mode)
                .create(dir)
                .with_context(|| format!("create the socket dir {}", dir.display()))?;
            // A dir another user created between the look and the create
            // fails the same check.
            let created = std::fs::symlink_metadata(dir)
                .with_context(|| format!("inspect the socket dir {}", dir.display()))?;
            match verdict(Some(&created)) {
                DirVerdict::Use => Ok(SocketDir::Created),
                DirVerdict::Refuse(why) => Err(refused(dir, why, Some(&created))),
                DirVerdict::Create(_) => Err(anyhow!(
                    "the socket dir {} is still missing after it was created",
                    dir.display()
                )),
            }
        }
    }
}

/// The core's verdict on what `symlink_metadata` found (`None`: nothing).
fn verdict(found: Option<&std::fs::Metadata>) -> DirVerdict {
    let own_uid = current_uid();
    match found {
        None => fsmode::socket_dir(Node::Missing, 0, own_uid, 0),
        Some(found) => {
            let file_type = found.file_type();
            let node = if file_type.is_symlink() {
                Node::Link
            } else if file_type.is_dir() {
                Node::Dir
            } else {
                Node::Other
            };
            fsmode::socket_dir(node, found.uid(), own_uid, found.mode() & 0o7777)
        }
    }
}

/// The error of a refused socket dir: what was found and what to do.
fn refused(dir: &Path, why: Why, found: Option<&std::fs::Metadata>) -> anyhow::Error {
    let own_uid = current_uid();
    let problem = match why {
        Why::Link => "is a symbolic link".to_string(),
        Why::NotDir => "is not a directory".to_string(),
        Why::Owner => format!("is owned by uid {}", found.map_or(0, MetadataExt::uid)),
        Why::Mode => format!(
            "has mode {:04o}, so other users can replace its sockets",
            found.map_or(0, |found| found.mode() & 0o7777)
        ),
    };
    anyhow!(
        "the socket dir {} {problem}. eukhe binds its sockets only in a real directory \
         that uid {own_uid} owns and that no other user can write. Remove that path (or, \
         if it is your own directory, run `chmod go-w` on it), or pass --daemon-socket \
         with a path in a private directory.",
        dir.display()
    )
}
