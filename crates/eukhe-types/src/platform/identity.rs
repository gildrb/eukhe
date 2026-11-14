//! Identity of a daemon socket endpoint.
//!
//! A ticket or stale-file check must prove the endpoint at a socket path is
//! the same object it was when the identity was recorded: a socket file's
//! dev + ino, or (Linux) a listening abstract socket's sockfs inode with dev
//! 0. Both survive path rewrites and pid reuse, and a new bind of the path
//! gets a new one.

use std::path::Path;

use crate::daemon::SocketIdentity;

/// The endpoint's identity: the listening abstract socket named by `path`
/// (Linux), else the socket file's dev + ino; `None` when neither is
/// there.
#[must_use]
pub fn socket_identity(path: &Path) -> Option<SocketIdentity> {
    use std::os::unix::fs::MetadataExt;
    if let Some(listener) = super::endpoints::listening_abstract(path) {
        return Some(SocketIdentity {
            dev: 0,
            ino: listener.inode,
        });
    }
    let metadata = std::fs::symlink_metadata(path).ok()?;
    Some(SocketIdentity {
        dev: metadata.dev(),
        ino: metadata.ino(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identity_is_stable_and_distinguishes_files() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let a = dir.path().join("a.sock");
        let b = dir.path().join("b.sock");
        std::fs::write(&a, b"x").expect("write");
        std::fs::write(&b, b"x").expect("write");
        let a1 = socket_identity(&a).expect("identity");
        let a2 = socket_identity(&a).expect("identity");
        assert_eq!(a1, a2, "stable for one file");
        assert_ne!(a1, socket_identity(&b).expect("identity"));
        assert_eq!(socket_identity(&dir.path().join("missing.sock")), None);
    }

    /// An endpoint bound twice at one path has two identities; a closed
    /// one has none (Linux: no file is left).
    #[tokio::test]
    async fn a_rebound_endpoint_has_a_new_identity() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let socket = dir.path().join("w.sock");
        let first = crate::platform::transport::bind_tokio(&socket).expect("bind");
        let one = socket_identity(&socket).expect("identity");
        assert_eq!(socket_identity(&socket), Some(one.clone()));
        drop(first);
        let _ = std::fs::remove_file(&socket);
        #[cfg(target_os = "linux")]
        assert_eq!(socket_identity(&socket), None);
        let _second = crate::platform::transport::bind_tokio(&socket).expect("rebind");
        assert_ne!(socket_identity(&socket), Some(one));
    }
}
