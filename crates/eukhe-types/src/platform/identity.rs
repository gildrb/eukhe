//! Filesystem identity of a daemon socket endpoint.
//!
//! A ticket or stale-file check must prove the file at a socket path is the
//! same filesystem object it was when the identity was recorded (dev + ino
//! survive path rewrites and pid reuse).

use std::path::Path;

use crate::daemon::SocketIdentity;

/// Stat the endpoint's filesystem identity (dev + ino); `None` when the
/// socket file cannot be stated.
#[must_use]
pub fn socket_identity(path: &Path) -> Option<SocketIdentity> {
    use std::os::unix::fs::MetadataExt;
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
}
