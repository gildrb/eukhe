//! Endpoints at paths too long to name one. An endpoint name holds 107
//! bytes on Linux (an abstract name) and 103 on macOS (a socket file path),
//! so an endpoint under a deep agent dir or a long `$HOME` (the chat's
//! `lock`, a worker's socket, the daemon's) cannot be bound at its path.
//! Its endpoint is bound at a short path instead, `sock/<hash of the
//! path's canonical form>` in the run dir (`<agent dir>/run`), else in
//! `/tmp/eukhe-<uid>` when even that is too long; both dirs pass the socket
//! dir check. The long path is a symbolic link to it: the transport
//! connects through the link
//! (`eukhe_types::platform::transport::endpoint_behind`).

use std::path::{Path, PathBuf};

use anyhow::{anyhow, Result};
use eukhe_types::platform::transport::{
    bind_transport, is_addressable, TransportListener, ENDPOINTS_ARE_FILES,
};
use sha2::Digest as _;

use super::socket_dir::prepare_socket_dir;

/// The dir of the short endpoints, in the run dir or `/tmp/eukhe-<uid>`.
const SHORT_DIR: &str = "sock";

/// Bind the endpoint at `path` with the server peer rule, its socket file
/// (macOS) private to this user. A `path` too long to name an endpoint
/// binds at its [`short_endpoint`] and becomes a symbolic link to it; an
/// existing `path` is in use, as for a bind (`AddrInUse`).
///
/// # Errors
///
/// The bind fails, no short dir passes the socket dir check, or the link
/// cannot be made.
#[tracing::instrument(skip_all, fields(path = %path.display()))]
pub async fn bind_endpoint(path: &Path) -> Result<Box<dyn TransportListener>> {
    if is_addressable(path) {
        let listener = bind_transport(path, eukhe_bend::rules::fsmode::peer_verdict).await?;
        restrict(path)?;
        return Ok(listener);
    }
    match std::fs::symlink_metadata(path) {
        Ok(_) => return Err(std::io::Error::from(std::io::ErrorKind::AddrInUse).into()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => return Err(error.into()),
    }
    let endpoint = short_endpoint(path)?;
    // No link names the endpoint: a socket file there is a dead owner's.
    remove_if_present(&endpoint)?;
    let listener = bind_transport(&endpoint, eukhe_bend::rules::fsmode::peer_verdict).await?;
    restrict(&endpoint)?;
    if let Err(error) = std::os::unix::fs::symlink(&endpoint, path) {
        drop(listener);
        remove_if_present(&endpoint)?;
        return Err(anyhow::Error::from(error).context(format!(
            "link {} to its endpoint {}",
            path.display(),
            endpoint.display()
        )));
    }
    Ok(listener)
}

/// The short endpoint of `path`: `sock/<hash of the canonical path>` in the
/// run dir, else in `/tmp/eukhe-<uid>` when even that path is too long (a
/// deep agent dir). The dir it is in passes the socket dir check (created
/// when missing).
///
/// # Errors
///
/// `path` has no dir, its dir cannot be resolved, or no short dir is short
/// enough or passes the check.
pub fn short_endpoint(path: &Path) -> Result<PathBuf> {
    let (Some(dir), Some(file_name)) = (path.parent(), path.file_name()) else {
        return Err(anyhow!("the endpoint {} has no directory", path.display()));
    };
    let canonical = std::fs::canonicalize(dir)?.join(file_name);
    let digest = sha2::Sha256::digest(canonical.as_os_str().as_encoded_bytes());
    let name = digest[..8]
        .iter()
        .fold(String::with_capacity(16), |mut name, byte| {
            use std::fmt::Write as _;
            // Writing to a String cannot fail.
            let _ = write!(name, "{byte:02x}");
            name
        });
    let fallback = Path::new("/tmp").join(format!(
        "eukhe-{}",
        eukhe_types::platform::access::current_uid()
    ));
    let base = [eukhe_types::platform::daemon_socket::socket_dir(), fallback]
        .into_iter()
        .find(|base| is_addressable(&base.join(SHORT_DIR).join(&name)))
        .ok_or_else(|| anyhow!("no socket dir is short enough for {}", path.display()))?;
    let short_dir = base.join(SHORT_DIR);
    prepare_socket_dir(&base)?;
    prepare_socket_dir(&short_dir)?;
    Ok(short_dir.join(name))
}

/// Remove the link at `path` and, where endpoints are files, the socket
/// file it names: for a link whose endpoint nothing serves.
///
/// # Errors
///
/// A removal fails other than for a missing file.
pub fn remove_link(path: &Path) -> std::io::Result<()> {
    if ENDPOINTS_ARE_FILES {
        let endpoint = eukhe_types::platform::transport::endpoint_behind(path);
        if eukhe_types::platform::endpoints::is_socket_file(&endpoint) {
            remove_if_present(&endpoint)?;
        }
    }
    remove_if_present(path)
}

/// Make the socket file at `path` private (endpoints that are files).
fn restrict(path: &Path) -> Result<()> {
    if ENDPOINTS_ARE_FILES {
        super::restrict_file(path)
            .map_err(|error| anyhow!("set mode 0600 on the socket {}: {error}", path.display()))?;
    }
    Ok(())
}

fn remove_if_present(path: &Path) -> std::io::Result<()> {
    match std::fs::remove_file(path) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(error),
    }
}
