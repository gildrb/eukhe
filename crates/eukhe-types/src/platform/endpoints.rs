//! Which socket endpoints exist, by path.
//!
//! On Linux eukhe's own endpoints are abstract sockets named by their path
//! (`transport`): no file marks them, and the kernel's census of listening
//! Unix sockets (`/proc/net/unix`, where an abstract name shows as
//! `@<name>`) is where they are found. Socket files (an earlier release's
//! daemon, another program's socket) are found on disk on every platform.

use std::path::{Path, PathBuf};

/// How a listening endpoint is named.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EndpointKind {
    /// A Linux abstract socket whose name is the path's bytes.
    Abstract,
    /// A socket file at the path.
    File,
}

/// One listening Unix socket of the kernel's census.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Listening {
    /// The socket's inode (sockfs), the key `/proc/<pid>/fd` links name.
    pub inode: u64,
    /// The endpoint's path: the file's path, or the path an abstract name
    /// spells.
    pub path: PathBuf,
    pub kind: EndpointKind,
}

/// Parse `/proc/net/unix` rows into the *listening* sockets whose name is
/// an absolute path, as a file or an abstract name (`@/...`). Columns:
/// `Num RefCount Protocol Flags Type St Inode Path`; a listener carries
/// `__SO_ACCEPTCON` (0x10000) in Flags. The path is the remainder of the
/// line after the seventh column, so a path with spaces stays whole; a
/// row whose path is not UTF-8 is skipped, the rest of the census kept.
#[must_use]
pub fn parse_proc_net_unix(bytes: &[u8]) -> Vec<Listening> {
    const SS_ACCEPTCONN: u32 = 0x0001_0000;
    let mut listeners = Vec::new();
    for line in bytes.split(|byte| *byte == b'\n') {
        let mut rest = line;
        let mut columns: Vec<&[u8]> = Vec::with_capacity(7);
        for _ in 0..7 {
            rest = rest.trim_ascii_start();
            let Some((token, after)) = split_first_token(rest) else {
                break;
            };
            columns.push(token);
            rest = after;
        }
        if columns.len() < 7 {
            continue;
        }
        let Some(flags) = std::str::from_utf8(columns[3])
            .ok()
            .and_then(|flags| u32::from_str_radix(flags, 16).ok())
        else {
            continue;
        };
        if flags & SS_ACCEPTCONN == 0 {
            continue;
        }
        let Some(name) = std::str::from_utf8(rest.trim_ascii_start()).ok() else {
            continue;
        };
        let (kind, path) = match name.strip_prefix('@') {
            Some(path) => (EndpointKind::Abstract, path),
            None => (EndpointKind::File, name),
        };
        if !path.starts_with('/') {
            continue;
        }
        let Some(inode) = std::str::from_utf8(columns[6])
            .ok()
            .and_then(|inode| inode.parse::<u64>().ok())
        else {
            continue;
        };
        listeners.push(Listening {
            inode,
            path: PathBuf::from(path),
            kind,
        });
    }
    listeners
}

fn split_first_token(bytes: &[u8]) -> Option<(&[u8], &[u8])> {
    if bytes.is_empty() {
        return None;
    }
    let end = bytes
        .iter()
        .position(u8::is_ascii_whitespace)
        .unwrap_or(bytes.len());
    Some((&bytes[..end], &bytes[end..]))
}

/// The kernel's census of listening Unix sockets with path names (Linux;
/// empty elsewhere, and when `/proc/net/unix` cannot be read).
#[must_use]
pub fn listening() -> Vec<Listening> {
    #[cfg(target_os = "linux")]
    {
        std::fs::read("/proc/net/unix")
            .map_or_else(|_| Vec::new(), |bytes| parse_proc_net_unix(&bytes))
    }
    #[cfg(not(target_os = "linux"))]
    {
        Vec::new()
    }
}

/// The listening abstract socket named by `path`, if one listens (Linux).
#[must_use]
pub fn listening_abstract(path: &Path) -> Option<Listening> {
    listening()
        .into_iter()
        .find(|listener| listener.kind == EndpointKind::Abstract && listener.path == path)
}

/// Whether a socket file is at `path` (not following a link).
#[must_use]
pub fn is_socket_file(path: &Path) -> bool {
    use std::os::unix::fs::FileTypeExt;
    std::fs::symlink_metadata(path).is_ok_and(|meta| meta.file_type().is_socket())
}

/// Whether an endpoint is at `path`: a listening abstract socket named by
/// it, or a socket file there (live or left by a crashed listener).
#[must_use]
pub fn endpoint_exists(path: &Path) -> bool {
    is_socket_file(path) || listening_abstract(path).is_some()
}

/// The endpoints directly in `dir`: socket files there, and listening
/// abstract sockets whose path's parent is `dir`. Sorted, without
/// duplicates.
#[must_use]
pub fn endpoints_in(dir: &Path) -> Vec<PathBuf> {
    let mut endpoints: Vec<PathBuf> = listening()
        .into_iter()
        .filter(|listener| {
            listener.kind == EndpointKind::Abstract && listener.path.parent() == Some(dir)
        })
        .map(|listener| listener.path)
        .collect();
    if let Ok(entries) = std::fs::read_dir(dir) {
        endpoints.extend(
            entries
                .flatten()
                .map(|entry| entry.path())
                .filter(|path| is_socket_file(path)),
        );
    }
    endpoints.sort();
    endpoints.dedup();
    endpoints
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The row shapes of `/proc/net/unix`: a listening file socket, a
    /// listening abstract socket named by a path, a connected socket (no
    /// path), a bound socket that does not listen, an abstract name that is
    /// no path, and a path with a space.
    #[test]
    fn the_census_keeps_listeners_named_by_paths() {
        let sample = b"Num       RefCount Protocol Flags    Type St Inode Path\n\
0000000047ecc27d: 00000002 00000000 00010000 0001 01  9703 /tmp/agent/daemon.sock\n\
0000000047ecc27e: 00000002 00000000 00010000 0001 01  9704 @/home/u/.eukhe/run/daemon.sock\n\
0000000000ac5346: 00000003 00000000 00000000 0001 03  9700\n\
0000000047ecc280: 00000002 00000000 00000000 0001 01  9710 /tmp/agent/bound.sock\n\
0000000047ecc281: 00000002 00000000 00010000 0001 01  9711 @xdg-portal\n\
0000000047ecc282: 00000002 00000000 00010000 0001 01  9712 /tmp/agent sandbox/daemon.sock\n";
        assert_eq!(
            parse_proc_net_unix(sample),
            vec![
                Listening {
                    inode: 9703,
                    path: PathBuf::from("/tmp/agent/daemon.sock"),
                    kind: EndpointKind::File,
                },
                Listening {
                    inode: 9704,
                    path: PathBuf::from("/home/u/.eukhe/run/daemon.sock"),
                    kind: EndpointKind::Abstract,
                },
                Listening {
                    inode: 9712,
                    path: PathBuf::from("/tmp/agent sandbox/daemon.sock"),
                    kind: EndpointKind::File,
                },
            ]
        );
    }

    /// A non-UTF-8 row is skipped; the rows after it are kept.
    #[test]
    fn a_non_utf8_row_keeps_the_rest() {
        let mut sample =
            b"0000000047ecc27d: 00000002 00000000 00010000 0001 01  9703 /tmp/".to_vec();
        sample.extend_from_slice(b"\xff/daemon.sock\n");
        sample.extend_from_slice(
            b"0000000047ecc27e: 00000002 00000000 00010000 0001 01  9704 @/tmp/a.sock\n",
        );
        assert_eq!(
            parse_proc_net_unix(&sample),
            vec![Listening {
                inode: 9704,
                path: PathBuf::from("/tmp/a.sock"),
                kind: EndpointKind::Abstract,
            }]
        );
    }

    /// A bound endpoint is found in its dir and by its path; after it
    /// closes it is gone (Linux: no file is left).
    #[tokio::test]
    async fn a_bound_endpoint_is_found_until_it_closes() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let socket = dir.path().join("daemon.sock");
        let listener = crate::platform::transport::bind_tokio(&socket).expect("bind");
        assert_eq!(
            (endpoint_exists(&socket), endpoints_in(dir.path())),
            (true, vec![socket.clone()])
        );
        drop(listener);
        #[cfg(target_os = "linux")]
        assert_eq!(
            (endpoint_exists(&socket), endpoints_in(dir.path())),
            (false, Vec::<PathBuf>::new())
        );
    }
}
