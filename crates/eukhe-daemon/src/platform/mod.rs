//! eukhe-daemon platform wall: endpoint naming and identity. The
//! transport itself is the shared trait in `eukhe_types::platform` (daemon
//! sockets bind/connect through it without touching the supervisor or
//! worker loops).

mod executable;
mod paths;

pub(crate) use executable::worker_image;

#[cfg(test)]
pub(crate) use paths::SocketDir;
pub use paths::{
    default_daemon_socket_path, socket_dir, socket_identity, worker_socket_path, SocketIdentity,
};
pub(crate) use paths::{prepare_socket_dir, worker_socket_prefix};
