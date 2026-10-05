//! Cross-crate platform contracts: transport, process identity, and home-dir
//! resolution.
//!
//! eukhe-types is the only crate every platform consumer can depend on
//! (eukhe-tui depends on eukhe-types alone; eukhe-daemon, eukhe-cli, eukhe-core all sit
//! above it), so the shared platform traits live here. Every implementation
//! is cfg-gated per platform: Unix sockets and `/proc` today, named pipes and
//! native process queries on Windows later. Adding a platform means adding an
//! implementation - call sites never branch on `cfg` themselves.

pub mod dirs;
pub mod identity;
pub mod process;
pub mod terminal;
pub mod transport;
#[cfg(windows)]
pub(crate) mod windows_pipe;

pub use dirs::{agent_dir, home_dir};
pub use identity::socket_identity;
pub use process::{
    ignore_sigint_for_suspend, is_process_alive, process_start_id, restore_default_sigint,
    stop_own_process_group,
};
pub use transport::{
    bind_transport, connect_blocking, connect_transport, BlockingTransportStream,
    TransportListener, TransportStream,
};
