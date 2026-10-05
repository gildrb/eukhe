//! Cross-crate platform contracts: transport, process identity, and home-dir
//! resolution.
//!
//! eukhe-types is the only crate every platform consumer can depend on
//! (eukhe-tui depends on eukhe-types alone; eukhe-daemon, eukhe-cli, eukhe-core all sit
//! above it), so the shared platform traits live here: Unix sockets and
//! `/proc`/libproc process queries, with call sites never branching on
//! `cfg` themselves.

pub mod dirs;
pub mod identity;
pub mod process;
pub mod terminal;
pub mod transport;

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
