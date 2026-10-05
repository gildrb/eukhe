//! Private-frame codec re-export. The codec is the shared worker-socket wire
//! contract (served by this crate's workers, spoken by direct-attach clients
//! in eukhe-tui/eukhe-cli), so it lives in [`eukhe_types::daemon::framing`].

pub use eukhe_types::daemon::framing::*;
