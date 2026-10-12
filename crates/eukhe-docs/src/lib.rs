//! Documents: what a session reads and edits.
//!
//! - [`file_hash`]: the four-hex file tag (`[path#TAG]`), omp's xxh32 tag.
//! - [`EditStore`]: per-session snapshots of read text, seen lines, clipboard
//!   registers, and the no-op loop guard.
//! - [`text`]: line endings and the BOM, stripped for editing and restored on
//!   write.
//!
//! The hashline edit grammar, store, and messages are ported from omp
//! (`can1357/oh-my-pi`, MIT; see `THIRD-PARTY-NOTICES`).

mod error;
mod path;
mod store;
pub mod text;

pub use error::{EditError, EditResult};
pub use path::{canonical_key, resolve};
pub use store::{
    file_hash, payload_hash, seen_lines_from_body, Clipboard, EditStore, Snapshot,
    DEFAULT_MAX_PATHS, DEFAULT_MAX_TOTAL_BYTES, DEFAULT_MAX_VERSIONS_PER_PATH,
    MAX_SNAPSHOT_FILE_BYTES, NOOP_HARD_LIMIT,
};
