//! Documents: what a session reads and edits.
//!
//! - [`file_hash`]: the four-hex file tag (`[path#TAG]`), omp's xxh32 tag.
//! - [`EditStore`]: per-session snapshots of read text, seen lines, clipboard
//!   registers, and the no-op loop guard.
//! - [`Documents`]: the session's authority: reads project `[path#TAG]` plus
//!   `N:TEXT` rows and record seen lines; writes take an OS path lock and
//!   replace files atomically.
//! - [`text`]: line endings and the BOM, stripped for editing and restored on
//!   write.
//! - [`rebase_content`]: byte-level three-way rebase of a stale edit onto the
//!   current file.
//!
//! The hashline edit grammar, store, and messages are ported from omp
//! (`can1357/oh-my-pi`, MIT; see `THIRD-PARTY-NOTICES`).

mod diag;
mod documents;
mod error;
mod path;
mod read;
mod rebase;
mod store;
pub mod text;
mod write;

pub use diag::{Diag, DiagKind, Severity};
pub use documents::Documents;
pub use error::{EditError, EditResult};
pub use path::{canonical_key, resolve};
pub use read::{
    display_path, DirEntry, FileView, LineSpan, ReadContent, ReadError, ReadView, SelectorError,
    DEFAULT_WINDOW_LINES,
};
pub use rebase::{
    apply_edits, canonical_edits, rebase_content, rebase_edits, validate_edits, AppliedEdits,
    ByteEdit, ByteEditError, ByteRange, RebaseConflict,
};
pub use store::{
    file_hash, payload_hash, seen_lines_from_body, Clipboard, EditStore, Snapshot,
    DEFAULT_MAX_PATHS, DEFAULT_MAX_TOTAL_BYTES, DEFAULT_MAX_VERSIONS_PER_PATH,
    MAX_SNAPSHOT_FILE_BYTES, NOOP_HARD_LIMIT,
};
pub use write::{WriteDisposition, WriteError, WriteOutcome};
