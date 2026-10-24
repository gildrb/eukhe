//! Documents: what a session reads and edits.
//!
//! - [`file_hash`]: the four-hex file tag (`[path#TAG]`), omp's xxh32 tag.
//! - [`EditStore`]: per-session snapshots of read text, seen lines, clipboard
//!   registers, and the no-op loop guard.
//! - [`AccessGate`]: the host's check of each path a tool reads or writes
//!   (the path policy and the user's approval), on the real path.
//! - [`Documents`]: the session's authority: reads project `[path#TAG]` plus
//!   `N:TEXT` rows (the caller marks the rows that reach the model seen);
//!   writes take an OS path lock and replace files atomically.
//! - [`text`]: line endings and the BOM, stripped for editing and restored on
//!   write.
//! - [`grep`]: regex search rendered as `[path#TAG]` / `N:TEXT` rows that
//!   become edit anchors.
//! - [`glob`]: matching paths, newest first, as a folded listing.
//! - [`Url`]: internal URLs (`repo://`, `skill://`, `agent://`, `memory://`)
//!   whose `..` cannot leave the scheme's root.
//! - [`rebase_content`]: byte-level three-way rebase of a stale edit onto the
//!   current file.
//! - [`apply_hashline`]: the hashline `edit` engine; writes go through the
//!   host's [`EditWriter`].
//!
//! The hashline edit grammar, store, and messages are ported from omp
//! (`can1357/oh-my-pi`, MIT; see `THIRD-PARTY-NOTICES`).

mod commit;
mod diff;
mod diff_string;
mod documents;
mod error;
mod gate;
mod glob;
mod grep;
mod hashline;
mod notice;
mod path;
mod path_tree;
mod read;
mod rebase;
mod scope;
mod store;
#[cfg(test)]
mod testing;
pub mod text;
mod url;
mod write;

pub use documents::Documents;
pub use error::{EditError, EditResult};
pub use gate::{Access, AccessGate};
pub use glob::{GlobError, GlobMatch, GlobOutput, GlobRequest, MAX_GLOB_LIMIT};
pub use grep::{ContextLine, GrepAccount, GrepError, GrepFile, GrepMatch, GrepOutput, GrepRequest};
pub use hashline::{
    apply_hashline, section_paths, EditWriter, FileChange, FileOutcome, HashlineOptions,
    HashlineOutcome, Published, WriteOp, WriteRequest, HASHLINE_DESCRIPTION,
};
pub use notice::{Notice, NoticeKind, Omitted, Severity, Unit};
pub use path::{lexical_normalize, resolve};
pub use read::{
    display_path, DirEntry, FileView, LineSpan, ReadContent, ReadError, ReadView, Row,
    SelectorError,
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
pub use url::{Located, Remote, Scheme, Url, UrlError};
pub use write::{WriteDisposition, WriteError, WriteOutcome};
