//! The session's document authority: one [`EditStore`] and the lock
//! directory every write takes its path lock in.

use std::path::{Path, PathBuf};

use crate::read::{self, ReadError, ReadView};
use crate::store::EditStore;
use crate::write::{self, WriteError, WriteOutcome};

/// Reads, writes, and edits of one session.
#[derive(Clone)]
pub struct Documents {
    store: EditStore,
    lock_dir: PathBuf,
    home: Option<PathBuf>,
}

impl Documents {
    /// `lock_dir` is shared by every session of one eukhe home; `home`
    /// expands `~` and shortens display paths.
    #[must_use]
    pub fn new(lock_dir: PathBuf, home: Option<PathBuf>) -> Self {
        Self {
            store: EditStore::new(),
            lock_dir,
            home,
        }
    }

    #[must_use]
    pub fn store(&self) -> &EditStore {
        &self.store
    }

    /// Read `path` (with an optional `:selector`) relative to `cwd`.
    ///
    /// # Errors
    ///
    /// See [`ReadError`].
    pub fn read(&self, cwd: &Path, path: &str) -> Result<ReadView, ReadError> {
        read::read(&self.store, cwd, self.home.as_deref(), path)
    }

    /// Create or overwrite `path` relative to `cwd`.
    ///
    /// # Errors
    ///
    /// See [`WriteError`].
    pub fn write(&self, cwd: &Path, path: &str, content: &str) -> Result<WriteOutcome, WriteError> {
        let absolute = crate::path::resolve(cwd, self.home.as_deref(), path);
        let display = read::display_path(&absolute, cwd, self.home.as_deref());
        write::write_file(&self.store, &self.lock_dir, &absolute, &display, content)
    }
}
