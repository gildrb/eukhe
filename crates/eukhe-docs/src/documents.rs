//! The session's document authority: one [`EditStore`] and the lock
//! directory every write takes its path lock in.

use std::path::{Path, PathBuf};

use crate::error::EditError;
use crate::glob::{GlobError, GlobOutput, GlobRequest};
use crate::grep::{GrepError, GrepOutput, GrepRequest};
use crate::hashline::{apply_hashline, HashlineOptions, HashlineOutcome};
use crate::read::{self, ReadError, ReadView};
use crate::store::EditStore;
use crate::write::{self, LockedWriter, WriteError, WriteOutcome};

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

    /// Apply a hashline payload (`[path#TAG]` sections) relative to `cwd`.
    /// Anchors must be on lines this session was shown; every write is
    /// compared against the bytes the edit was applied to under the path
    /// lock.
    ///
    /// # Errors
    ///
    /// The model-facing parse, anchor, stale-tag, seen-line, no-op loop, or
    /// write error; see [`apply_hashline`].
    pub fn edit(&self, cwd: &Path, input: &str) -> Result<HashlineOutcome, EditError> {
        let options = HashlineOptions {
            cwd,
            home: self.home.as_deref(),
            enforce_seen_lines: true,
        };
        let writer = LockedWriter {
            lock_dir: &self.lock_dir,
        };
        apply_hashline(input, &options, &self.store, &writer)
    }

    /// Search under `cwd`; shown lines become editable anchors.
    ///
    /// # Errors
    ///
    /// See [`GrepError`].
    pub fn grep(&self, cwd: &Path, request: &GrepRequest) -> Result<GrepOutput, GrepError> {
        crate::grep::grep(&self.store, cwd, request)
    }

    /// Match paths under `cwd`, newest first.
    ///
    /// # Errors
    ///
    /// See [`GlobError`].
    pub fn glob(&self, cwd: &Path, request: &GlobRequest) -> Result<GlobOutput, GlobError> {
        crate::glob::glob(cwd, request)
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::*;

    fn session(dir: &Path) -> Documents {
        Documents::new(dir.join("locks"), None)
    }

    #[test]
    fn a_stale_session_recovers_onto_another_sessions_edit() {
        let dir = tempfile::tempdir().unwrap();
        let cwd = dir.path().join("w");
        std::fs::create_dir(&cwd).unwrap();
        std::fs::write(cwd.join("a.txt"), "one\ntwo\nthree\n").unwrap();
        let (first, second) = (session(dir.path()), session(dir.path()));
        let header = |docs: &Documents| {
            let view = docs.read(&cwd, "a.txt").unwrap();
            view.rendered.lines().next().unwrap().to_owned()
        };
        let (h1, h2) = (header(&first), header(&second));
        first.edit(&cwd, &format!("{h1}\nPUT 1.=1:\n+ONE")).unwrap();
        second
            .edit(&cwd, &format!("{h2}\nPUT 3.=3:\n+THREE"))
            .unwrap();
        assert_eq!(
            std::fs::read_to_string(cwd.join("a.txt")).unwrap(),
            "ONE\ntwo\nTHREE\n"
        );
    }

    #[test]
    fn locked_writer_refuses_bytes_that_changed_since_staging() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("a.txt");
        std::fs::write(&path, "other writer\n").unwrap();
        let writer = LockedWriter {
            lock_dir: &dir.path().join("locks"),
        };
        let error = crate::hashline::EditWriter::write(
            &writer,
            &crate::hashline::WriteRequest {
                absolute: &path,
                display: "a.txt",
                op: crate::hashline::WriteOp::Update {
                    before_raw: "staged from\n",
                    content: "mine\n",
                },
            },
        )
        .unwrap_err();
        assert_eq!(
            error.to_string(),
            "Edit rejected for a.txt: the file changed on disk while the edit was being applied. \
             Nothing was written. Re-read the file and retry."
        );
        assert_eq!(std::fs::read_to_string(&path).unwrap(), "other writer\n");
    }

    /// Sessions editing one file at once never lose an update: a write
    /// whose staged bytes went stale is refused, and the retry recovers.
    #[test]
    fn concurrent_sessions_keep_every_edit() {
        let dir = tempfile::tempdir().unwrap();
        let cwd: PathBuf = dir.path().join("w");
        std::fs::create_dir(&cwd).unwrap();
        let lines = 8;
        let original = (1..=lines)
            .map(|n| format!("line {n}\n"))
            .collect::<Vec<_>>()
            .concat();
        std::fs::write(cwd.join("a.txt"), &original).unwrap();
        std::thread::scope(|scope| {
            for n in 1..=lines {
                let (cwd, locks) = (&cwd, dir.path());
                scope.spawn(move || {
                    let docs = session(locks);
                    loop {
                        let view = docs.read(cwd, "a.txt").unwrap();
                        let header = view.rendered.lines().next().unwrap().to_owned();
                        let payload = format!("{header}\nPUT {n}.={n}:\n+LINE {n}");
                        match docs.edit(cwd, &payload) {
                            Ok(_) => break,
                            Err(EditError::Apply(_) | EditError::Match(_)) => {}
                            Err(error) => panic!("{error}"),
                        }
                    }
                });
            }
        });
        let expected = (1..=lines)
            .map(|n| format!("LINE {n}\n"))
            .collect::<Vec<_>>()
            .concat();
        assert_eq!(
            std::fs::read_to_string(cwd.join("a.txt")).unwrap(),
            expected
        );
    }
}
