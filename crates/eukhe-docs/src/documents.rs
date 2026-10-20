//! The session's document authority: one [`EditStore`] and the lock
//! directory every write takes its path lock in. Every call takes the
//! host's [`AccessGate`]: each path access happens only after it let it.

use std::path::{Path, PathBuf};

use crate::error::EditError;
use crate::gate::AccessGate;
use crate::glob::{GlobError, GlobOutput, GlobRequest};
use crate::grep::{GrepError, GrepOutput, GrepRequest};
use crate::hashline::{apply_hashline, HashlineOptions, HashlineOutcome};
use crate::read::{self, ReadError, ReadView};
use crate::store::EditStore;
use crate::url::{Located, Url};
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

    /// Record `lines` of the version tagged `tag` of `absolute` as seen:
    /// the rows of a read or grep result that reached the model, after its
    /// output was bounded. Only seen lines are edit anchors.
    pub fn mark_seen(&self, absolute: &Path, tag: &str, lines: &[u32]) {
        self.store
            .record_seen_lines(&eukhe_types::path_policy::real_path(absolute), tag, lines);
    }

    /// Read `path` (with an optional `:selector`) relative to `cwd`.
    ///
    /// # Errors
    ///
    /// See [`ReadError`].
    pub fn read(
        &self,
        cwd: &Path,
        path: &str,
        gate: &dyn AccessGate,
    ) -> Result<ReadView, ReadError> {
        read::read(&self.store, cwd, self.home.as_deref(), path, gate)
    }

    /// Read the file-backed internal URL `url` (`repo://`, `skill://`;
    /// its path may carry a `:selector`): `locate` turns the names the
    /// path reaches under its scheme's root into the file or directory to
    /// read and that root. Display paths stay relative to `cwd`.
    ///
    /// # Errors
    ///
    /// [`ReadError::Url`] when the path goes above its root, as written or
    /// through a symlink, [`ReadError::NotFound`] when `locate` finds
    /// nothing; else see [`ReadError`].
    pub fn read_under(
        &self,
        cwd: &Path,
        url: Url<'_>,
        locate: impl Fn(&[&str]) -> Option<Located>,
        gate: &dyn AccessGate,
    ) -> Result<ReadView, ReadError> {
        read::read_under(&self.store, cwd, self.home.as_deref(), url, locate, gate)
    }

    /// Create `path` relative to `cwd`, or overwrite it when its bytes on
    /// disk are a version this session saw (a read, a grep, or its own
    /// write or edit).
    ///
    /// # Errors
    ///
    /// [`WriteError::Unseen`] when the file holds bytes this session never
    /// saw (nothing is written); otherwise see [`WriteError`].
    pub fn write(
        &self,
        cwd: &Path,
        path: &str,
        content: &str,
        gate: &dyn AccessGate,
    ) -> Result<WriteOutcome, WriteError> {
        let absolute = crate::path::resolve(cwd, self.home.as_deref(), path);
        let display = read::display_path(&absolute, cwd, self.home.as_deref());
        write::write_file(
            &self.store,
            &self.lock_dir,
            gate,
            &absolute,
            &display,
            content,
            write::Base::Seen,
        )
    }

    /// Replace `path` (relative to `cwd`) with `content` only if its bytes
    /// on disk are still `expected`, under its path lock: the
    /// compare-and-swap write for callers that computed `content` from a
    /// read of their own (LSP renames and code actions). The file keeps its
    /// BOM, line endings, and mode, and the store records the new text.
    ///
    /// # Errors
    ///
    /// [`WriteError::Changed`] when the file is missing or its bytes differ
    /// from `expected` (nothing is written); otherwise see [`WriteError`].
    pub fn replace_if(
        &self,
        cwd: &Path,
        path: &str,
        expected: &[u8],
        content: &str,
        gate: &dyn AccessGate,
    ) -> Result<WriteOutcome, WriteError> {
        let absolute = crate::path::resolve(cwd, self.home.as_deref(), path);
        let display = read::display_path(&absolute, cwd, self.home.as_deref());
        write::write_file(
            &self.store,
            &self.lock_dir,
            gate,
            &absolute,
            &display,
            content,
            write::Base::Bytes(expected),
        )
    }

    /// Apply a hashline payload (`[path#TAG]` sections) relative to `cwd`.
    /// The seen-line guard is on: an anchor on a line no read or grep
    /// showed is rejected with that line revealed, so a straight retry
    /// works. The writes of one call are all checked against the bytes the
    /// edit was applied to, under their path locks, before any is written.
    ///
    /// # Errors
    ///
    /// The model-facing parse, anchor, stale-tag, seen-line, no-op loop, or
    /// write error; see [`apply_hashline`].
    pub fn edit(
        &self,
        cwd: &Path,
        input: &str,
        gate: &dyn AccessGate,
    ) -> Result<HashlineOutcome, EditError> {
        let options = HashlineOptions {
            cwd,
            home: self.home.as_deref(),
            enforce_seen_lines: true,
        };
        let writer = LockedWriter {
            lock_dir: &self.lock_dir,
            gate,
            faults: &write::NoFaults,
        };
        apply_hashline(input, &options, &self.store, &writer)
    }

    /// Search under `cwd`; shown lines become editable anchors.
    ///
    /// # Errors
    ///
    /// See [`GrepError`].
    pub fn grep(
        &self,
        cwd: &Path,
        request: &GrepRequest,
        gate: &dyn AccessGate,
    ) -> Result<GrepOutput, GrepError> {
        crate::grep::grep(&self.store, cwd, request, gate)
    }

    /// Match paths under `cwd`, newest first.
    ///
    /// # Errors
    ///
    /// See [`GlobError`].
    pub fn glob(
        &self,
        cwd: &Path,
        request: &GlobRequest,
        gate: &dyn AccessGate,
    ) -> Result<GlobOutput, GlobError> {
        crate::glob::glob(cwd, request, gate)
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::*;
    use crate::gate::Open;
    use crate::write::WriteDisposition;

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
            let view = docs.read(&cwd, "a.txt", &Open).unwrap();
            show(docs, &view);
            view.rendered.lines().next().unwrap().to_owned()
        };
        let (h1, h2) = (header(&first), header(&second));
        first
            .edit(&cwd, &format!("{h1}\nPUT 1.=1:\n+ONE"), &Open)
            .unwrap();
        second
            .edit(&cwd, &format!("{h2}\nPUT 3.=3:\n+THREE"), &Open)
            .unwrap();
        assert_eq!(
            std::fs::read_to_string(cwd.join("a.txt")).unwrap(),
            "ONE\ntwo\nTHREE\n"
        );
    }

    /// The rows a read showed, marked seen as the documents tools do once
    /// the output reached the model.
    fn show(docs: &Documents, view: &ReadView) {
        if let crate::read::ReadContent::File(file) = &view.content {
            let lines: Vec<u32> = file.rows.iter().map(|row| row.line).collect();
            docs.mark_seen(&view.absolute, file.tag.as_deref().unwrap(), &lines);
        }
    }

    /// The seen-line guard is on: an anchor outside the rows a read showed
    /// is refused with the line revealed, and the same edit then applies.
    #[test]
    fn an_edit_outside_the_shown_rows_is_refused_then_applies() {
        let dir = tempfile::tempdir().unwrap();
        let cwd = dir.path().join("w");
        std::fs::create_dir(&cwd).unwrap();
        let source = (1..=10).map(|n| n.to_string() + "\n").collect::<String>();
        std::fs::write(cwd.join("a.txt"), &source).unwrap();
        let docs = session(dir.path());
        let view = docs.read(&cwd, "a.txt:1-1", &Open).unwrap();
        show(&docs, &view);
        let header = view.rendered.lines().next().unwrap().to_owned();
        let payload = format!("{header}\nPUT 9.=9:\n+NINE");
        let refused = docs.edit(&cwd, &payload, &Open).unwrap_err().to_string();
        let applied = docs
            .edit(&cwd, &payload, &Open)
            .map(|outcome| outcome.files.len());
        assert_eq!(
            (
                refused.contains("9:9"),
                applied.unwrap(),
                std::fs::read_to_string(cwd.join("a.txt")).unwrap()
            ),
            (true, 1, source.replace("9\n", "NINE\n"))
        );
    }

    /// After an edit lands, the lines the model saw before it (and the
    /// lines it wrote) stay seen under the new tag; the others do not.
    #[test]
    fn seen_lines_carry_across_a_landed_edit() {
        let dir = tempfile::tempdir().unwrap();
        let cwd = dir.path().join("w");
        std::fs::create_dir(&cwd).unwrap();
        let source = (1..=10).map(|n| n.to_string() + "\n").collect::<String>();
        std::fs::write(cwd.join("a.txt"), &source).unwrap();
        let docs = session(dir.path());
        let view = docs.read(&cwd, "a.txt:1-3", &Open).unwrap();
        show(&docs, &view);
        let header = view.rendered.lines().next().unwrap().to_owned();
        let first = docs
            .edit(
                &cwd,
                &format!("{header}\nPUT 2.=2:\n+TWO\n+TWO AND A HALF"),
                &Open,
            )
            .unwrap();
        let header = format!("[a.txt#{}]", first.files[0].tag.clone().unwrap());
        let kept = docs
            .edit(&cwd, &format!("{header}\nPUT 4.=4:\n+THREE"), &Open)
            .unwrap();
        let header = format!("[a.txt#{}]", kept.files[0].tag.clone().unwrap());
        let unseen = docs.edit(&cwd, &format!("{header}\nPUT 9.=9:\n+EIGHT"), &Open);
        assert_eq!(
            (
                unseen.is_err(),
                std::fs::read_to_string(cwd.join("a.txt")).unwrap()
            ),
            (
                true,
                source.replacen("2\n3\n", "TWO\nTWO AND A HALF\nTHREE\n", 1)
            )
        );
    }

    #[test]
    fn locked_writer_refuses_bytes_that_changed_since_staging() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("a.txt");
        std::fs::write(&path, "other writer\n").unwrap();
        let writer = LockedWriter {
            lock_dir: &dir.path().join("locks"),
            gate: &Open,
            faults: &write::NoFaults,
        };
        let error = crate::hashline::EditWriter::write_all(
            &writer,
            &[crate::hashline::WriteRequest {
                absolute: &path,
                display: "a.txt",
                op: crate::hashline::WriteOp::Update {
                    before_raw: "staged from\n",
                    content: "mine\n",
                },
            }],
        )
        .unwrap_err();
        assert_eq!(
            (error.to_string(), std::fs::read_to_string(&path).unwrap()),
            (
                "Edit rejected for a.txt: the file changed on disk while the edit was being \
                 applied. Nothing was written. Re-read the file and retry."
                    .to_owned(),
                "other writer\n".to_owned()
            )
        );
    }

    /// The write tool replaces a file only from a version this session saw:
    /// a file it never read, or one another program changed after its read,
    /// is refused; after a read, or for a new file, the write lands.
    #[test]
    fn write_replaces_only_a_version_this_session_saw() {
        let dir = tempfile::tempdir().unwrap();
        let cwd = dir.path().join("w");
        std::fs::create_dir(&cwd).unwrap();
        let docs = session(dir.path());
        let path = cwd.join("a.txt");
        std::fs::write(&path, "theirs\n").unwrap();
        let never_read = docs
            .write(&cwd, "a.txt", "mine\n", &Open)
            .unwrap_err()
            .to_string();
        docs.read(&cwd, "a.txt", &Open).unwrap();
        std::fs::write(&path, "theirs again\n").unwrap();
        let changed_after_read = docs
            .write(&cwd, "a.txt", "mine\n", &Open)
            .unwrap_err()
            .to_string();
        let kept = std::fs::read_to_string(&path).unwrap();
        docs.read(&cwd, "a.txt", &Open).unwrap();
        let after_read = docs
            .write(&cwd, "a.txt", "mine\n", &Open)
            .map(|outcome| outcome.disposition);
        let again = docs
            .write(&cwd, "a.txt", "mine 2\n", &Open)
            .map(|outcome| outcome.disposition);
        let created = docs
            .write(&cwd, "b.txt", "new\n", &Open)
            .map(|outcome| outcome.disposition);
        let refusal = "Cannot write a.txt: it changed since you last read it, or you never read \
                       it. Nothing was written; read it, then write again.";
        assert_eq!(
            (
                never_read.as_str(),
                changed_after_read.as_str(),
                kept.as_str(),
                after_read.unwrap(),
                again.unwrap(),
                created.unwrap(),
                std::fs::read_to_string(&path).unwrap()
            ),
            (
                refusal,
                refusal,
                "theirs again\n",
                WriteDisposition::Overwrote,
                WriteDisposition::Overwrote,
                WriteDisposition::Created,
                "mine 2\n".to_owned()
            )
        );
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
                        let view = docs.read(cwd, "a.txt", &Open).unwrap();
                        show(&docs, &view);
                        let header = view.rendered.lines().next().unwrap().to_owned();
                        let payload = format!("{header}\nPUT {n}.={n}:\n+LINE {n}");
                        match docs.edit(cwd, &payload, &Open) {
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
