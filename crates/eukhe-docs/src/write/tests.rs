use std::path::Path;
use std::sync::Mutex;

use eukhe_types::path_policy::RealPath;

use super::*;
use crate::gate::Open;
use crate::hashline::{apply_hashline, FileChange, HashlineOptions};

/// A gate that records each check and refuses every access to a path
/// under `refused`.
struct Recorder {
    refused: PathBuf,
    checks: Mutex<Vec<(Access, PathBuf, String)>>,
}

impl AccessGate for Recorder {
    fn check(&self, access: Access, real: &RealPath, display: &str) -> Result<(), String> {
        let real = real.path();
        self.checks
            .lock()
            .unwrap()
            .push((access, real.to_path_buf(), display.to_owned()));
        if real.starts_with(&self.refused) {
            Err("the user denied it".to_owned())
        } else {
            Ok(())
        }
    }
}

struct Fixture {
    dir: tempfile::TempDir,
    store: EditStore,
}

impl Fixture {
    fn new() -> Self {
        Self {
            dir: tempfile::tempdir().unwrap(),
            store: EditStore::new(),
        }
    }

    fn locks(&self) -> PathBuf {
        self.dir.path().join("locks")
    }

    fn path(&self, name: &str) -> PathBuf {
        self.dir.path().join(name)
    }

    fn write(&self, name: &str, content: &str) -> WriteOutcome {
        self.write_over(name, content, Base::Seen).unwrap()
    }

    /// Mark the current bytes of `name` seen, as a read does.
    fn saw(&self, name: &str) {
        let path = self.path(name);
        self.store.saw_bytes(
            &eukhe_types::path_policy::real_path(&path),
            &std::fs::read(&path).unwrap(),
        );
    }

    fn write_over(
        &self,
        name: &str,
        content: &str,
        base: Base<'_>,
    ) -> Result<WriteOutcome, WriteError> {
        write_file(
            &self.store,
            &self.locks(),
            &Open,
            &self.path(name),
            name,
            content,
            base,
        )
    }

    /// `[name#TAG]` of the current text of `name`, recorded with every
    /// line seen.
    fn header(&self, name: &str) -> String {
        let text = std::fs::read_to_string(self.path(name)).unwrap();
        let text = crate::text::normalize_to_lf(crate::text::strip_bom(&text).1).into_owned();
        let lines: Vec<u32> = (1..=u32::try_from(text.split('\n').count()).unwrap()).collect();
        let tag = self.store.record(
            &eukhe_types::path_policy::real_path(&self.path(name)),
            &text,
            Some(&lines),
        );
        format!("[{name}#{tag}]")
    }

    /// Apply `payload` with `faults` and, before the writes, rewrite every
    /// file of `changed` on disk (another program).
    fn edit(
        &self,
        payload: &str,
        faults: &dyn Faults,
        changed: &[&str],
    ) -> Result<crate::hashline::HashlineOutcome, EditError> {
        let locks = self.locks();
        let writer = Interloper {
            inner: LockedWriter {
                lock_dir: &locks,
                gate: &Open,
                faults,
            },
            changed: changed.iter().map(|name| self.path(name)).collect(),
        };
        apply_hashline(
            payload,
            &HashlineOptions {
                cwd: self.dir.path(),
                home: None,
                enforce_seen_lines: true,
            },
            &self.store,
            &writer,
        )
    }

    fn read(&self, name: &str) -> Option<String> {
        std::fs::read_to_string(self.path(name)).ok()
    }
}

/// A writer that lets another program change files after the edit was
/// staged, then calls the real writer.
struct Interloper<'a> {
    inner: LockedWriter<'a>,
    changed: Vec<PathBuf>,
}

impl crate::hashline::EditWriter for Interloper<'_> {
    fn write_all(
        &self,
        requests: &[crate::hashline::WriteRequest<'_>],
    ) -> Result<Vec<crate::hashline::Published>, EditError> {
        for path in &self.changed {
            std::fs::write(path, "changed by another program\n").unwrap();
        }
        self.inner.write_all(requests)
    }
}

/// Fails the publish of the file named `name` at `stage`.
struct FailAt {
    name: &'static str,
    stage: Stage,
}

impl Faults for FailAt {
    fn inject(&self, target: &Path, stage: Stage) -> std::io::Result<()> {
        if stage == self.stage && target.file_name() == Some(std::ffi::OsStr::new(self.name)) {
            return Err(std::io::Error::other("injected"));
        }
        Ok(())
    }
}

/// `(display, change)` of every file of an outcome.
fn changes(outcome: &crate::hashline::HashlineOutcome) -> Vec<(String, FileChange)> {
    outcome
        .files
        .iter()
        .map(|file| (file.display.clone(), file.change.clone()))
        .collect()
}

#[test]
fn compare_and_swap_replaces_only_the_expected_bytes_keeping_crlf() {
    let fixture = Fixture::new();
    let path = fixture.path("a.txt");
    std::fs::write(&path, "\u{feff}one\r\ntwo\r\n").unwrap();
    let stale = fixture.write_over("a.txt", "x\n", Base::Bytes(b"one\ntwo\n"));
    assert!(matches!(stale, Err(WriteError::Changed { .. })));
    let missing = fixture.write_over("b.txt", "x\n", Base::Bytes(b""));
    assert!(matches!(missing, Err(WriteError::Changed { .. })));
    assert!(!fixture.path("b.txt").exists());
    let current = std::fs::read(&path).unwrap();
    fixture
        .write_over("a.txt", "one\nTWO\n", Base::Bytes(&current))
        .unwrap();
    assert_eq!(
        std::fs::read_to_string(&path).unwrap(),
        "\u{feff}one\r\nTWO\r\n"
    );
}

#[test]
fn creates_with_parents_and_records_every_line_seen() {
    let fixture = Fixture::new();
    let outcome = fixture.write("sub/a.txt", "one\ntwo\n");
    let tag = crate::file_hash("one\ntwo\n");
    assert_eq!(
        outcome,
        WriteOutcome {
            path: "sub/a.txt".to_owned(),
            absolute: fixture.path("sub/a.txt"),
            disposition: WriteDisposition::Created,
            bytes: 8,
            tag: Some(tag.clone()),
            warnings: Vec::new(),
            rendered: format!("[sub/a.txt#{tag}]\nSuccessfully wrote 8 bytes to sub/a.txt"),
        }
    );
    let key = eukhe_types::path_policy::real_path(&fixture.path("sub/a.txt"));
    let seen = fixture.store.head(&key).unwrap().seen_lines.unwrap();
    assert_eq!(seen.into_iter().collect::<Vec<_>>(), [1, 2]);
}

#[test]
fn overwrite_keeps_bom_crlf_and_mode() {
    let fixture = Fixture::new();
    let path = fixture.path("a.txt");
    std::fs::write(&path, "\u{FEFF}old\r\n").unwrap();
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o640)).unwrap();
    fixture.saw("a.txt");
    let outcome = fixture.write("a.txt", "new\r\nlines\r\n");
    assert_eq!(
        (
            outcome.disposition,
            std::fs::read_to_string(&path).unwrap(),
            std::fs::metadata(&path).unwrap().permissions().mode() & 0o777
        ),
        (
            WriteDisposition::Overwrote,
            "\u{FEFF}new\r\nlines\r\n".to_owned(),
            0o640
        )
    );
}

/// A BOM in the content of a file that has one is not doubled, and content
/// whose endings the file does not keep gets a warning.
#[test]
fn overwrite_never_doubles_the_bom_and_warns_of_kept_endings() {
    let fixture = Fixture::new();
    let path = fixture.path("a.txt");
    std::fs::write(&path, "\u{FEFF}old\r\n").unwrap();
    fixture.saw("a.txt");
    let outcome = fixture.write("a.txt", "\u{FEFF}new\n");
    assert_eq!(
        (std::fs::read_to_string(&path).unwrap(), outcome.warnings),
        (
            "\u{FEFF}new\r\n".to_owned(),
            vec!["a.txt keeps its CRLF line endings; the content had LF.".to_owned()]
        )
    );
}

/// Replacing a file that is not UTF-8 says that its encoding changed.
#[test]
fn overwrite_of_a_file_not_utf8_warns() {
    let fixture = Fixture::new();
    let path = fixture.path("latin1.txt");
    std::fs::write(&path, b"caf\xe9\n").unwrap();
    fixture.saw("latin1.txt");
    let outcome = fixture.write("latin1.txt", "café\n");
    assert_eq!(
        (std::fs::read_to_string(&path).unwrap(), outcome.warnings),
        (
            "café\n".to_owned(),
            vec!["latin1.txt was not UTF-8; it is now UTF-8.".to_owned()]
        )
    );
}

/// Regression: a created file that starts with `#!` was made 0o755, so
/// an agent's write made a program that a later step could run.
#[test]
fn created_script_gets_no_execute_bit() {
    let fixture = Fixture::new();
    fixture.write("run.sh", "#!/bin/sh\necho hi\n");
    let mode = std::fs::metadata(fixture.path("run.sh"))
        .unwrap()
        .permissions()
        .mode();
    assert_eq!(mode & 0o111, 0);
}

/// A write through a symlink is checked on the link's target, and a
/// refused write changes nothing.
#[test]
fn the_gate_judges_a_link_by_its_target_and_a_refusal_writes_nothing() {
    let fixture = Fixture::new();
    let top = fixture.dir.path().canonicalize().unwrap();
    std::fs::create_dir_all(top.join("cfg")).unwrap();
    std::fs::write(top.join("cfg/settings.json"), "{}").unwrap();
    std::os::unix::fs::symlink(top.join("cfg/settings.json"), top.join("link")).unwrap();
    let gate = Recorder {
        refused: top.join("cfg"),
        checks: Mutex::new(Vec::new()),
    };
    let error = write_file(
        &fixture.store,
        &fixture.locks(),
        &gate,
        &top.join("link"),
        "link",
        "{\"shell\":{\"autoEffects\":[\"exec\"]}}",
        Base::Seen,
    )
    .unwrap_err();
    assert_eq!(
        (
            error.to_string(),
            gate.checks.into_inner().unwrap(),
            std::fs::read_to_string(top.join("cfg/settings.json")).unwrap(),
        ),
        (
            "Did not write link: the user denied it".to_owned(),
            vec![(
                Access::Write,
                top.join("cfg/settings.json"),
                "link".to_owned()
            )],
            "{}".to_owned(),
        )
    );
}

#[test]
fn writing_a_directory_is_refused() {
    let fixture = Fixture::new();
    std::fs::create_dir(fixture.path("d")).unwrap();
    let error = fixture.write_over("d", "x", Base::Seen).unwrap_err();
    assert_eq!(error.to_string(), "Cannot write d: it is a directory.");
}

/// Two writers doing read-modify-write under the path lock never lose an
/// update; each opens its own lock file handle, as two processes would.
#[test]
fn path_lock_serializes_read_modify_write() {
    let dir = tempfile::tempdir().unwrap();
    let target = dir.path().join("counter");
    std::fs::write(&target, "0").unwrap();
    let locks = dir.path().join("locks");
    let rounds = 200;
    std::thread::scope(|scope| {
        for _ in 0..2 {
            scope.spawn(|| {
                for _ in 0..rounds {
                    let _lock = lock(&locks, &target).unwrap();
                    let value: u32 = std::fs::read_to_string(&target).unwrap().parse().unwrap();
                    std::thread::yield_now();
                    publish(
                        &target,
                        (value + 1).to_string().as_bytes(),
                        None,
                        Publish::Replace,
                        &NoFaults,
                    )
                    .unwrap();
                }
            });
        }
    });
    assert_eq!(
        std::fs::read_to_string(&target).unwrap(),
        (2 * rounds).to_string()
    );
}

/// A file another program changed after staging refuses the whole call:
/// the files before it are not written either.
#[test]
fn a_conflict_on_any_file_writes_no_file() {
    let fixture = Fixture::new();
    std::fs::write(fixture.path("a.txt"), "a\n").unwrap();
    std::fs::write(fixture.path("b.txt"), "b\n").unwrap();
    let payload = format!(
        "{}\nPUT >1:\n+A\n{}\nPUT >1:\n+B",
        fixture.header("a.txt"),
        fixture.header("b.txt")
    );
    let error = fixture.edit(&payload, &NoFaults, &["b.txt"]).unwrap_err();
    assert_eq!(
        (
            error.to_string(),
            fixture.read("a.txt"),
            fixture.read("b.txt")
        ),
        (
            "Edit rejected for b.txt: the file changed on disk while the edit was being \
             applied. Nothing was written. Re-read the file and retry."
                .to_owned(),
            Some("a\n".to_owned()),
            Some("changed by another program\n".to_owned())
        )
    );
}

/// A publish that fails after an earlier file landed reports what landed
/// (with its new tag) and what did not; it never says nothing was written.
#[test]
fn a_failed_publish_reports_each_file() {
    let fixture = Fixture::new();
    for name in ["a.txt", "b.txt", "c.txt"] {
        std::fs::write(fixture.path(name), "x\n").unwrap();
    }
    let payload = ["a.txt", "b.txt", "c.txt"]
        .map(|name| format!("{}\nPUT >1:\n+new", fixture.header(name)))
        .join("\n");
    let faults = FailAt {
        name: "b.txt",
        stage: Stage::BeforeRename,
    };
    let outcome = fixture.edit(&payload, &faults, &[]).unwrap();
    let new_tag = crate::file_hash("x\nnew\n");
    assert_eq!(
        (
            changes(&outcome),
            outcome.text.lines().next().unwrap().to_owned(),
            outcome.files[0].tag.clone(),
            [
                fixture.read("a.txt"),
                fixture.read("b.txt"),
                fixture.read("c.txt")
            ]
        ),
        (
            vec![
                ("a.txt".to_owned(), FileChange::Updated),
                (
                    "b.txt".to_owned(),
                    FileChange::NotWritten {
                        reason: "b.txt: injected".to_owned()
                    }
                ),
                (
                    "c.txt".to_owned(),
                    FileChange::NotWritten {
                        reason: "not tried: the write of b.txt failed first".to_owned()
                    }
                ),
            ],
            "Applied to a.txt; NOT applied to b.txt, c.txt. The applied files have the new \
             tags below; re-read the others before you edit them again."
                .to_owned(),
            Some(new_tag),
            [
                Some("x\nnew\n".to_owned()),
                Some("x\n".to_owned()),
                Some("x\n".to_owned())
            ]
        )
    );
}

/// A failed directory sync after the rename is a landed write with a
/// warning, and the store holds the new text: the next edit uses its tag.
#[test]
fn a_failed_directory_sync_is_a_landed_write() {
    let fixture = Fixture::new();
    std::fs::write(fixture.path("a.txt"), "x\n").unwrap();
    let faults = FailAt {
        name: "a.txt",
        stage: Stage::AfterRename,
    };
    let payload = format!("{}\nPUT >1:\n+y", fixture.header("a.txt"));
    let outcome = fixture.edit(&payload, &faults, &[]).unwrap();
    assert_eq!(
        (changes(&outcome), outcome.files[0].warnings.clone()),
        (
            vec![("a.txt".to_owned(), FileChange::Updated)],
            vec!["a.txt was written, but its directory sync failed: injected".to_owned()]
        )
    );
    let next = format!(
        "[a.txt#{}]\nPUT >2:\n+z",
        outcome.files[0].tag.clone().unwrap()
    );
    fixture.edit(&next, &NoFaults, &[]).unwrap();
    assert_eq!(fixture.read("a.txt"), Some("x\ny\nz\n".to_owned()));
}

/// A move whose source cannot be removed after its destination landed is
/// a landed move with a warning.
#[test]
fn a_move_that_keeps_its_source_is_reported_landed() {
    let fixture = Fixture::new();
    std::fs::write(fixture.path("a.txt"), "x\n").unwrap();
    let faults = FailAt {
        name: "a.txt",
        stage: Stage::RemoveSource,
    };
    let payload = format!("{}\nMV b.txt", fixture.header("a.txt"));
    let outcome = fixture.edit(&payload, &faults, &[]).unwrap();
    assert_eq!(
        (
            changes(&outcome),
            outcome.files[0].warnings.clone(),
            fixture.read("a.txt"),
            fixture.read("b.txt")
        ),
        (
            vec![(
                "a.txt".to_owned(),
                FileChange::Moved {
                    destination: fixture.path("b.txt")
                }
            )],
            vec![
                "a.txt was copied to b.txt, but it could not be removed: injected. Remove it \
                 with a REM edit."
                    .to_owned()
            ],
            Some("x\n".to_owned()),
            Some("x\n".to_owned())
        )
    );
}

/// `MV` onto an existing file is refused and writes nothing.
#[test]
fn a_move_never_replaces_its_destination() {
    let fixture = Fixture::new();
    std::fs::write(fixture.path("a.txt"), "a\n").unwrap();
    std::fs::write(fixture.path("b.txt"), "b\n").unwrap();
    let payload = format!("{}\nMV b.txt", fixture.header("a.txt"));
    let error = fixture.edit(&payload, &NoFaults, &[]).unwrap_err();
    assert_eq!(
        (
            error.to_string(),
            fixture.read("a.txt"),
            fixture.read("b.txt")
        ),
        (
            "Edit rejected for a.txt: the MV destination b.txt exists. Nothing was written. \
             Pick another name, or REM b.txt in an earlier edit."
                .to_owned(),
            Some("a\n".to_owned()),
            Some("b\n".to_owned())
        )
    );
}

/// A no-replace publish onto a name that appeared after the check fails
/// and leaves that file as it is.
#[test]
fn a_create_publish_never_replaces() {
    let fixture = Fixture::new();
    let target = fixture.path("b.txt");
    std::fs::write(&target, "theirs\n").unwrap();
    let error = publish(&target, b"mine\n", None, Publish::Create, &NoFaults).unwrap_err();
    assert_eq!(
        (error.kind(), fixture.read("b.txt")),
        (
            std::io::ErrorKind::AlreadyExists,
            Some("theirs\n".to_owned())
        )
    );
}

/// A write removes the temporary files a crashed writer of the same target
/// left, keeps those a live writer holds, and keeps other targets' ones.
#[test]
fn a_write_sweeps_temporary_files_of_dead_writers() {
    let fixture = Fixture::new();
    let target = fixture.path("a.txt");
    let prefix = temp_prefix(&target);
    let dead = fixture.path(&format!("{prefix}1-0"));
    let live = fixture.path(&format!("{prefix}2-0"));
    let other = fixture.path(&format!("{}1-0", temp_prefix(&fixture.path("b.txt"))));
    for path in [&dead, &live, &other] {
        std::fs::write(path, "partial").unwrap();
    }
    let held = File::open(&live).unwrap();
    held.lock().unwrap();
    fixture.write("a.txt", "x\n");
    assert_eq!(
        [dead.exists(), live.exists(), other.exists()],
        [false, true, true]
    );
}

/// A target name near the file name limit still gets a temporary file: the
/// temporary name has a fixed length.
#[test]
fn a_long_file_name_is_written() {
    let fixture = Fixture::new();
    let name = "n".repeat(250);
    fixture.write(&name, "x\n");
    assert_eq!(fixture.read(&name), Some("x\n".to_owned()));
}
