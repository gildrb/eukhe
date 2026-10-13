use super::*;

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

    fn write(&self, name: &str, content: &str) -> WriteOutcome {
        self.write_over(name, content, Base::Any).unwrap()
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
            &self.dir.path().join(name),
            name,
            content,
            base,
        )
    }
}

#[test]
fn compare_and_swap_replaces_only_the_expected_bytes_keeping_crlf() {
    let fixture = Fixture::new();
    let path = fixture.dir.path().join("a.txt");
    std::fs::write(&path, "\u{feff}one\r\ntwo\r\n").unwrap();
    let stale = fixture.write_over("a.txt", "x\n", Base::Bytes(b"one\ntwo\n"));
    assert!(matches!(stale, Err(WriteError::Changed { .. })));
    let missing = fixture.write_over("b.txt", "x\n", Base::Bytes(b""));
    assert!(matches!(missing, Err(WriteError::Changed { .. })));
    assert!(!fixture.dir.path().join("b.txt").exists());
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
            absolute: fixture.dir.path().join("sub/a.txt"),
            disposition: WriteDisposition::Created,
            bytes: 8,
            tag: Some(tag.clone()),
            made_executable: false,
            rendered: format!("[sub/a.txt#{tag}]\nSuccessfully wrote 8 bytes to sub/a.txt"),
        }
    );
    let key = crate::canonical_key(&fixture.dir.path().join("sub/a.txt"));
    let seen = fixture.store.head(&key).unwrap().seen_lines.unwrap();
    assert_eq!(seen.into_iter().collect::<Vec<_>>(), [1, 2]);
}

#[test]
fn overwrite_keeps_bom_crlf_and_mode() {
    let fixture = Fixture::new();
    let path = fixture.dir.path().join("a.txt");
    std::fs::write(&path, "\u{FEFF}old\r\n").unwrap();
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o640)).unwrap();
    let outcome = fixture.write("a.txt", "new\nlines\n");
    assert_eq!(outcome.disposition, WriteDisposition::Overwrote);
    assert_eq!(
        std::fs::read_to_string(&path).unwrap(),
        "\u{FEFF}new\r\nlines\r\n"
    );
    assert_eq!(
        std::fs::metadata(&path).unwrap().permissions().mode() & 0o777,
        0o640
    );
}

#[test]
fn created_script_is_executable() {
    let fixture = Fixture::new();
    let outcome = fixture.write("run.sh", "#!/bin/sh\necho hi\n");
    let mode = std::fs::metadata(fixture.dir.path().join("run.sh"))
        .unwrap()
        .permissions()
        .mode();
    assert_eq!((outcome.made_executable, mode & 0o111), (true, 0o111));
}

#[test]
fn writing_a_directory_is_refused() {
    let fixture = Fixture::new();
    std::fs::create_dir(fixture.dir.path().join("d")).unwrap();
    let error = fixture.write_over("d", "x", Base::Any).unwrap_err();
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
                    replace_atomic(&target, (value + 1).to_string().as_bytes(), None).unwrap();
                }
            });
        }
    });
    assert_eq!(
        std::fs::read_to_string(&target).unwrap(),
        (2 * rounds).to_string()
    );
}
