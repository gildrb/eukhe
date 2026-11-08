//! The seen lines beyond one process (model `reload` in
//! `bend/doc_seen.bend`, laws `reload_keeps_exactly_the_live_version` and
//! `reload_sees_exactly_the_live_records` in `laws/doc_seen.bend`): each
//! time lines of a version become seen, the [`EditStore`] appends a
//! [`SeenRecord`] to the host's [`SeenJournal`]. A later process of the same
//! session restores, for each file it edits, the records of the text the
//! file holds then ([`EditStore::restore`]): those whose tag and digest name
//! that text. The records of any other version are dropped, so a file
//! changed between the processes has no seen lines, as in one process.
//!
//! [`EditStore`]: crate::EditStore
//! [`EditStore::restore`]: crate::EditStore::restore

use std::path::PathBuf;

/// Lines of one version of a file that became seen: the canonical path,
/// the version's four-hex tag and the digest of its text (xxh64 of the
/// LF-normalized text, 16 hex digits: the tag alone can collide), and the
/// lines as runs `(lo, hi)`, both ends included.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SeenRecord {
    pub path: PathBuf,
    pub tag: String,
    pub digest: String,
    pub runs: Vec<(u32, u32)>,
}

/// Where a session keeps its [`SeenRecord`]s, so a later process of the
/// session (a headless `-c` turn, a worker restart, a resume) knows which
/// lines the model saw. The store appends each record as it happens and
/// loads them all once, at the first restore of the process.
/// Implementations keep the records in order, need not sync them (a lost
/// record costs a re-read, never a wrong edit), and report their own
/// failures: `load` answers the records it could read.
pub trait SeenJournal: Send + Sync {
    /// Every record appended so far, in order.
    fn load(&self) -> Vec<SeenRecord>;
    /// Append one record.
    fn append(&self, record: &SeenRecord);
}

/// The lines as maximal runs of consecutive lines, in order.
pub(crate) fn runs(lines: &[u32]) -> Vec<(u32, u32)> {
    let mut sorted = lines.to_vec();
    sorted.sort_unstable();
    sorted.dedup();
    let mut runs: Vec<(u32, u32)> = Vec::new();
    for line in sorted {
        match runs.last_mut() {
            Some((_, hi)) if hi.checked_add(1) == Some(line) => *hi = line,
            Some(_) | None => runs.push((line, line)),
        }
    }
    runs
}

/// The records of one file a reload keeps when the file holds the text
/// tagged `tag` with digest `digest`: exactly those of that version, in
/// order (model `reload`).
pub(crate) fn reload(records: Vec<SeenRecord>, tag: &str, digest: &str) -> Vec<SeenRecord> {
    records
        .into_iter()
        .filter(|record| record.tag == tag && record.digest == digest)
        .collect()
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;
    use std::path::Path;
    use std::sync::Arc;

    use parking_lot::Mutex;

    use super::*;
    use crate::gate::Open;
    use crate::store::{digest, file_hash};
    use crate::testing::Rng;
    use crate::{Documents, EditStore};

    /// A journal in memory, shared by the "processes" of one session.
    #[derive(Default)]
    struct Memory(Mutex<Vec<SeenRecord>>);

    impl SeenJournal for Memory {
        fn load(&self) -> Vec<SeenRecord> {
            self.0.lock().clone()
        }

        fn append(&self, record: &SeenRecord) {
            self.0.lock().push(record.clone());
        }
    }

    #[test]
    fn lines_become_maximal_runs() {
        assert_eq!(
            runs(&[7, 1, 2, 3, 3, 9, 8, u32::MAX, 5]),
            vec![(1, 3), (5, 5), (7, 9), (u32::MAX, u32::MAX)]
        );
        assert_eq!(runs(&[]), Vec::new());
    }

    /// The laws `reload_keeps_exactly_the_live_version` and
    /// `reload_sees_exactly_the_live_records` on the real store: on 200
    /// logs of one file over three versions (two of them with one tag, so
    /// only the digest tells them apart), a later store restores, for the
    /// version the file holds, exactly the lines the records of that
    /// version name; of a file holding a version no record names, nothing.
    #[test]
    fn a_restore_sees_exactly_the_records_of_the_text_on_disk() {
        let (alike, other) = (1..)
            .map(|n| format!("{n}\n").repeat(12))
            .find_map(|first| {
                let tag = file_hash(&first);
                (1..200_000)
                    .map(|m| format!("{first}{m}\n"))
                    .find(|second| file_hash(second) == tag)
                    .map(|second| (first, second))
            })
            .expect("a tag collision");
        let texts = [alike, other, "x\n".repeat(12)];
        let path = Path::new("/w/a.txt");
        let mut rng = Rng(0x5ee1_0ad0_c4ed_0001);
        for _ in 0..200 {
            let journal: Arc<dyn SeenJournal> = Arc::new(Memory::default());
            let mut expected: [BTreeSet<u32>; 3] = Default::default();
            for _ in 0..rng.range(0, 6) {
                let version = usize::try_from(rng.below(3)).unwrap();
                let lines: Vec<u32> = (0..rng.range(1, 4))
                    .map(|_| u32::try_from(rng.range(1, 12)).unwrap())
                    .collect();
                expected[version].extend(&lines);
                let text = &texts[version];
                journal.append(&SeenRecord {
                    path: path.to_owned(),
                    tag: file_hash(text),
                    digest: digest(text.as_bytes()),
                    runs: runs(&lines),
                });
            }
            let live = usize::try_from(rng.below(3)).unwrap();
            let store = EditStore::journaled(Arc::clone(&journal));
            store.restore(path, &texts[live]);
            let restored = store
                .by_content(path, &texts[live])
                .and_then(|snapshot| snapshot.seen_lines)
                .unwrap_or_default();
            assert_eq!(restored, expected[live], "{:?}", journal.load());
            let fresh = EditStore::journaled(journal);
            fresh.restore(path, "never seen\n");
            assert!(fresh.head(path).is_none());
        }
    }

    /// A second process of the session (a new store on the same journal)
    /// takes an edit on the lines the first one's edit showed, without a
    /// read; a file changed between them is refused as unseen.
    #[test]
    fn the_next_process_edits_what_the_last_one_saw() {
        let dir = tempfile::tempdir().unwrap();
        let cwd = dir.path().join("w");
        std::fs::create_dir(&cwd).unwrap();
        std::fs::write(cwd.join("a.txt"), "one\ntwo\nthree\n").unwrap();
        let journal: Arc<dyn SeenJournal> = Arc::new(Memory::default());
        let process = || Documents::journaled(dir.path().join("locks"), None, Arc::clone(&journal));
        let first = process();
        let view = first.read(&cwd, "a.txt", &Open).unwrap();
        if let crate::read::ReadContent::File(file) = &view.content {
            let lines: Vec<u32> = file.rows.iter().map(|row| row.line).collect();
            first.mark_seen(&view.absolute, file.tag.as_deref().unwrap(), &lines);
        }
        let header = view.rendered.lines().next().unwrap().to_owned();
        let edited = first
            .edit(&cwd, &format!("{header}\nPUT 2.=2:\n+TWO"), &Open)
            .unwrap();
        let tag = edited.files[0].tag.clone().unwrap();
        let second = process()
            .edit(&cwd, &format!("[a.txt#{tag}]\nPUT 3.=3:\n+THREE"), &Open)
            .map(|outcome| outcome.files.len())
            .map_err(|error| error.to_string());
        let after = std::fs::read_to_string(cwd.join("a.txt")).unwrap();
        std::fs::write(cwd.join("a.txt"), "uno\ndos\ntres\n").unwrap();
        let changed = process()
            .edit(
                &cwd,
                &format!("[a.txt#{}]\nPUT 1.=1:\n+UNO", file_hash("uno\ndos\ntres\n")),
                &Open,
            )
            .map(|outcome| outcome.files.len())
            .map_err(|error| error.to_string().contains("never displayed"));
        assert_eq!(
            (second, after, changed),
            (Ok(1), "one\nTWO\nTHREE\n".to_owned(), Err(true))
        );
    }
}
