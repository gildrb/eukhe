//! The sweep of import and fork staging directories left behind.

use std::fs::{File, FileTimes};

use super::*;

/// Set the modification time of `path` to `age` ago.
fn age(path: &Path, age: Duration) {
    File::open(path)
        .expect("open")
        .set_times(FileTimes::new().set_modified(SystemTime::now() - age))
        .expect("set times");
}

/// A fresh staging directory for the session `name` under `sessions`.
fn staging(sessions: &Path, name: &str, kind: StagingKind) -> PathBuf {
    let (parent, staging) = staging_dir(&sessions.join(name), kind).expect("staging dir");
    assert_eq!(parent, sessions);
    std::fs::create_dir(&staging).expect("create staging");
    staging
}

/// The entry names of `dir`, sorted.
fn names(dir: &Path) -> Vec<String> {
    let mut names: Vec<String> = std::fs::read_dir(dir)
        .expect("read dir")
        .map(|entry| {
            entry
                .expect("entry")
                .file_name()
                .to_string_lossy()
                .into_owned()
        })
        .collect();
    names.sort();
    names
}

fn name(path: &Path) -> String {
    path.file_name()
        .expect("name")
        .to_string_lossy()
        .into_owned()
}

#[test]
fn sweeps_only_staging_dirs_and_tombstones_untouched_past_the_bound() {
    let dir = tempfile::tempdir().expect("tempdir");
    let sessions = dir.path().join("sessions");
    std::fs::create_dir(&sessions).expect("sessions");
    let stale = STALE_AFTER + Duration::from_hours(1);
    let young = STALE_AFTER
        .checked_sub(Duration::from_hours(1))
        .expect("a bound above an hour");
    let id = "0123456789abcdef0123456789abcdef";

    // Crash leftovers: no entry and the directory changed within the bound.
    let stale_import = staging(&sessions, "s1", StagingKind::Import);
    std::fs::write(stale_import.join("main.jsonl"), "{}\n").expect("main");
    age(&stale_import.join("main.jsonl"), stale);
    age(&stale_import, stale);
    let stale_fork = staging(&sessions, "s2", StagingKind::Fork);
    age(&stale_fork, stale);
    let stale_tombstone = sessions.join(format!(".s12.deleted-{id}"));
    std::fs::create_dir(&stale_tombstone).expect("tombstone");
    std::fs::write(stale_tombstone.join("main.jsonl"), "{}\n").expect("main");
    age(&stale_tombstone.join("main.jsonl"), stale);
    age(&stale_tombstone, stale);

    // Builds and deletes that may still run.
    let fresh = staging(&sessions, "s3", StagingKind::Import);
    let young_fork = staging(&sessions, "s4", StagingKind::Fork);
    age(&young_fork, young);
    let busy = staging(&sessions, "s5", StagingKind::Fork);
    std::fs::write(busy.join("main.jsonl"), "{}\n").expect("main");
    age(&busy, stale);
    let young_tombstone = sessions.join(format!(".s13.deleted-{id}"));
    std::fs::create_dir(&young_tombstone).expect("tombstone");
    age(&young_tombstone, young);

    // Everything else, as old as the leftovers.
    let elsewhere = dir.path().join("elsewhere");
    std::fs::create_dir(&elsewhere).expect("elsewhere");
    age(&elsewhere, stale);
    let mut unrelated = Vec::new();
    for other in [
        "session-1".to_owned(),
        ".s6.import-not-a-uuid".to_owned(),
        format!(".s7.export-{id}"),
        format!("s8.import-{id}"),
        format!("..import-{id}"),
        format!(".s9.fork-{}", id.to_uppercase()),
        ".s14.deleted-not-a-uuid".to_owned(),
    ] {
        let path = sessions.join(&other);
        std::fs::create_dir(&path).expect("unrelated dir");
        age(&path, stale);
        unrelated.push(other);
    }
    let file = format!(".s10.import-{id}");
    std::fs::write(sessions.join(&file), "x").expect("file");
    age(&sessions.join(&file), stale);
    let link = format!(".s11.fork-{id}");
    std::os::unix::fs::symlink(&elsewhere, sessions.join(&link)).expect("symlink");

    let sweep = sweep_stale_staging_dirs(&sessions).expect("sweep");
    let mut removed = sweep.removed;
    removed.sort();
    let mut expected_removed = vec![stale_import, stale_fork, stale_tombstone];
    expected_removed.sort();
    let failed: Vec<PathBuf> = sweep.failed.into_iter().map(|(path, _)| path).collect();
    assert_eq!((removed, failed), (expected_removed, Vec::new()));

    let mut kept = vec![
        name(&fresh),
        name(&young_fork),
        name(&busy),
        name(&young_tombstone),
        file,
        link,
    ];
    kept.extend(unrelated);
    kept.sort();
    assert_eq!(names(&sessions), kept);
    assert!(elsewhere.is_dir());
}

#[test]
fn a_missing_sessions_dir_sweeps_nothing() {
    let dir = tempfile::tempdir().expect("tempdir");
    let sweep = sweep_stale_staging_dirs(&dir.path().join("absent")).expect("sweep");
    let failed: Vec<PathBuf> = sweep.failed.into_iter().map(|(path, _)| path).collect();
    assert_eq!((sweep.removed, failed), (Vec::new(), Vec::new()));
}
