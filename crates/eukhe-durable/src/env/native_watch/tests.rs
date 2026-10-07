//! `NativeFileWatcher` driven directly: the watch cases of the env
//! conformance suite and `NativeExecutionEnv watch limits`
//! (`test/env-node-conformance.test.ts`), in native and polling modes.

use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use tempfile::TempDir;
use tokio::time::Instant;

use super::{NativeFileWatcher, NativeWatchOptions};
use crate::env::{
    FileErrorCode, FileWatcher, OnWatchChange, WatchChange, WatchExclude, WatchMode, WatchTarget,
};

type Changes = Arc<Mutex<Vec<WatchChange>>>;

fn native() -> NativeWatchOptions {
    NativeWatchOptions {
        mode: Some(WatchMode::Native),
        ..NativeWatchOptions::default()
    }
}

fn polling() -> NativeWatchOptions {
    NativeWatchOptions {
        mode: Some(WatchMode::Polling),
        poll_interval_ms: Some(100),
        ..NativeWatchOptions::default()
    }
}

/// A fresh directory, canonical so reported paths compare as written.
struct Root {
    _dir: TempDir,
    path: PathBuf,
}

impl Root {
    fn new() -> Self {
        let dir = tempfile::tempdir().expect("temp dir");
        let path = fs::canonicalize(dir.path()).expect("canonical temp dir");
        Self { _dir: dir, path }
    }

    fn absolute(&self, path: &str) -> String {
        self.path
            .join(path)
            .to_str()
            .expect("UTF-8 path")
            .to_owned()
    }

    /// `env.writeFile`: parents are created.
    fn write(&self, path: &str, content: &str) {
        let path = self.path.join(path);
        fs::create_dir_all(path.parent().expect("parent")).expect("create parents");
        fs::write(path, content).expect("write");
    }

    fn create_dir(&self, path: &str) {
        fs::create_dir_all(self.path.join(path)).expect("create dir");
    }

    fn rename(&self, from: &str, to: &str) {
        fs::rename(self.path.join(from), self.path.join(to)).expect("rename");
    }

    async fn open(
        &self,
        targets: Vec<WatchTarget>,
        options: &NativeWatchOptions,
    ) -> (Result<NativeFileWatcher, crate::env::FileError>, Changes) {
        let changes: Changes = Arc::default();
        let recorded = Arc::clone(&changes);
        let on_change: OnWatchChange = Arc::new(move |change| {
            recorded
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(change);
        });
        let root = self.path.clone();
        let resolve = move |path: &str| root.join(path).to_str().expect("UTF-8 path").to_owned();
        let watcher = NativeFileWatcher::open(&targets, &resolve, on_change, options).await;
        (watcher, changes)
    }

    async fn watch(
        &self,
        targets: Vec<WatchTarget>,
        options: &NativeWatchOptions,
    ) -> (NativeFileWatcher, Changes) {
        let (watcher, changes) = self.open(targets, options).await;
        (watcher.expect("watch opens"), changes)
    }
}

fn target(path: &str) -> WatchTarget {
    WatchTarget {
        path: path.to_owned(),
        ..WatchTarget::default()
    }
}

fn recursive(path: &str) -> WatchTarget {
    WatchTarget {
        path: path.to_owned(),
        recursive: true,
        ..WatchTarget::default()
    }
}

fn snapshot(changes: &Changes) -> Vec<WatchChange> {
    changes
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
}

/// Whether a change reports `path`: an overflow, or a reported path at or
/// above it.
fn covers(change: &WatchChange, path: &str) -> bool {
    match change {
        WatchChange::Overflow => true,
        WatchChange::Paths(paths) => paths
            .iter()
            .any(|reported| path == reported || path.starts_with(&format!("{reported}/"))),
        WatchChange::Error(_) => false,
    }
}

/// Wait up to three seconds for a change, after `change`, that reports `path`.
async fn expect_change(changes: &Changes, path: &str, change: impl FnOnce()) {
    let from = snapshot(changes).len();
    change();
    let deadline = Instant::now() + Duration::from_secs(3);
    loop {
        let seen = snapshot(changes);
        if seen[from..].iter().any(|entry| covers(entry, path)) {
            return;
        }
        assert!(
            Instant::now() <= deadline,
            "No change reported {path}; got {:?}",
            &seen[from..]
        );
        tokio::time::sleep(Duration::from_millis(20)).await;
    }
}

async fn reports_a_missing_files_creation_changes_replacement_and_removal(
    options: NativeWatchOptions,
) {
    let root = Root::new();
    let (watcher, changes) = root.watch(vec![target("AGENTS.md")], &options).await;
    let path = root.absolute("AGENTS.md");
    expect_change(&changes, &path, || root.write("AGENTS.md", "one")).await;
    expect_change(&changes, &path, || root.write("AGENTS.md", "two!")).await;
    // Editors replace a file by renaming a new one over it.
    expect_change(&changes, &path, || {
        root.write("AGENTS.md.tmp", "three");
        root.rename("AGENTS.md.tmp", "AGENTS.md");
    })
    .await;
    expect_change(&changes, &path, || root.write("AGENTS.md", "four")).await;
    expect_change(&changes, &path, || fs::remove_file(&path).expect("remove")).await;
    watcher.close(&BACKGROUND_CONTEXT).await;
}

async fn reports_a_missing_target_whose_ancestors_are_created(options: NativeWatchOptions) {
    let root = Root::new();
    let (watcher, changes) = root.watch(vec![target("a/b/c/AGENTS.md")], &options).await;
    let path = root.absolute("a/b/c/AGENTS.md");
    expect_change(&changes, &path, || root.write("a/b/c/AGENTS.md", "x")).await;
    watcher.close(&BACKGROUND_CONTEXT).await;
}

async fn follows_directories_created_together_with_their_contents(options: NativeWatchOptions) {
    let root = Root::new();
    root.create_dir("skills");
    let (watcher, changes) = root.watch(vec![recursive("skills")], &options).await;
    // Written before any watcher on the new directories can exist.
    let skill = root.absolute("skills/a/b/SKILL.md");
    expect_change(&changes, &skill, || {
        root.write("skills/a/b/SKILL.md", "one");
    })
    .await;
    expect_change(&changes, &skill, || {
        root.write("skills/a/b/SKILL.md", "two!");
    })
    .await;
    let deeper = root.absolute("skills/a/b/c/SKILL.md");
    expect_change(&changes, &deeper, || {
        root.write("skills/a/b/c/SKILL.md", "deeper");
    })
    .await;
    watcher.close(&BACKGROUND_CONTEXT).await;
}

async fn keeps_watching_a_path_whose_parent_is_renamed_and_recreated(options: NativeWatchOptions) {
    let root = Root::new();
    root.write("proj/.pi/skills/x.md", "x");
    let (watcher, changes) = root
        .watch(vec![recursive("proj/.pi/skills")], &options)
        .await;
    expect_change(&changes, &root.absolute("proj/.pi/skills"), || {
        root.rename("proj/.pi", "proj/old");
    })
    .await;
    let y = root.absolute("proj/.pi/skills/y.md");
    expect_change(&changes, &y, || root.write("proj/.pi/skills/y.md", "y")).await;
    expect_change(&changes, &y, || root.write("proj/.pi/skills/y.md", "yy")).await;
    watcher.close(&BACKGROUND_CONTEXT).await;
}

async fn skips_excluded_entries_and_reports_a_rename_out_of_them(options: NativeWatchOptions) {
    let root = Root::new();
    root.create_dir("skills");
    let targets = vec![WatchTarget {
        path: "skills".to_owned(),
        recursive: true,
        exclude: WatchExclude {
            hidden: true,
            names: vec!["node_modules".to_owned()],
        },
    }];
    let (watcher, changes) = root.watch(targets, &options).await;
    root.write("skills/node_modules/dep/SKILL.md", "dep");
    root.write("skills/.SKILL.md.tmp", "draft");
    expect_change(&changes, &root.absolute("skills/SKILL.md"), || {
        root.rename("skills/.SKILL.md.tmp", "skills/SKILL.md");
    })
    .await;
    let hidden = [
        root.absolute("skills/node_modules"),
        root.absolute("skills/.SKILL.md.tmp"),
    ];
    for change in snapshot(&changes) {
        let WatchChange::Paths(paths) = change else {
            continue;
        };
        for path in paths {
            assert!(
                !hidden
                    .iter()
                    .any(|excluded| path == *excluded || path.starts_with(excluded.as_str())),
                "excluded {path}"
            );
        }
    }
    watcher.close(&BACKGROUND_CONTEXT).await;
}

async fn keeps_recursive_coverage_where_a_non_recursive_target_overlaps(
    options: NativeWatchOptions,
) {
    let root = Root::new();
    root.write("skills/a/one.md", "one");
    let (watcher, changes) = root
        .watch(vec![target("skills"), recursive("skills")], &options)
        .await;
    expect_change(&changes, &root.absolute("skills/a/two.md"), || {
        root.write("skills/a/two.md", "two");
    })
    .await;
    watcher.close(&BACKGROUND_CONTEXT).await;
}

async fn follows_a_directory_replaced_at_the_same_path(options: NativeWatchOptions) {
    let root = Root::new();
    root.write("skills/a/x.md", "x");
    let (watcher, changes) = root.watch(vec![recursive("skills")], &options).await;
    expect_change(&changes, &root.absolute("skills/a"), || {
        root.rename("skills/a", "skills-old");
        root.create_dir("skills/a");
    })
    .await;
    let y = root.absolute("skills/a/y.md");
    expect_change(&changes, &y, || root.write("skills/a/y.md", "y")).await;
    expect_change(&changes, &y, || root.write("skills/a/y.md", "yy")).await;
    watcher.close(&BACKGROUND_CONTEXT).await;
}

async fn stops_reporting_once_closed(options: NativeWatchOptions) {
    let root = Root::new();
    let (watcher, changes) = root.watch(vec![target("file.txt")], &options).await;
    assert_eq!(watcher.mode(), options.mode.expect("forced mode"));
    watcher.close(&BACKGROUND_CONTEXT).await;
    watcher.close(&BACKGROUND_CONTEXT).await;
    root.write("file.txt", "x");
    tokio::time::sleep(Duration::from_millis(300)).await;
    assert!(snapshot(&changes).is_empty());
}

async fn reports_changes_to_the_file_a_target_links_to(options: NativeWatchOptions) {
    let root = Root::new();
    root.write("real/AGENTS.md", "one");
    std::os::unix::fs::symlink(
        root.path.join("real/AGENTS.md"),
        root.path.join("AGENTS.md"),
    )
    .expect("symlink");
    let (watcher, changes) = root.watch(vec![target("AGENTS.md")], &options).await;
    let path = root.absolute("AGENTS.md");
    expect_change(&changes, &path, || root.write("real/AGENTS.md", "two!")).await;
    expect_change(&changes, &path, || root.write("real/AGENTS.md", "three")).await;
    watcher.close(&BACKGROUND_CONTEXT).await;
}

async fn keeps_watching_after_a_callback_panics(options: NativeWatchOptions) {
    let root = Root::new();
    let changes: Changes = Arc::default();
    let recorded = Arc::clone(&changes);
    let calls = Arc::new(AtomicUsize::new(0));
    let counted = Arc::clone(&calls);
    let on_change: OnWatchChange = Arc::new(move |change| {
        assert!(
            counted.fetch_add(1, Ordering::SeqCst) > 0,
            "the first callback panics"
        );
        recorded
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(change);
    });
    let base = root.path.clone();
    let resolve = move |path: &str| base.join(path).to_str().expect("UTF-8 path").to_owned();
    let watcher = NativeFileWatcher::open(&[target("file.txt")], &resolve, on_change, &options)
        .await
        .expect("watch opens");
    root.write("file.txt", "one");
    let deadline = Instant::now() + Duration::from_secs(3);
    while calls.load(Ordering::SeqCst) == 0 {
        assert!(
            Instant::now() <= deadline,
            "the creation was never reported"
        );
        tokio::time::sleep(Duration::from_millis(20)).await;
    }
    // The panicking call reported the creation; later changes still arrive.
    expect_change(&changes, &root.absolute("file.txt"), || {
        root.write("file.txt", "two!");
    })
    .await;
    watcher.close(&BACKGROUND_CONTEXT).await;
}

macro_rules! in_both_modes {
    ($($scenario:ident),* $(,)?) => {
        mod native_mode {
            $(
                #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
                async fn $scenario() {
                    super::$scenario(super::native()).await;
                }
            )*
        }

        mod polling_mode {
            $(
                #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
                async fn $scenario() {
                    super::$scenario(super::polling()).await;
                }
            )*
        }
    };
}

in_both_modes!(
    reports_a_missing_files_creation_changes_replacement_and_removal,
    reports_a_missing_target_whose_ancestors_are_created,
    follows_directories_created_together_with_their_contents,
    keeps_watching_a_path_whose_parent_is_renamed_and_recreated,
    skips_excluded_entries_and_reports_a_rename_out_of_them,
    keeps_recursive_coverage_where_a_non_recursive_target_overlaps,
    follows_a_directory_replaced_at_the_same_path,
    stops_reporting_once_closed,
    reports_changes_to_the_file_a_target_links_to,
    keeps_watching_after_a_callback_panics,
);

/// Port of `NativeExecutionEnv watch limits`.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn refuses_a_tree_over_the_directory_budget_and_stops_with_an_error_when_one_grows_past_it() {
    let root = Root::new();
    let options = NativeWatchOptions {
        max_directories: Some(3),
        ..NativeWatchOptions::default()
    };
    root.create_dir("tree/a/b");
    root.create_dir("tree/c");
    let (refused, _) = root.open(vec![recursive("tree")], &options).await;
    let Err(error) = refused else {
        panic!("a tree over the budget is refused");
    };
    assert_eq!(
        (error.code, error.message.as_str(), error.path),
        (
            FileErrorCode::Invalid,
            "Watched paths exceed 3 directories",
            None
        )
    );

    fs::remove_dir_all(root.path.join("tree/c")).expect("remove");
    let (watcher, changes) = root.watch(vec![recursive("tree")], &options).await;
    root.create_dir("tree/d");
    let deadline = Instant::now() + Duration::from_secs(3);
    while !snapshot(&changes)
        .iter()
        .any(|change| matches!(change, WatchChange::Error(_)))
        && Instant::now() < deadline
    {
        tokio::time::sleep(Duration::from_millis(20)).await;
    }
    let Some(WatchChange::Error(error)) = snapshot(&changes).pop() else {
        panic!("the last change is an error: {:?}", snapshot(&changes));
    };
    assert_eq!(
        (error.code, error.message.as_str(), error.path),
        (
            FileErrorCode::Invalid,
            "Watched paths exceed 3 directories",
            None
        )
    );
    watcher.close(&BACKGROUND_CONTEXT).await;
}

/// An unreadable target directory fails `open` with node.ts `toFileError` of
/// Node's `scandir` error.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn refuses_an_unreadable_target_directory() {
    use std::os::unix::fs::PermissionsExt;

    let root = Root::new();
    root.create_dir("locked");
    let locked = root.path.join("locked");
    fs::set_permissions(&locked, fs::Permissions::from_mode(0o000)).expect("chmod");
    // Privileged users read anything; nothing to check then.
    let readable = fs::read_dir(&locked).is_ok();
    let (result, _) = root.open(vec![target("locked")], &native()).await;
    fs::set_permissions(&locked, fs::Permissions::from_mode(0o755)).expect("chmod back");
    if readable {
        assert!(result.is_ok());
        return;
    }
    let Err(error) = result else {
        panic!("an unreadable target is refused");
    };
    let path = root.absolute("locked");
    assert_eq!(
        (error.code, error.message, error.path),
        (
            FileErrorCode::PermissionDenied,
            format!("EACCES: permission denied, scandir '{path}'"),
            Some(path)
        )
    );
}

/// Changes are reported in JS's default sort order.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn reports_paths_sorted_by_utf16_code_units() {
    let root = Root::new();
    root.write("staging/\u{FF5E}", "a");
    root.write("staging/\u{1F600}", "b");
    let (watcher, changes) = root.watch(vec![target("dir")], &polling()).await;
    let dir = root.absolute("dir");
    // One rename: the next snapshot has the directory and both entries.
    expect_change(&changes, &dir, || root.rename("staging", "dir")).await;
    let Some(WatchChange::Paths(paths)) = snapshot(&changes).pop() else {
        panic!("paths reported: {:?}", snapshot(&changes));
    };
    assert_eq!(
        paths,
        [
            dir.clone(),
            root.absolute("dir/\u{1F600}"),
            root.absolute("dir/\u{FF5E}"),
        ]
    );
    watcher.close(&BACKGROUND_CONTEXT).await;
}
