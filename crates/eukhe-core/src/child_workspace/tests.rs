use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;

use super::check::detect;
use super::{
    files, run_check, unit_of, unit_patch, CheckConfig, CheckOutcome, CheckRun, ChildWorkspace,
    Listing, ScopedHandback, BASE, CONFLICTS, HANDBACK,
};

/// Every file under `dir` with its text (`.git` left out).
fn snapshot(dir: &Path) -> BTreeMap<String, String> {
    files::walk(dir, Listing::All)
        .unwrap()
        .into_iter()
        .map(|path| {
            let text = fs::read_to_string(dir.join(&path)).unwrap();
            (path.to_string_lossy().into_owned(), text)
        })
        .collect()
}

fn write(dir: &Path, path: &str, text: &str) {
    let path = dir.join(path);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, text).unwrap();
}

fn git_run(dir: &Path, args: &[&str]) -> std::process::Output {
    std::process::Command::new("git")
        .args(args)
        .current_dir(dir)
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .output()
        .unwrap()
}

/// `git args` in `dir`, which succeeds: its standard output.
fn git(dir: &Path, args: &[&str]) -> String {
    let output = git_run(dir, args);
    assert!(
        output.status.success(),
        "git {args:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).unwrap()
}

fn files_of(pairs: &[(&str, &str)]) -> BTreeMap<String, String> {
    pairs
        .iter()
        .map(|(path, text)| ((*path).to_owned(), (*text).to_owned()))
        .collect()
}

fn names(paths: &[&str]) -> Vec<String> {
    paths.iter().map(|path| (*path).to_owned()).collect()
}

fn paths(paths: &[&str]) -> Vec<PathBuf> {
    paths.iter().map(PathBuf::from).collect()
}

/// The whole workspace as one unit, owned.
fn whole() -> (Vec<String>, Vec<bool>) {
    (names(&[""]), vec![true])
}

#[test]
fn a_path_belongs_to_its_longest_component_wise_prefix() {
    let units = names(&["", "src", "src/core", "docs/a.md"]);
    let cases = [
        "src/core/x.rs",
        "src/corex/y.rs",
        "src/lib.rs",
        "docs/a.md",
        "docs/b.md",
        "README.md",
    ];
    assert_eq!(
        cases.map(|path| unit_of(&units, Path::new(path))),
        [Some(2), Some(1), Some(1), Some(3), Some(0), Some(0)]
    );
    // Without the root unit, a path outside every unit has none.
    assert_eq!(unit_of(&names(&["src"]), Path::new("lib/x.rs")), None);
}

#[test]
fn a_childs_patch_marks_each_unit_it_changed() {
    let units = names(&["", "src", "docs"]);
    assert_eq!(
        unit_patch(&units, &paths(&["src/a.rs", "src/b.rs", "README.md"])),
        vec![Some(1), Some(1), None]
    );
}

#[tokio::test]
async fn a_workspace_copies_tracked_and_untracked_files_but_not_ignored_ones() {
    let dir = tempfile::tempdir().unwrap();
    let parent = dir.path().join("repo");
    write(&parent, ".gitignore", "target/\n");
    write(&parent, "src/a.txt", "a");
    write(&parent, "b.txt", "b");
    write(&parent, "target/out", "built");
    git(&parent, &["init", "-q"]);
    git(&parent, &["add", ".gitignore", "src/a.txt"]);
    let workspace = ChildWorkspace::at(dir.path().join("ws"));
    let report = workspace.create(&parent).await.unwrap();
    let expected = files_of(&[
        (".gitignore", "target/\n"),
        ("b.txt", "b"),
        ("src/a.txt", "a"),
    ]);
    assert_eq!(
        (
            snapshot(&workspace.root().join(BASE)),
            snapshot(&workspace.tree()),
            report.files,
            report.cloned + report.copied,
        ),
        (expected.clone(), expected, 3, 6)
    );
    // A second create keeps the copy the child already changed.
    write(&workspace.tree(), "b.txt", "changed");
    assert_eq!(workspace.create(&parent).await.unwrap(), report);
    assert_eq!(
        fs::read_to_string(workspace.tree().join("b.txt")).unwrap(),
        "changed"
    );
}

/// The child's copy is a repository of its own: `git status` and `git
/// diff` there show only the child's edits, nothing of the parent's
/// repository (history, branches, remotes, objects) is in it, and the
/// hand-back carries no `.git`.
#[tokio::test]
async fn a_child_sees_only_its_own_changes_in_git_and_none_of_the_parents_repository() {
    let dir = tempfile::tempdir().unwrap();
    let parent = dir.path().join("parent");
    write(&parent, "a.txt", "a0\n");
    write(&parent, "b.txt", "b0\n");
    git(&parent, &["init", "-q"]);
    git(&parent, &["add", "a.txt", "b.txt"]);
    let identity = ["-c", "user.name=test", "-c", "user.email=test@example.com"];
    git(
        &parent,
        &[&identity[..], &["commit", "-q", "-m", "one"]].concat(),
    );
    git(&parent, &["branch", "secret"]);
    git(
        &parent,
        &[
            "remote",
            "add",
            "origin",
            "https://example.invalid/parent.git",
        ],
    );
    let parent_head = git(&parent, &["rev-parse", "HEAD"]);
    // Uncommitted work of the parent is part of the child's start.
    write(&parent, "b.txt", "b-parent\n");
    write(&parent, "u.txt", "u0\n");
    let workspace = ChildWorkspace::at(dir.path().join("ws"));
    workspace.create(&parent).await.unwrap();
    let tree = workspace.tree();
    write(&tree, "a.txt", "a-child\n");
    write(&tree, "c.txt", "c-child\n");
    let view = |dir: &Path| {
        (
            git(dir, &["status", "--porcelain"]),
            git(dir, &["diff", "--name-only"]),
            git(dir, &["log", "--all", "--format=%s"]),
            git(dir, &["remote"]),
            git(dir, &["rev-parse", "--absolute-git-dir"]),
        )
    };
    assert_eq!(
        (
            view(&tree),
            git(&tree, &["diff", "--", "a.txt"]).contains("-a0\n+a-child\n"),
            git_run(&tree, &["cat-file", "-e", parent_head.trim()])
                .status
                .success(),
        ),
        (
            (
                " M a.txt\n?? c.txt\n".to_owned(),
                "a.txt\n".to_owned(),
                "The workspace at the child's start\n".to_owned(),
                String::new(),
                format!("{}\n", tree.canonicalize().unwrap().join(".git").display()),
            ),
            true,
            false,
        )
    );
    let (units, scope) = whole();
    let handback = workspace.hand_back_scoped(&units, &scope).await.unwrap();
    assert_eq!(
        (
            handback.taken,
            snapshot(&parent),
            git(&parent, &["status", "--porcelain"]),
            git(&parent, &["rev-list", "--all", "--count"]),
        ),
        (
            names(&["a.txt", "c.txt"]),
            files_of(&[
                ("a.txt", "a-child\n"),
                ("b.txt", "b-parent\n"),
                ("c.txt", "c-child\n"),
                ("u.txt", "u0\n"),
            ]),
            " M a.txt\n M b.txt\n?? c.txt\n?? u.txt\n".to_owned(),
            "1\n".to_owned(),
        )
    );
}

#[tokio::test]
async fn a_hand_back_takes_the_childs_changes_and_reports_conflicts() {
    let dir = tempfile::tempdir().unwrap();
    let parent = dir.path().join("parent");
    write(&parent, "a.txt", "a0");
    write(&parent, "b.txt", "b0");
    write(&parent, "c.txt", "c0");
    write(&parent, "gone.txt", "g0");
    let workspace = ChildWorkspace::at(dir.path().join("ws"));
    workspace.create(&parent).await.unwrap();
    // The child edits a, c and adds a nested file and a build output its
    // .gitignore hides; the parent edits b and c.
    write(&workspace.tree(), "a.txt", "a-child");
    write(&workspace.tree(), "c.txt", "c-child");
    write(&workspace.tree(), "new/d.txt", "d-child");
    write(&workspace.tree(), ".gitignore", "target/\n");
    write(&workspace.tree(), "target/out", "built");
    fs::remove_file(workspace.tree().join("gone.txt")).unwrap();
    write(&parent, "b.txt", "b-parent");
    write(&parent, "c.txt", "c-parent");
    let (units, scope) = whole();
    let handback = workspace.hand_back_scoped(&units, &scope).await.unwrap();
    let kept = workspace.root().join(CONFLICTS);
    assert_eq!(
        (handback, snapshot(&parent), snapshot(&kept)),
        (
            ScopedHandback {
                taken: names(&[".gitignore", "a.txt", "gone.txt", "new/d.txt"]),
                outside: Vec::new(),
                conflicts: names(&["c.txt"]),
                kept: Some(kept.to_string_lossy().into_owned()),
                patch: vec![Some(1)],
            },
            files_of(&[
                (".gitignore", "target/\n"),
                ("a.txt", "a-child"),
                ("b.txt", "b-parent"),
                ("c.txt", "c-parent"),
                ("new/d.txt", "d-child"),
            ]),
            files_of(&[("c.txt", "c-child")]),
        )
    );
    // The copies are gone; the child's directory now is the parent's.
    assert_eq!(
        (
            workspace.root().join(BASE).exists(),
            fs::read_link(workspace.tree()).unwrap(),
        ),
        (false, parent.clone())
    );
}

/// A child owning `src` changes files in and out of its scope: the
/// in-scope changes (an edit, an addition, a removal) reach the parent;
/// the rest stays under `conflicts/`, never applied.
#[tokio::test]
async fn a_scoped_hand_back_applies_only_the_childs_scope() {
    let dir = tempfile::tempdir().unwrap();
    let parent = dir.path().join("parent");
    write(&parent, "src/a.rs", "a0");
    write(&parent, "src/old.rs", "old");
    write(&parent, "docs/d.md", "d0");
    write(&parent, "README.md", "r0");
    let workspace = ChildWorkspace::at(dir.path().join("ws"));
    workspace.create(&parent).await.unwrap();
    write(&workspace.tree(), "src/a.rs", "a-child");
    write(&workspace.tree(), "src/new.rs", "new-child");
    fs::remove_file(workspace.tree().join("src/old.rs")).unwrap();
    write(&workspace.tree(), "docs/d.md", "d-child");
    write(&workspace.tree(), "top.txt", "top-child");
    let units = names(&["", "src", "docs"]);
    let scope = vec![false, true, false];
    let changed = workspace.changed().await.unwrap();
    let handback = workspace.hand_back_scoped(&units, &scope).await.unwrap();
    let kept = workspace.root().join(CONFLICTS);
    assert_eq!(
        (changed, handback, snapshot(&parent), snapshot(&kept)),
        (
            paths(&[
                "docs/d.md",
                "src/a.rs",
                "src/new.rs",
                "src/old.rs",
                "top.txt"
            ]),
            ScopedHandback {
                taken: names(&["src/a.rs", "src/new.rs", "src/old.rs"]),
                outside: names(&["docs/d.md", "top.txt"]),
                conflicts: Vec::new(),
                kept: Some(kept.to_string_lossy().into_owned()),
                patch: vec![Some(1), Some(1), Some(1)],
            },
            files_of(&[
                ("README.md", "r0"),
                ("docs/d.md", "d0"),
                ("src/a.rs", "a-child"),
                ("src/new.rs", "new-child"),
            ]),
            files_of(&[("docs/d.md", "d-child"), ("top.txt", "top-child")]),
        )
    );
}

/// A scoped hand-back a crash cut (one in-scope path replaced, one
/// out-of-scope path kept) runs again to the result of an uncut one.
#[tokio::test]
async fn a_scoped_hand_back_cut_by_a_crash_runs_again_to_the_same_result() {
    let dir = tempfile::tempdir().unwrap();
    let make = |name: &str| {
        let parent = dir.path().join(name).join("parent");
        write(&parent, "src/a.rs", "a0");
        write(&parent, "src/b.rs", "b0");
        write(&parent, "src/gone.rs", "g0");
        write(&parent, "docs/d.md", "d0");
        (parent, ChildWorkspace::at(dir.path().join(name).join("ws")))
    };
    let (clean_parent, clean) = make("clean");
    let (cut_parent, cut) = make("cut");
    for (parent, workspace) in [(&clean_parent, &clean), (&cut_parent, &cut)] {
        workspace.create(parent).await.unwrap();
        write(&workspace.tree(), "src/a.rs", "a-child");
        write(&workspace.tree(), "src/b.rs", "b-child");
        fs::remove_file(workspace.tree().join("src/gone.rs")).unwrap();
        write(&workspace.tree(), "docs/d.md", "d-child");
    }
    // The cut run replaced src/a.rs, removed src/gone.rs and kept
    // docs/d.md, then the process died before its record.
    files::replace(&cut.tree().join("src/a.rs"), &cut_parent.join("src/a.rs")).unwrap();
    files::replace(
        &cut.tree().join("src/gone.rs"),
        &cut_parent.join("src/gone.rs"),
    )
    .unwrap();
    files::replace(
        &cut.tree().join("docs/d.md"),
        &cut.root().join(CONFLICTS).join("docs/d.md"),
    )
    .unwrap();
    assert!(!cut.root().join(HANDBACK).exists());
    let units = names(&["src", "docs"]);
    let scope = vec![true, false];
    let clean_back = clean.hand_back_scoped(&units, &scope).await.unwrap();
    let cut_back = cut.hand_back_scoped(&units, &scope).await.unwrap();
    // A repeat after the record returns the record.
    let again = cut.hand_back_scoped(&units, &scope).await.unwrap();
    let relative = |back: ScopedHandback, root: &Path| ScopedHandback {
        kept: back.kept.map(|kept| {
            Path::new(&kept)
                .strip_prefix(root)
                .unwrap()
                .to_string_lossy()
                .into_owned()
        }),
        ..back
    };
    assert_eq!(
        (
            relative(cut_back.clone(), cut.root()),
            snapshot(&cut_parent),
            snapshot(&cut.root().join(CONFLICTS)),
            again,
        ),
        (
            relative(clean_back.clone(), clean.root()),
            snapshot(&clean_parent),
            snapshot(&clean.root().join(CONFLICTS)),
            cut_back,
        )
    );
    assert_eq!(
        (relative(clean_back, clean.root()), snapshot(&clean_parent)),
        (
            ScopedHandback {
                taken: names(&["src/a.rs", "src/b.rs", "src/gone.rs"]),
                outside: names(&["docs/d.md"]),
                conflicts: Vec::new(),
                kept: Some(CONFLICTS.to_owned()),
                patch: vec![Some(1), Some(1)],
            },
            files_of(&[
                ("docs/d.md", "d0"),
                ("src/a.rs", "a-child"),
                ("src/b.rs", "b-child"),
            ]),
        )
    );
}

#[tokio::test]
async fn a_hand_back_after_a_crash_removes_the_copy_the_crash_left_beside_a_path() {
    let dir = tempfile::tempdir().unwrap();
    let parent = dir.path().join("parent");
    write(&parent, "a.txt", "a0");
    let workspace = ChildWorkspace::at(dir.path().join("ws"));
    workspace.create(&parent).await.unwrap();
    write(&workspace.tree(), "a.txt", "a-child");
    // The cut run staged a.txt's copy beside it, then the process died
    // before the rename.
    write(
        &parent,
        &format!(".a.txt{}", files::STAGED_SUFFIX),
        "a-child",
    );
    let (units, scope) = whole();
    let handback = workspace.hand_back_scoped(&units, &scope).await.unwrap();
    assert_eq!(
        (handback, snapshot(&parent)),
        (
            ScopedHandback {
                taken: names(&["a.txt"]),
                outside: Vec::new(),
                conflicts: Vec::new(),
                kept: None,
                patch: vec![Some(1)],
            },
            files_of(&[("a.txt", "a-child")]),
        )
    );
}

#[tokio::test]
async fn a_path_the_parent_holds_as_a_directory_or_under_a_file_is_a_conflict() {
    let dir = tempfile::tempdir().unwrap();
    let parent = dir.path().join("parent");
    write(&parent, "a.txt", "a0");
    let workspace = ChildWorkspace::at(dir.path().join("ws"));
    workspace.create(&parent).await.unwrap();
    // The child adds the file p and the file q/x; the parent adds the
    // directory p/ and the file q.
    write(&workspace.tree(), "a.txt", "a-child");
    write(&workspace.tree(), "p", "p-child");
    write(&workspace.tree(), "q/x", "x-child");
    write(&parent, "p/inner", "inner-parent");
    write(&parent, "q", "q-parent");
    let (units, scope) = whole();
    let handback = workspace.hand_back_scoped(&units, &scope).await.unwrap();
    let kept = workspace.root().join(CONFLICTS);
    assert_eq!(
        (handback, snapshot(&parent), snapshot(&kept)),
        (
            ScopedHandback {
                taken: names(&["a.txt"]),
                outside: Vec::new(),
                conflicts: names(&["p", "q/x"]),
                kept: Some(kept.to_string_lossy().into_owned()),
                patch: vec![Some(1)],
            },
            files_of(&[
                ("a.txt", "a-child"),
                ("p/inner", "inner-parent"),
                ("q", "q-parent"),
            ]),
            files_of(&[("p", "p-child"), ("q/x", "x-child")]),
        )
    );
}

#[test]
fn a_cargo_check_tests_each_crate_owning_a_touched_file() {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    write(
        root,
        "Cargo.toml",
        "[workspace]\nmembers = [\"crates/*\"]\n",
    );
    write(root, "Cargo.lock", "");
    write(root, "crates/a/Cargo.toml", "[package]\nname = \"alpha\"\n");
    write(root, "crates/a/src/lib.rs", "");
    write(root, "crates/b/Cargo.toml", "[package]\nname = \"beta\"\n");
    write(root, "crates/b/tests/t.rs", "");
    write(root, "crates/c/Cargo.toml", "[package]\nname = \"gamma\"\n");
    assert_eq!(
        detect(
            root,
            &[
                root.join("crates/b/tests/t.rs"),
                PathBuf::from("crates/a/src/lib.rs"),
                PathBuf::from("crates/a/src/removed.rs"),
                PathBuf::from("Cargo.lock"),
            ],
        ),
        Some("cargo test -p 'alpha' -p 'beta'".to_owned())
    );
}

#[test]
fn an_npm_check_tests_the_nearest_package() {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    write(root, "package.json", "{}");
    write(root, "index.js", "");
    write(root, "web/package.json", "{}");
    write(root, "web/src/x.ts", "");
    assert_eq!(
        [
            detect(root, &paths(&["web/src/x.ts"])),
            detect(root, &paths(&["index.js", "web/src/x.ts"])),
        ],
        [
            Some("npm --prefix 'web' test".to_owned()),
            Some("npm test && npm --prefix 'web' test".to_owned()),
        ]
    );
}

#[test]
fn a_python_check_runs_the_touched_test_directories() {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    write(root, "pyproject.toml", "[project]\nname = \"p\"\n");
    write(root, "pkg/mod.py", "");
    write(root, "tests/unit/test_mod.py", "");
    assert_eq!(
        [
            detect(root, &paths(&["pkg/mod.py", "tests/unit/test_mod.py"])),
            detect(root, &paths(&["pkg/mod.py"])),
        ],
        [
            Some("python -m pytest 'tests/unit'".to_owned()),
            Some("python -m pytest .".to_owned()),
        ]
    );
}

#[tokio::test]
async fn without_a_project_or_a_command_there_is_no_check() {
    let dir = tempfile::tempdir().unwrap();
    write(dir.path(), "notes.txt", "");
    let config = CheckConfig {
        command: None,
        timeout: Duration::from_secs(60),
    };
    assert_eq!(
        run_check(dir.path(), &paths(&["notes.txt"]), &config).await,
        CheckRun::None
    );
}

/// The run without its duration (the one field a test cannot know).
fn timeless(run: CheckRun) -> CheckRun {
    match run {
        CheckRun::None => CheckRun::None,
        CheckRun::Ran {
            command,
            outcome,
            output,
            duration_ms: _,
        } => CheckRun::Ran {
            command,
            outcome,
            output,
            duration_ms: 0,
        },
    }
}

#[tokio::test]
async fn a_configured_command_wins_and_reports_its_exit_and_output() {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    write(root, "crates/a/Cargo.toml", "[package]\nname = \"alpha\"\n");
    let touched = paths(&["crates/a/src/lib.rs"]);
    let config = |command: &str| CheckConfig {
        command: Some(command.to_owned()),
        timeout: Duration::from_secs(60),
    };
    let passed = run_check(root, &touched, &config("printf ok")).await;
    let failed = run_check(root, &touched, &config("echo out; echo err >&2; exit 3")).await;
    assert_eq!(
        [timeless(passed), timeless(failed)],
        [
            CheckRun::Ran {
                command: "printf ok".to_owned(),
                outcome: CheckOutcome::Passed,
                output: "ok".to_owned(),
                duration_ms: 0,
            },
            CheckRun::Ran {
                command: "echo out; echo err >&2; exit 3".to_owned(),
                outcome: CheckOutcome::Failed { code: Some(3) },
                output: "out\nerr\n".to_owned(),
                duration_ms: 0,
            },
        ]
    );
}

#[tokio::test]
async fn a_check_past_its_timeout_is_killed() {
    let dir = tempfile::tempdir().unwrap();
    let config = CheckConfig {
        command: Some("echo started; sleep 30".to_owned()),
        timeout: Duration::from_millis(500),
    };
    assert_eq!(
        timeless(run_check(dir.path(), &[], &config).await),
        CheckRun::Ran {
            command: "echo started; sleep 30".to_owned(),
            outcome: CheckOutcome::TimedOut,
            output: "started\n".to_owned(),
            duration_ms: 0,
        }
    );
}
