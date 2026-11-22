use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsStr;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::time::Duration;

use super::check::detect;
use super::trust::{config_root, trusted_dirs, trusted_value, TRUSTED_CONFIG_PATHS};
use super::{
    files, run_check, tool_env, unit_of, unit_patch, CheckConfig, CheckOutcome, CheckReport,
    CheckRun, ChildWorkspace, GitView, Listing, ScopedHandback, TreeStamp, WorkspaceDrift, BASE,
    CONFLICTS, HANDBACK,
};
use eukhe_types::daemon::agent_tree::CheckPhase;

/// A check report nobody reads.
fn unheard(_report: CheckReport) {}

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
    let report = workspace.create(&parent, &[]).await.unwrap();
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
    assert_eq!(workspace.create(&parent, &[]).await.unwrap(), report);
    assert_eq!(
        fs::read_to_string(workspace.tree().join("b.txt")).unwrap(),
        "changed"
    );
}

/// A parent working in a directory that holds Eukhe's own state (a home
/// directory holds `~/.eukhe` and `~/.eukhe-work`) splits two children at
/// once: both copies are made, beside each other in the work root, and
/// neither holds the agent dir, the work root or the other's staging,
/// whether git lists the parent's files or the walk does.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_workspace_never_copies_eukhes_state_inside_its_parent() {
    for git_tree in [false, true] {
        let dir = tempfile::tempdir().unwrap();
        let parent = dir.path().join("home");
        write(&parent, "project/a.txt", "a");
        write(&parent, ".eukhe/settings.json", "{}");
        write(&parent, ".eukhe/sessions/s.jsonl", "{}\n");
        let (agent, work) = (parent.join(".eukhe"), parent.join(".eukhe-work"));
        let workspaces = work.join("workspaces").join("session");
        fs::create_dir_all(&workspaces).unwrap();
        if git_tree {
            git(&parent, &["init", "-q"]);
            git(&parent, &["add", "project/a.txt"]);
        }
        let (one, two) = (
            ChildWorkspace::at(workspaces.join("one")),
            ChildWorkspace::at(workspaces.join("two")),
        );
        let state = [agent.as_path(), work.as_path()];
        let (first, second) =
            tokio::join!(one.create(&parent, &state), two.create(&parent, &state));
        first.unwrap();
        second.unwrap();
        let expected = files_of(&[("project/a.txt", "a")]);
        assert_eq!(
            [snapshot(&one.tree()), snapshot(&two.tree())],
            [expected.clone(), expected],
            "git tree: {git_tree}"
        );
    }
}

/// An entry removed while the walk runs (another process renaming its
/// staging away) is not listed, and the walk goes on.
#[test]
fn a_walk_skips_an_entry_gone_while_it_walks() {
    let dir = tempfile::tempdir().unwrap();
    write(dir.path(), "a/x", "x");
    write(dir.path(), "b/y", "y");
    let mut walk = files::walked(dir.path(), Listing::All, Vec::new());
    let first = walk.next().unwrap().unwrap();
    let other = if first.starts_with("a") { "b" } else { "a" };
    fs::remove_dir_all(dir.path().join(other)).unwrap();
    let rest: Vec<PathBuf> = walk.collect::<std::io::Result<_>>().unwrap();
    assert!(rest.is_empty(), "{first:?}, then {rest:?}");
}

/// A child's copy is known by its directory until it is handed back;
/// another directory is no child's copy.
#[tokio::test]
async fn a_childs_copy_is_known_by_its_directory_until_its_hand_back() {
    let dir = tempfile::tempdir().unwrap();
    let parent = dir.path().join("parent");
    write(&parent, "a.txt", "a0");
    let workspace = ChildWorkspace::at(dir.path().join("ws"));
    workspace.create(&parent, &[]).await.unwrap();
    let found = (
        ChildWorkspace::of_tree(&workspace.tree()),
        ChildWorkspace::of_tree(&parent),
        ChildWorkspace::of_tree(workspace.root()),
    );
    let (units, scope) = whole();
    workspace.hand_back_scoped(&units, &scope).await.unwrap();
    assert_eq!(
        (found, ChildWorkspace::of_tree(&workspace.tree())),
        ((Some(workspace.clone()), None, None), None)
    );
}

/// The child's copy becomes a repository of its own at its first git, not
/// at the spawn: its index and commit are the copy as the child found it
/// (an edit made before the first git still shows), `git status` and `git
/// diff` show only the child's edits, the base commit carries no identity
/// of the environment or the configuration, nothing of the parent's
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
    workspace.create(&parent, &[]).await.unwrap();
    let tree = workspace.tree();
    write(&tree, "a.txt", "a-child\n");
    write(&tree, "n.txt", "n-child\n");
    let before = tree.join(".git").exists();
    // The first git, an exclude of the child's own repository (hiding a
    // file the child added) and a status (which writes the index) leave
    // the copy's stamp as it was: the repository is no change of the
    // tree.
    let stamp = TreeStamp::take(&tree).await;
    let views = (
        workspace.git_view().await.unwrap(),
        workspace.git_view().await.unwrap(),
    );
    write(&tree, ".git/info/exclude", "n.txt\n");
    git(&tree, &["status", "--porcelain"]);
    let drift = stamp.drift(&TreeStamp::take(&tree).await);
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
    let base_tree = git(&tree, &["rev-parse", "HEAD^{tree}"]);
    assert_eq!(
        (
            before,
            drift,
            views,
            view(&tree),
            git(&tree, &["cat-file", "commit", "HEAD"]),
            git(&tree, &["diff", "--", "a.txt"]).contains("-a0\n+a-child\n"),
            git_run(&tree, &["cat-file", "-e", parent_head.trim()])
                .status
                .success(),
        ),
        (
            false,
            WorkspaceDrift::Held,
            (GitView::Made, GitView::Present),
            (
                " M a.txt\n?? c.txt\n".to_owned(),
                "a.txt\n".to_owned(),
                "The workspace at the child's start\n".to_owned(),
                String::new(),
                format!("{}\n", tree.canonicalize().unwrap().join(".git").display()),
            ),
            format!(
                "tree {}\nauthor eukhe <eukhe@localhost> 0 +0000\n\
                 committer eukhe <eukhe@localhost> 0 +0000\n\n\
                 The workspace at the child's start\n",
                base_tree.trim()
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
            names(&["a.txt", "c.txt", "n.txt"]),
            files_of(&[
                ("a.txt", "a-child\n"),
                ("b.txt", "b-parent\n"),
                ("c.txt", "c-child\n"),
                ("n.txt", "n-child\n"),
                ("u.txt", "u0\n"),
            ]),
            " M a.txt\n M b.txt\n?? c.txt\n?? n.txt\n?? u.txt\n".to_owned(),
            "1\n".to_owned(),
        )
    );
    // The repository stays with the copy while checks run; the close
    // removes both, and the root keeps no staging of it.
    let open = workspace.tree().join(".git").is_dir();
    workspace.close().await.unwrap();
    let mut entries: Vec<String> = fs::read_dir(workspace.root())
        .unwrap()
        .map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned())
        .collect();
    entries.sort();
    assert_eq!(
        (open, fs::read_link(workspace.tree()).unwrap(), entries),
        (
            true,
            parent.clone(),
            names(&["handback.json", "manifest.json", "tree"])
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
    workspace.create(&parent, &[]).await.unwrap();
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
    // The copies stay for the checks; once closed, they are gone and the
    // child's directory is the parent's.
    let copies = (
        workspace.root().join(BASE).is_dir(),
        workspace.tree().is_symlink(),
    );
    workspace.close().await.unwrap();
    assert_eq!(
        (
            copies,
            workspace.root().join(BASE).exists(),
            fs::read_link(workspace.tree()).unwrap(),
        ),
        ((true, false), false, parent.clone())
    );
}

/// Two children change a Rust file with doc comments: the hand-back moves
/// whole files, never lines. The first child's file reaches the parent
/// byte for byte, each doc above its own item; the second child's change
/// of the same file is a conflict kept whole under `conflicts/`, and its
/// change of another file reaches the parent byte for byte.
#[tokio::test]
async fn a_hand_back_keeps_each_doc_above_its_item_or_reports_the_conflict() {
    let dir = tempfile::tempdir().unwrap();
    let parent = dir.path().join("parent");
    let lib = "/// Adds one.\npub fn inc(x: u32) -> u32 {\n    x + 1\n}\n\n/// Doubles.\n\
               pub fn double(x: u32) -> u32 {\n    x * 2\n}\n";
    write(&parent, "src/lib.rs", lib);
    write(&parent, "src/b.rs", "/// B.\npub struct B;\n");
    let first = ChildWorkspace::at(dir.path().join("first"));
    let second = ChildWorkspace::at(dir.path().join("second"));
    first.create(&parent, &[]).await.unwrap();
    second.create(&parent, &[]).await.unwrap();
    let first_lib = "/// Adds one.\npub fn inc(x: u32) -> u32 {\n    x + 1\n}\n\n/// Halves.\n\
                     pub fn half(x: u32) -> u32 {\n    x / 2\n}\n\n/// Doubles.\n\
                     pub fn double(x: u32) -> u32 {\n    x * 2\n}\n";
    let second_lib =
        format!("{lib}\n/// Subtracts one.\npub fn dec(x: u32) -> u32 {{\n    x - 1\n}}\n");
    let second_b = "/// B.\npub struct B;\n\n/// C.\npub struct C;\n";
    write(&first.tree(), "src/lib.rs", first_lib);
    write(&second.tree(), "src/lib.rs", &second_lib);
    write(&second.tree(), "src/b.rs", second_b);
    let (units, scope) = whole();
    let first_back = first.hand_back_scoped(&units, &scope).await.unwrap();
    let second_back = second.hand_back_scoped(&units, &scope).await.unwrap();
    let kept = second.root().join(CONFLICTS);
    assert_eq!(
        (first_back, second_back, snapshot(&parent), snapshot(&kept)),
        (
            ScopedHandback {
                taken: names(&["src/lib.rs"]),
                outside: Vec::new(),
                conflicts: Vec::new(),
                kept: None,
                patch: vec![Some(1)],
            },
            ScopedHandback {
                taken: names(&["src/b.rs"]),
                outside: Vec::new(),
                conflicts: names(&["src/lib.rs"]),
                kept: Some(kept.to_string_lossy().into_owned()),
                patch: vec![Some(1)],
            },
            files_of(&[("src/b.rs", second_b), ("src/lib.rs", first_lib)]),
            files_of(&[("src/lib.rs", &second_lib)]),
        )
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
    workspace.create(&parent, &[]).await.unwrap();
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
        workspace.create(parent, &[]).await.unwrap();
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
    workspace.create(&parent, &[]).await.unwrap();
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
    workspace.create(&parent, &[]).await.unwrap();
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
        progress_every: Duration::from_secs(30),
    };
    assert_eq!(
        run_check(dir.path(), &paths(&["notes.txt"]), &config, &unheard).await,
        CheckRun::None
    );
}

/// The run without its duration (the one field a test cannot know).
fn timeless(run: CheckRun) -> CheckRun {
    match run {
        CheckRun::None => CheckRun::None,
        CheckRun::Pending => CheckRun::Pending,
        CheckRun::NotRun { error } => CheckRun::NotRun { error },
        CheckRun::Ran {
            command,
            outcome,
            output,
            duration_ms: _,
            workspace,
        } => CheckRun::Ran {
            command,
            outcome,
            output,
            duration_ms: 0,
            workspace,
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
        progress_every: Duration::from_secs(30),
    };
    let passed = run_check(root, &touched, &config("printf ok"), &unheard).await;
    let failed = run_check(
        root,
        &touched,
        &config("echo out; echo err >&2; exit 3"),
        &unheard,
    )
    .await;
    assert_eq!(
        [timeless(passed), timeless(failed)],
        [
            CheckRun::Ran {
                command: "printf ok".to_owned(),
                outcome: CheckOutcome::Passed,
                output: "ok".to_owned(),
                duration_ms: 0,
                workspace: WorkspaceDrift::Held,
            },
            CheckRun::Ran {
                command: "echo out; echo err >&2; exit 3".to_owned(),
                outcome: CheckOutcome::Failed { code: Some(3) },
                output: "out\nerr\n".to_owned(),
                duration_ms: 0,
                workspace: WorkspaceDrift::Held,
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
        progress_every: Duration::from_secs(30),
    };
    assert_eq!(
        timeless(run_check(dir.path(), &[], &config, &unheard).await),
        CheckRun::Ran {
            command: "echo started; sleep 30".to_owned(),
            outcome: CheckOutcome::TimedOut,
            output: "started\n".to_owned(),
            duration_ms: 0,
            workspace: WorkspaceDrift::Held,
        }
    );
}

/// A fifo at `path`: opening it blocks until the other end opens.
fn fifo(path: &Path) {
    let made = std::process::Command::new("mkfifo")
        .arg(path)
        .status()
        .unwrap();
    assert!(made.success(), "mkfifo {}", path.display());
}

/// Regression: a check runs in a workspace others keep writing (the
/// parent's, after integration). A file written while it ran is named in
/// its report, so its result is not read as judging the tree as it
/// stands; a path written before it started is not.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_check_names_the_paths_written_while_it_ran() {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path().to_path_buf();
    git(&root, &["init", "-q"]);
    write(&root, "src/lib.rs", "pub fn a() {}\n");
    write(&root, "README.md", "a\n");
    let gates = tempfile::tempdir().unwrap();
    let gate = gates.path().join("gate");
    fifo(&gate);
    let command = format!("cat '{}' >/dev/null", gate.display());
    let config = CheckConfig {
        command: Some(command.clone()),
        timeout: Duration::from_secs(60),
        progress_every: Duration::from_secs(30),
    };
    // The edit lands once the check holds the gate open, the gate's byte
    // after it.
    let edit = {
        let (root, gate) = (root.clone(), gate.clone());
        tokio::task::spawn_blocking(move || {
            let mut opened = fs::OpenOptions::new().write(true).open(&gate).unwrap();
            write(&root, "src/lib.rs", "pub fn a() {}\npub fn b() {}\n");
            std::io::Write::write_all(&mut opened, b"go").unwrap();
        })
    };
    let run = timeless(run_check(&root, &[], &config, &unheard).await);
    edit.await.unwrap();
    assert_eq!(
        (run.clone(), run.text()),
        (
            CheckRun::Ran {
                command: command.clone(),
                outcome: CheckOutcome::Passed,
                output: String::new(),
                duration_ms: 0,
                workspace: WorkspaceDrift::Changed {
                    count: 1,
                    paths: names(&["src/lib.rs"]),
                },
            },
            format!(
                "Check `{command}`: passed in 0.0 s.\nThe workspace changed while the check ran \
                 (1 path: src/lib.rs): its result judged no single tree state."
            ),
        )
    );
}

/// A failed check names its own failure: its verdict carries the last
/// lines it printed, so a formatting failure and a test failure read
/// apart.
#[tokio::test]
async fn a_failed_check_names_its_last_lines() {
    let dir = tempfile::tempdir().unwrap();
    let fmt = "printf 'Diff in a.rs:1:\\n-fn a(){}\\n+fn a() {}\\n'; echo FMT FAILED; echo CHECK EXIT 1; exit 1";
    let tests = "echo 'test b ... FAILED'; echo TESTS FAILED; echo CHECK EXIT 1; exit 1";
    let verdict = |run: CheckRun| {
        timeless(run)
            .text()
            .lines()
            .next()
            .unwrap_or_default()
            .to_owned()
    };
    let config = |command: &str| CheckConfig {
        command: Some(command.to_owned()),
        timeout: Duration::from_secs(60),
        progress_every: Duration::from_secs(30),
    };
    assert_eq!(
        [
            verdict(run_check(dir.path(), &[], &config(fmt), &unheard).await),
            verdict(run_check(dir.path(), &[], &config(tests), &unheard).await),
        ],
        [
            format!("Check `{fmt}`: failed (exit 1) in 0.0 s; last lines: +fn a() {{}} | FMT FAILED | CHECK EXIT 1."),
            format!("Check `{tests}`: failed (exit 1) in 0.0 s; last lines: test b ... FAILED | TESTS FAILED | CHECK EXIT 1."),
        ]
    );
}

/// A check that waits (for a slot, a queue) reports while it runs: at
/// its start, then at each interval its time since the start and the last
/// line it printed, then at its end how it ended and its last lines.
#[tokio::test]
async fn a_running_check_reports_its_time_and_last_line() {
    let dir = tempfile::tempdir().unwrap();
    let command = "echo waiting for a slot; while [ ! -e release ]; do sleep 0.01; done; echo FMT FAILED; exit 1";
    let every = Duration::from_millis(20);
    let config = CheckConfig {
        command: Some(command.to_owned()),
        timeout: Duration::from_secs(60),
        progress_every: every,
    };
    let (sender, mut reports) = tokio::sync::mpsc::unbounded_channel();
    let report = move |report: CheckReport| {
        let _sent = sender.send(report);
    };
    let waiting = |report: &CheckReport| matches!(&report.phase, CheckPhase::Running { last_line: Some(line) } if line == "waiting for a slot");
    // The check ends only once a report showed it waiting.
    let heard = async {
        let mut heard = Vec::new();
        while let Some(report) = reports.recv().await {
            if waiting(&report) && !heard.iter().any(waiting) {
                fs::write(dir.path().join("release"), "").unwrap();
            }
            let ended = matches!(report.phase, CheckPhase::Ended { .. });
            heard.push(report);
            if ended {
                return heard;
            }
        }
        heard
    };
    let (run, heard) = tokio::join!(run_check(dir.path(), &[], &config, &report), heard);
    let at_start = |report: &CheckReport| CheckReport {
        elapsed_ms: 0,
        ..report.clone()
    };
    let wait = heard.iter().find(|report| waiting(report)).unwrap();
    assert_eq!(
        (
            heard.first().map(at_start),
            at_start(wait),
            wait.elapsed_ms >= u64::try_from(every.as_millis()).unwrap(),
            heard.last().map(at_start),
            timeless(run).text().lines().next().map(str::to_owned),
        ),
        (
            Some(CheckReport {
                command: command.to_owned(),
                elapsed_ms: 0,
                phase: CheckPhase::Running { last_line: None },
            }),
            CheckReport {
                command: command.to_owned(),
                elapsed_ms: 0,
                phase: CheckPhase::Running {
                    last_line: Some("waiting for a slot".to_owned()),
                },
            },
            true,
            Some(CheckReport {
                command: command.to_owned(),
                elapsed_ms: 0,
                phase: CheckPhase::Ended {
                    outcome: CheckOutcome::Failed { code: Some(1) },
                    last_lines: vec!["waiting for a slot".to_owned(), "FMT FAILED".to_owned()],
                },
            }),
            Some(format!(
                "Check `{command}`: failed (exit 1) in 0.0 s; last lines: waiting for a slot | FMT FAILED."
            )),
        )
    );
}

#[test]
fn a_mise_config_belongs_to_the_directory_its_trust_covers() {
    let roots: Vec<Option<PathBuf>> = [
        "mise.toml",
        ".mise.toml",
        "mise.local.toml",
        "crates/a/mise.ci.toml",
        "mise/config.toml",
        "sub/.mise/config.local.toml",
        ".config/mise.toml",
        ".config/mise/config.toml",
        ".config/mise/conf.d/tools.toml",
        "misery.toml",
        "mise.tom",
        "src/config.toml",
    ]
    .into_iter()
    .map(|path| config_root(Path::new(path)))
    .collect();
    assert_eq!(
        roots,
        [
            Some(""),
            Some(""),
            Some(""),
            Some("crates/a"),
            Some(""),
            Some("sub"),
            Some(""),
            Some(""),
            Some(""),
            None,
            None,
            None,
        ]
        .map(|root| root.map(PathBuf::from))
    );
}

#[test]
fn trust_show_lines_name_the_trusted_directories() {
    let show = "~/work/repo: trusted\n/tmp/other: untrusted\n/srv/x: trusted\nmise WARN noise\n";
    assert_eq!(
        trusted_dirs(show, Some(Path::new("/home/u"))),
        BTreeSet::from([PathBuf::from("/home/u/work/repo"), PathBuf::from("/srv/x")])
    );
    assert_eq!(
        trusted_value(
            &[
                PathBuf::from("/t/mise.toml"),
                PathBuf::from("/t/a/mise.toml")
            ],
            Some(OsStr::new("/host/mise.toml")),
        ),
        Some("/t/mise.toml:/t/a/mise.toml:/host/mise.toml".to_owned())
    );
    assert_eq!(trusted_value(&[], Some(OsStr::new("/host"))), None);
}

/// A `mise` stand-in in `dir`: `trust --show` reports the directory it
/// runs in trusted, except under a `sub` directory, which it reports
/// untrusted (with its trusted parent).
fn fake_mise(dir: &Path) -> PathBuf {
    let program = dir.join("mise");
    fs::write(
        &program,
        "#!/bin/sh\n[ \"$1 $2\" = \"trust --show\" ] || exit 2\nd=$(pwd)\n\
         case \"$d\" in\n*/sub) echo \"$d: untrusted\"; echo \"${d%/sub}: trusted\" ;;\n\
         *) echo \"$d: trusted\" ;;\nesac\n",
    )
    .unwrap();
    fs::set_permissions(&program, fs::Permissions::from_mode(0o755)).unwrap();
    program
}

/// The value a command in the copy gets: `trusted`, then the host's own.
fn with_host_trust(trusted: &Path) -> String {
    match std::env::var(TRUSTED_CONFIG_PATHS) {
        Ok(host) if !host.is_empty() => format!("{}:{host}", trusted.display()),
        Ok(_) | Err(_) => trusted.display().to_string(),
    }
}

/// Regression: a child's copy lives at another path, and mise keys trust
/// by path, so the parent's trusted `mise.toml` was untrusted in the copy
/// and every mise-activated command there failed. The copy now keeps the
/// trust of what the parent trusts (only that: `sub/mise.toml`, untrusted
/// in the parent, stays untrusted), its node check runs with it, and the
/// hand-back ends it.
#[tokio::test]
async fn a_childs_copy_keeps_the_mise_trust_its_parent_has() {
    let dir = tempfile::tempdir().unwrap();
    let parent = dir.path().join("parent");
    write(&parent, "mise.toml", "[tools]\n");
    write(&parent, "sub/mise.toml", "[tools]\n");
    write(&parent, "a.txt", "a");
    let mise = fake_mise(dir.path());
    let workspace = ChildWorkspace::at(dir.path().join("ws"));
    workspace
        .create_asking(&parent, &[], mise.as_os_str())
        .await
        .unwrap();
    let tree = workspace.tree();
    let value = with_host_trust(&tree.join("mise.toml"));
    let config = CheckConfig {
        command: Some(format!("printf %s \"${TRUSTED_CONFIG_PATHS}\"")),
        timeout: Duration::from_secs(60),
        progress_every: Duration::from_secs(30),
    };
    assert_eq!(
        (
            tool_env(&tree),
            tool_env(&parent),
            timeless(run_check(&tree, &[], &config, &unheard).await),
        ),
        (
            Some((TRUSTED_CONFIG_PATHS, value.clone())),
            None,
            CheckRun::Ran {
                command: format!("printf %s \"${TRUSTED_CONFIG_PATHS}\""),
                outcome: CheckOutcome::Passed,
                output: value,
                duration_ms: 0,
                workspace: WorkspaceDrift::Held,
            },
        )
    );
    // The child's check runs in its copy after the hand-back, with the
    // trust; the close ends it.
    let (units, scope) = whole();
    workspace.hand_back_scoped(&units, &scope).await.unwrap();
    let handed_back = tool_env(&tree);
    workspace.close().await.unwrap();
    assert_eq!(
        (handed_back, tool_env(&tree)),
        (
            Some((
                TRUSTED_CONFIG_PATHS,
                with_host_trust(&tree.join("mise.toml"))
            )),
            None
        )
    );
}

/// A parent that trusts nothing, or no mise to ask, gives the copy no
/// trust.
#[tokio::test]
async fn a_copy_of_an_untrusted_or_unasked_parent_trusts_nothing() {
    let dir = tempfile::tempdir().unwrap();
    let parent = dir.path().join("parent").join("sub");
    write(&parent, "mise.toml", "[tools]\n");
    let mise = fake_mise(dir.path());
    let untrusted = ChildWorkspace::at(dir.path().join("untrusted"));
    untrusted
        .create_asking(&parent, &[], mise.as_os_str())
        .await
        .unwrap();
    let unasked = ChildWorkspace::at(dir.path().join("unasked"));
    unasked
        .create_asking(&parent, &[], dir.path().join("no-mise").as_os_str())
        .await
        .unwrap();
    assert_eq!(
        (tool_env(&untrusted.tree()), tool_env(&unasked.tree())),
        (None, None)
    );
}
