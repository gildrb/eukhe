use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use super::{files, ChildWorkspace, Handback, Listing, BASE, CONFLICTS, HANDBACK};

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

fn git(dir: &Path, args: &[&str]) {
    let status = std::process::Command::new("git")
        .args(args)
        .current_dir(dir)
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .status()
        .unwrap();
    assert!(status.success(), "git {args:?}");
}

fn files_of(pairs: &[(&str, &str)]) -> BTreeMap<String, String> {
    pairs
        .iter()
        .map(|(path, text)| ((*path).to_owned(), (*text).to_owned()))
        .collect()
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
    let handback = workspace.hand_back().await.unwrap();
    let kept = workspace.root().join(CONFLICTS);
    assert_eq!(
        (handback, snapshot(&parent), snapshot(&kept)),
        (
            Handback {
                taken: vec![
                    ".gitignore".to_owned(),
                    "a.txt".to_owned(),
                    "gone.txt".to_owned(),
                    "new/d.txt".to_owned(),
                ],
                conflicts: vec!["c.txt".to_owned()],
                kept: Some(kept.to_string_lossy().into_owned()),
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

#[tokio::test]
async fn a_hand_back_cut_by_a_crash_runs_again_to_the_same_result() {
    let dir = tempfile::tempdir().unwrap();
    let make = |name: &str| {
        let parent = dir.path().join(name).join("parent");
        write(&parent, "a.txt", "a0");
        write(&parent, "b.txt", "b0");
        write(&parent, "c.txt", "c0");
        (parent, ChildWorkspace::at(dir.path().join(name).join("ws")))
    };
    let (clean_parent, clean) = make("clean");
    let (cut_parent, cut) = make("cut");
    for (parent, workspace) in [(&clean_parent, &clean), (&cut_parent, &cut)] {
        workspace.create(parent).await.unwrap();
        write(&workspace.tree(), "a.txt", "a-child");
        write(&workspace.tree(), "b.txt", "b-child");
        write(&workspace.tree(), "c.txt", "c-child");
        write(parent, "c.txt", "c-parent");
    }
    // The cut run replaced a.txt, then the process died before its record.
    files::replace(&cut.tree().join("a.txt"), &cut_parent.join("a.txt")).unwrap();
    assert!(!cut.root().join(HANDBACK).exists());
    let clean_back = clean.hand_back().await.unwrap();
    let cut_back = cut.hand_back().await.unwrap();
    // A repeat after the record returns the record.
    let again = cut.hand_back().await.unwrap();
    let relative = |back: Handback, root: &Path| Handback {
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
            again,
        ),
        (
            relative(clean_back, clean.root()),
            snapshot(&clean_parent),
            cut_back,
        )
    );
    assert_eq!(
        snapshot(&clean_parent),
        files_of(&[
            ("a.txt", "a-child"),
            ("b.txt", "b-child"),
            ("c.txt", "c-parent")
        ])
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
    let handback = workspace.hand_back().await.unwrap();
    assert_eq!(
        (handback, snapshot(&parent)),
        (
            Handback {
                taken: vec!["a.txt".to_owned()],
                conflicts: Vec::new(),
                kept: None,
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
    let handback = workspace.hand_back().await.unwrap();
    let kept = workspace.root().join(CONFLICTS);
    assert_eq!(
        (handback, snapshot(&parent), snapshot(&kept)),
        (
            Handback {
                taken: vec!["a.txt".to_owned()],
                conflicts: vec!["p".to_owned(), "q/x".to_owned()],
                kept: Some(kept.to_string_lossy().into_owned()),
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
