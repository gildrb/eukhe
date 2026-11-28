use std::collections::BTreeMap;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};

use super::*;

/// One entry of a tree: a file's bytes, a symlink's target, a directory;
/// with its mode (a symlink's is the platform's).
#[derive(Debug, PartialEq, Eq)]
enum Entry {
    File(Vec<u8>, u32),
    Link(PathBuf),
    Dir(u32),
}

/// Every entry under `root`, by its path relative to `root`.
fn listing(root: &Path) -> BTreeMap<PathBuf, Entry> {
    let mut entries = BTreeMap::new();
    let mut pending = vec![root.to_path_buf()];
    while let Some(dir) = pending.pop() {
        for entry in fs::read_dir(&dir).unwrap() {
            let path = entry.unwrap().path();
            let meta = fs::symlink_metadata(&path).unwrap();
            let relative = path.strip_prefix(root).unwrap().to_path_buf();
            let mode = meta.permissions().mode() & 0o7777;
            let value = if meta.file_type().is_symlink() {
                Entry::Link(fs::read_link(&path).unwrap())
            } else if meta.is_dir() {
                pending.push(path);
                Entry::Dir(mode)
            } else {
                Entry::File(fs::read(&path).unwrap(), mode)
            };
            entries.insert(relative, value);
        }
    }
    entries
}

/// A child workspace's shape: a private file, a nested directory, a
/// symlink out of the tree, and a read-only directory with a file in it.
fn tree(root: &Path) {
    fs::create_dir_all(root.join("tree/src")).unwrap();
    fs::write(root.join("manifest.json"), "{}").unwrap();
    fs::set_permissions(
        root.join("manifest.json"),
        fs::Permissions::from_mode(0o600),
    )
    .unwrap();
    fs::write(root.join("tree/src/a.rs"), "fn a() {}").unwrap();
    std::os::unix::fs::symlink("/parent/workspace", root.join("link")).unwrap();
    fs::create_dir(root.join("sealed")).unwrap();
    fs::write(root.join("sealed/b.txt"), "b").unwrap();
    fs::set_permissions(root.join("sealed"), fs::Permissions::from_mode(0o500)).unwrap();
}

/// The names in `dir`: a move leaves no staged copy or mark there.
fn names(dir: &Path) -> Vec<String> {
    let mut names: Vec<String> = fs::read_dir(dir)
        .unwrap()
        .map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned())
        .collect();
    names.sort();
    names
}

/// Restore write access, so the temp dir's removal can descend.
fn unseal(root: &Path) {
    let sealed = root.join("sealed");
    if sealed.is_dir() {
        fs::set_permissions(sealed, fs::Permissions::from_mode(0o700)).unwrap();
    }
}

#[test]
fn a_move_renames_the_whole_tree() {
    let dir = tempfile::tempdir().unwrap();
    let (from, to) = (dir.path().join("old/c"), dir.path().join("new/c"));
    tree(&from);
    fs::create_dir(dir.path().join("new")).unwrap();
    let before = listing(&from);
    move_dir(&from, &to).unwrap();
    assert_eq!(
        (listing(&to), from.exists(), names(&dir.path().join("new"))),
        (before, false, vec!["c".to_owned()])
    );
    unseal(&to);
}

#[test]
fn a_copy_keeps_bytes_modes_and_links() {
    let dir = tempfile::tempdir().unwrap();
    let (from, to) = (dir.path().join("from"), dir.path().join("to"));
    tree(&from);
    copy_tree(&from, &to).unwrap();
    assert_eq!(listing(&to), listing(&from));
    unseal(&from);
    unseal(&to);
}

#[test]
fn nothing_at_from_moves_nothing() {
    let dir = tempfile::tempdir().unwrap();
    let to = dir.path().join("to");
    move_dir(&dir.path().join("gone"), &to).unwrap();
    std::os::unix::fs::symlink(&to, dir.path().join("link")).unwrap();
    move_dir(&dir.path().join("link"), &to).unwrap();
    assert_eq!(names(dir.path()), ["link"]);
}

/// A crash after a copying move's rename, before `from` went: the next
/// move removes `from` and the mark, and keeps the copy.
#[test]
fn a_move_cut_after_its_copy_ends_by_removing_the_source() {
    let dir = tempfile::tempdir().unwrap();
    let (from, to) = (dir.path().join("old"), dir.path().join("new"));
    tree(&from);
    copy_tree(&from, &to).unwrap();
    fs::write(dir.path().join("new.moved"), "").unwrap();
    let copied = listing(&to);
    unseal(&from);
    move_dir(&from, &to).unwrap();
    assert_eq!(
        (listing(&to), names(dir.path())),
        (copied, vec!["new".to_owned()])
    );
    unseal(&to);
}

/// A crash inside a copy (no mark), or after a whole copy before its
/// rename (a mark, no `to`): the next move drops the staged copy and moves
/// `from` again.
#[test]
fn a_move_cut_before_its_rename_starts_again() {
    for marked in [false, true] {
        let dir = tempfile::tempdir().unwrap();
        let (from, to) = (dir.path().join("old"), dir.path().join("new"));
        tree(&from);
        fs::create_dir_all(dir.path().join("new.moving/tree")).unwrap();
        if marked {
            fs::write(dir.path().join("new.moved"), "").unwrap();
        }
        let before = listing(&from);
        move_dir(&from, &to).unwrap();
        assert_eq!(
            (listing(&to), names(dir.path())),
            (before, vec!["new".to_owned()])
        );
        unseal(&to);
    }
}

/// Two directories, neither made by a move: both stay, and the move fails.
#[test]
fn a_move_onto_another_directory_removes_nothing() {
    let dir = tempfile::tempdir().unwrap();
    let (from, to) = (dir.path().join("old"), dir.path().join("new"));
    tree(&from);
    fs::create_dir(&to).unwrap();
    fs::write(to.join("own.txt"), "own").unwrap();
    let (before_from, before_to) = (listing(&from), listing(&to));
    let error = move_dir(&from, &to).unwrap_err();
    assert_eq!(
        (error.kind(), listing(&from), listing(&to)),
        (io::ErrorKind::AlreadyExists, before_from, before_to)
    );
    unseal(&from);
}
