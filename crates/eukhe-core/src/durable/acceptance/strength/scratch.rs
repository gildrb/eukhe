//! A scratch copy of the workspace: the breaks are made and the check is
//! run there, never in the user's workspace. It holds the files git tracks
//! and the untracked ones it does not ignore, plus the dependency stores a
//! check reads (`node_modules`, a virtualenv); build output (`target`) is
//! left out and rebuilt in the copy, and `.git` is not copied. A copy uses
//! the file system's clone where it has one. The copy is removed when it
//! is dropped.

use std::io;
use std::path::{Path, PathBuf};

use super::super::workspace::git;

/// Ignored directories a check reads: dependency stores, copied whole.
const DEPENDENCY_DIRS: &[&str] = &["node_modules", ".venv", "venv"];
/// Directories a non-git copy leaves out.
const SKIPPED_DIRS: &[&str] = &[".git", "target", "__pycache__"];

/// A scratch copy of a workspace, removed on drop.
#[derive(Debug)]
pub(crate) struct Scratch {
    root: PathBuf,
}

impl Scratch {
    pub(crate) fn root(&self) -> &Path {
        &self.root
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        // Best effort: a copy left behind is temp-dir garbage, never the
        // user's files.
        drop(std::fs::remove_dir_all(&self.root));
    }
}

/// Copy `workspace` into a new scratch directory.
///
/// # Errors
///
/// The scratch directory or a file could not be written.
pub(crate) fn copy(workspace: &Path) -> io::Result<Scratch> {
    let root =
        std::env::temp_dir().join(format!("eukhe-strength-{}", uuid::Uuid::new_v4().simple()));
    std::fs::create_dir_all(&root)?;
    let scratch = Scratch { root };
    match git(workspace, &["ls-files", "-co", "--exclude-standard", "-z"]) {
        Some(listed) => {
            for path in listed
                .split(|byte| *byte == 0)
                .filter(|path| !path.is_empty())
            {
                let relative = PathBuf::from(String::from_utf8_lossy(path).into_owned());
                copy_entry(&workspace.join(&relative), &scratch.root.join(&relative))?;
            }
            for dir in DEPENDENCY_DIRS {
                let source = workspace.join(dir);
                if source.is_dir() {
                    copy_tree(&source, &scratch.root.join(dir), &[])?;
                }
            }
        }
        None => copy_tree(workspace, &scratch.root, SKIPPED_DIRS)?,
    }
    Ok(scratch)
}

/// Copy one file or symlink (a deleted tracked file is skipped).
fn copy_entry(source: &Path, target: &Path) -> io::Result<()> {
    let Ok(meta) = std::fs::symlink_metadata(source) else {
        return Ok(());
    };
    if let Some(parent) = target.parent() {
        std::fs::create_dir_all(parent)?;
    }
    if meta.file_type().is_symlink() {
        let link = std::fs::read_link(source)?;
        return symlink(&link, target);
    }
    if meta.is_dir() {
        // A submodule's directory: copied whole.
        return copy_tree(source, target, SKIPPED_DIRS);
    }
    std::fs::copy(source, target).map(drop)
}

/// Copy the tree at `source` to `target`, leaving out `skipped` names.
fn copy_tree(source: &Path, target: &Path, skipped: &[&str]) -> io::Result<()> {
    std::fs::create_dir_all(target)?;
    for entry in std::fs::read_dir(source)? {
        let entry = entry?;
        let name = entry.file_name();
        if skipped.iter().any(|skip| name == *skip) {
            continue;
        }
        let from = entry.path();
        let to = target.join(&name);
        let kind = entry.file_type()?;
        if kind.is_symlink() {
            symlink(&std::fs::read_link(&from)?, &to)?;
        } else if kind.is_dir() {
            copy_tree(&from, &to, skipped)?;
        } else {
            std::fs::copy(&from, &to)?;
        }
    }
    Ok(())
}

#[cfg(unix)]
fn symlink(link: &Path, at: &Path) -> io::Result<()> {
    std::os::unix::fs::symlink(link, at)
}

#[cfg(windows)]
fn symlink(link: &Path, at: &Path) -> io::Result<()> {
    std::os::windows::fs::symlink_file(link, at)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_scratch_copy_holds_the_sources_and_the_dependencies_and_goes_away() {
        let dir = tempfile::tempdir().expect("dir");
        let root = dir.path();
        let git_in = |args: &[&str]| {
            assert!(std::process::Command::new("git")
                .args(args)
                .current_dir(root)
                .status()
                .expect("git")
                .success());
        };
        git_in(&["init", "-q"]);
        std::fs::write(root.join(".gitignore"), "target/\nnode_modules/\n").expect("write");
        std::fs::create_dir_all(root.join("src")).expect("dir");
        std::fs::write(root.join("src/a.py"), "x = 1\n").expect("write");
        std::fs::create_dir_all(root.join("target")).expect("dir");
        std::fs::write(root.join("target/big.bin"), "build").expect("write");
        std::fs::create_dir_all(root.join("node_modules/dep")).expect("dir");
        std::fs::write(root.join("node_modules/dep/index.js"), "1").expect("write");
        let scratch = copy(root).expect("copy");
        let copied = scratch.root().to_path_buf();
        assert_eq!(
            (
                std::fs::read_to_string(copied.join("src/a.py")).ok(),
                std::fs::read_to_string(copied.join("node_modules/dep/index.js")).ok(),
                copied.join("target").exists(),
                copied.join(".git").exists(),
            ),
            (
                Some("x = 1\n".to_owned()),
                Some("1".to_owned()),
                false,
                false
            )
        );
        drop(scratch);
        assert!(!copied.exists());
    }
}
