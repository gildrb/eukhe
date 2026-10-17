//! Copy-on-write child workspaces (docs/runtime.md S3; model
//! `bend/sandbox.bend`, `back`).
//!
//! An isolated child works on its own copy of its parent's workspace. At
//! its spawn the host copies the parent's tracked and untracked, not
//! ignored files twice under the workspace root: `base/` (the workspace
//! as the child found it) and `tree/` (the child's working directory).
//! Each copy clones the file's extents where the filesystem can (btrfs,
//! XFS, APFS); elsewhere it copies the bytes and logs that it did.
//!
//! At the child's end the host takes the child's changes back into the
//! parent's workspace, path by path, with [`merge::merge1`]: a path the
//! child did not change keeps the parent's content; a path only the child
//! changed gets the child's; a path both changed to the same content keeps
//! it; a path both changed differently keeps the parent's and is a
//! conflict, and the child's version stays under `conflicts/`.
//!
//! Each path is replaced in one rename, and the hand-back is idempotent: a
//! path already taken reads as changed by both to the same content, so a
//! hand-back a crash cut runs again from the start to the same result.
//! Only its record (`handback.json`) ends it; then `base/` and the copy go,
//! and `tree/` becomes a symlink to the parent's workspace, so a child
//! woken later works there.

use std::collections::BTreeSet;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

mod files;
mod merge;

#[cfg(test)]
mod bridge;
#[cfg(test)]
mod tests;

use files::{Copied, Listing};

const MANIFEST: &str = "manifest.json";
const HANDBACK: &str = "handback.json";
const BASE: &str = "base";
const TREE: &str = "tree";
const CONFLICTS: &str = "conflicts";
/// The most paths an isolated workspace copies: a parent working in a
/// home directory without git must not clone it whole.
pub const MAX_WORKSPACE_FILES: usize = 100_000;

/// Where a spawned child works.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum WorkspaceMode {
    /// In its parent's working directory, as its parent does.
    #[default]
    Shared,
    /// In its own copy of its parent's workspace, handed back at its end.
    Isolated,
}

/// How the copies of a workspace were made.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CopyReport {
    /// The parent's paths copied.
    pub files: u64,
    /// Copies that copied no data (extent clones and symlinks).
    pub cloned: u64,
    /// Copies of the bytes, where the filesystem could not clone.
    pub copied: u64,
}

/// What a hand-back did.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Handback {
    /// The paths the child changed whose content the parent's workspace
    /// now has.
    pub taken: Vec<String>,
    /// The paths both changed differently: the parent's content stayed.
    pub conflicts: Vec<String>,
    /// The directory that keeps the child's versions of the conflicts;
    /// `None` without conflicts.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub kept: Option<String>,
}

impl Handback {
    /// The hand-back as the parent reads it.
    #[must_use]
    pub fn text(&self) -> String {
        use std::fmt::Write as _;
        let taken = if self.taken.is_empty() {
            "none".to_owned()
        } else {
            self.taken.join(", ")
        };
        let mut text = format!("Workspace hand-back: took the child's changes to {taken}.");
        if !self.conflicts.is_empty() {
            let _ = write!(
                text,
                " Conflicts (both changed; the parent's content stays): {}.",
                self.conflicts.join(", ")
            );
            if let Some(kept) = &self.kept {
                let _ = write!(text, " The child's versions are in {kept}.");
            }
        }
        text
    }
}

/// The record of a workspace, written when its copies are complete.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
struct Manifest {
    /// The parent's workspace.
    parent: PathBuf,
    copy: CopyReport,
}

/// One child's workspace, under its root directory.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChildWorkspace {
    root: PathBuf,
}

impl ChildWorkspace {
    #[must_use]
    pub fn at(root: PathBuf) -> Self {
        Self { root }
    }

    #[must_use]
    pub fn root(&self) -> &Path {
        &self.root
    }

    /// The child's working directory.
    #[must_use]
    pub fn tree(&self) -> PathBuf {
        self.root.join(TREE)
    }

    /// The copies are complete (a hand-back may have ended them since).
    #[must_use]
    pub fn is_created(&self) -> bool {
        self.root.join(MANIFEST).is_file()
    }

    /// The hand-back wrote its record: the child's changes are back.
    #[must_use]
    pub fn is_handed_back(&self) -> bool {
        self.root.join(HANDBACK).is_file()
    }

    /// Copy `parent`'s workspace into `base/` and `tree/`. Idempotent: a
    /// workspace already created is kept, a create a crash cut starts
    /// over.
    ///
    /// # Errors
    ///
    /// The parent's workspace has more than [`MAX_WORKSPACE_FILES`]
    /// paths, or a path cannot be listed, read or copied.
    #[tracing::instrument(skip(self), fields(root = %self.root.display()))]
    pub async fn create(&self, parent: &Path) -> anyhow::Result<CopyReport> {
        if let Some(manifest) = read_json::<Manifest>(&self.root.join(MANIFEST))? {
            return Ok(manifest.copy);
        }
        let paths = files::parent_paths(parent).await?;
        if paths.len() > MAX_WORKSPACE_FILES {
            anyhow::bail!(
                "{} holds {} files, more than an isolated workspace copies ({MAX_WORKSPACE_FILES}); \
                 spawn the child with workspace=\"shared\"",
                parent.display(),
                paths.len()
            );
        }
        let (root, parent) = (self.root.clone(), parent.to_path_buf());
        let report = tokio::task::spawn_blocking(move || copy_in(&root, &parent, &paths)).await??;
        if report.copied > 0 {
            tracing::warn!(
                root = %self.root.display(),
                files = report.files,
                cloned = report.cloned,
                copied = report.copied,
                "the filesystem cannot clone extents here: the child workspace is a plain copy"
            );
        } else {
            tracing::info!(
                root = %self.root.display(),
                files = report.files,
                "child workspace cloned"
            );
        }
        Ok(report)
    }

    /// Take the child's changes back into the parent's workspace; see the
    /// module doc. Idempotent and resumable.
    ///
    /// # Errors
    ///
    /// The workspace has no manifest, or a path cannot be read or
    /// replaced (the hand-back can run again).
    #[tracing::instrument(skip(self), fields(root = %self.root.display()))]
    pub async fn hand_back(&self) -> anyhow::Result<Handback> {
        let root = self.root.clone();
        tokio::task::spawn_blocking(move || hand_back_at(&root)).await?
    }

    /// Remove the workspace and everything under it.
    ///
    /// # Errors
    ///
    /// The root exists and cannot be removed.
    #[tracing::instrument(skip(self), fields(root = %self.root.display()))]
    pub async fn remove(&self) -> anyhow::Result<()> {
        let root = self.root.clone();
        tokio::task::spawn_blocking(move || match fs::remove_dir_all(&root) {
            Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
            removed => removed,
        })
        .await??;
        Ok(())
    }
}

/// `path`'s JSON value; `None` when there is no file.
fn read_json<T: serde::de::DeserializeOwned>(path: &Path) -> anyhow::Result<Option<T>> {
    match fs::read(path) {
        Ok(bytes) => Ok(Some(serde_json::from_slice(&bytes)?)),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(error) => Err(error.into()),
    }
}

/// Write `value` to `path` in one rename, synced.
fn write_json<T: Serialize>(path: &Path, value: &T) -> anyhow::Result<()> {
    let staged = path.with_extension("json.staged");
    let file = fs::File::create(&staged)?;
    serde_json::to_writer_pretty(&file, value)?;
    file.sync_all()?;
    fs::rename(&staged, path)?;
    if let Some(dir) = path.parent() {
        fs::File::open(dir)?.sync_all()?;
    }
    Ok(())
}

/// Copy `paths` of `parent` into a staging directory beside `root`, then
/// rename it to `root`: a workspace exists whole or not at all.
fn copy_in(root: &Path, parent: &Path, paths: &BTreeSet<PathBuf>) -> anyhow::Result<CopyReport> {
    let mut staging = root.as_os_str().to_os_string();
    staging.push(".staging");
    let staging = PathBuf::from(staging);
    for dir in [root, staging.as_path()] {
        match fs::remove_dir_all(dir) {
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            removed => removed?,
        }
    }
    fs::create_dir_all(staging.join(BASE))?;
    fs::create_dir_all(staging.join(TREE))?;
    let mut report = CopyReport {
        files: 0,
        cloned: 0,
        copied: 0,
    };
    for path in paths {
        let base = staging.join(BASE).join(path);
        // The child's copy clones the base, not the parent: when the
        // parent sits on another filesystem only the base is a plain copy.
        let copies = [
            (parent.join(path), base.clone()),
            (base, staging.join(TREE).join(path)),
        ];
        for (from, to) in copies {
            match files::copy_entry(&from, &to)? {
                Copied::Cloned => report.cloned += 1,
                Copied::Plain => report.copied += 1,
                // Gone since the listing, or a directory (a submodule).
                Copied::Skipped => break,
            }
        }
    }
    report.files = files::walk(&staging.join(BASE), Listing::All)?.len() as u64;
    write_json(
        &staging.join(MANIFEST),
        &Manifest {
            parent: parent.to_path_buf(),
            copy: report,
        },
    )?;
    fs::rename(&staging, root)?;
    Ok(report)
}

/// The hand-back of the workspace at `root`.
fn hand_back_at(root: &Path) -> anyhow::Result<Handback> {
    let Some(manifest) = read_json::<Manifest>(&root.join(MANIFEST))? else {
        anyhow::bail!(
            "{} is not a child workspace (no {MANIFEST})",
            root.display()
        );
    };
    let parent = manifest.parent;
    if let Some(done) = read_json::<Handback>(&root.join(HANDBACK))? {
        finish(root, &parent)?;
        return Ok(done);
    }
    let (base, tree) = (root.join(BASE), root.join(TREE));
    // Every path of the base (ignored or not: the child may not drop a
    // path a .gitignore of its own hides) and every path of the child's
    // copy its .gitignore files do not ignore (its build output stays).
    let mut paths = files::walk(&base, Listing::All)?;
    paths.extend(files::walk(&tree, Listing::NotIgnored)?);
    let mut handback = Handback {
        taken: Vec::new(),
        conflicts: Vec::new(),
        kept: None,
    };
    for path in &paths {
        let ours = files::content(&parent.join(path))?;
        let found = files::content(&base.join(path))?;
        let theirs = files::content(&tree.join(path))?;
        let one = merge::merge1(ours.as_ref(), found.as_ref(), theirs.as_ref());
        let name = path.to_string_lossy().into_owned();
        // A path whose place in the parent cannot take the child's file
        // (a directory there, or a file or symlink where one of its
        // directories goes) is a conflict too: the parent's entry stays.
        let blocked = || -> io::Result<bool> {
            if fs::symlink_metadata(parent.join(path)).is_ok_and(|meta| meta.is_dir()) {
                return Ok(true);
            }
            for dir in path.ancestors().skip(1) {
                if dir.as_os_str().is_empty() {
                    continue;
                }
                match fs::symlink_metadata(parent.join(dir)) {
                    Ok(meta) if !meta.is_dir() => return Ok(true),
                    Ok(_) => {}
                    Err(error) if error.kind() == io::ErrorKind::NotFound => {}
                    Err(error) => return Err(error),
                }
            }
            Ok(false)
        };
        if one.clash || (one.body != ours && one.body.is_some() && blocked()?) {
            files::replace(&tree.join(path), &root.join(CONFLICTS).join(path))?;
            handback.conflicts.push(name);
            continue;
        }
        if one.body != ours {
            files::replace(&tree.join(path), &parent.join(path))?;
        }
        if one.body == theirs && theirs != found {
            handback.taken.push(name);
        }
    }
    if !handback.conflicts.is_empty() {
        handback.kept = Some(root.join(CONFLICTS).to_string_lossy().into_owned());
    }
    write_json(&root.join(HANDBACK), &handback)?;
    finish(root, &parent)?;
    Ok(handback)
}

/// End a handed-back workspace: drop the base and the child's copy, and
/// leave `tree` a symlink to the parent's workspace. Idempotent.
fn finish(root: &Path, parent: &Path) -> io::Result<()> {
    let tree = root.join(TREE);
    for dir in [root.join(BASE), tree.clone()] {
        match fs::symlink_metadata(&dir) {
            Ok(meta) if meta.file_type().is_dir() => fs::remove_dir_all(&dir)?,
            Ok(_) => {}
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error),
        }
    }
    match fs::symlink_metadata(&tree) {
        Ok(_) => Ok(()),
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            std::os::unix::fs::symlink(parent, &tree)
        }
        Err(error) => Err(error),
    }
}
