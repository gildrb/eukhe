//! Copy-on-write child workspaces (S3; model
//! `bend/sandbox.bend`, `back`, and its per-path `plan`) and the hand-back
//! of an agent tree's writing child by its scope (`bend/agent_tree.bend`,
//! `overlay`).
//!
//! An isolated child works on its own copy of its parent's workspace. At
//! its spawn the host copies the parent's tracked and untracked, not
//! ignored files twice under the workspace root: `base/` (the workspace
//! as the child found it) and `tree/` (the child's working directory).
//! Each copy clones the file's extents where the filesystem can (btrfs,
//! XFS, APFS); elsewhere it copies the bytes and logs that it did.
//!
//! At the child's end the host takes the child's changes back into the
//! parent's workspace by the child's scope
//! ([`ChildWorkspace::hand_back_scoped`]):
//! - the child's patch: per unit ([`unit_of`]), whether the child added,
//!   modified or removed a file in it (its copy against `base/`);
//! - the core's `overlay` of that patch by the child's scope: a changed
//!   path in a unit outside the scope, or in no unit, is never applied; the
//!   child's version stays under `conflicts/`;
//! - each path inside the scope takes the plan of its parent, base and
//!   child contents ([`merge::plan`]): a path only the child changed gets
//!   the child's content; a path both changed to the same content keeps
//!   it; a path both changed differently keeps the parent's and is a
//!   conflict, the child's version under `conflicts/`.
//!
//! The child's copy is a git repository of its own (`tree/.git`, made at
//! the spawn; [`git_view`]): its one commit is the workspace as the child
//! found it, so `git status` and `git diff` there show the child's changes
//! only. It holds no history, branch or remote of the parent's
//! repository, and the patch never carries a `.git` path
//! ([`files::walk`]).
//!
//! Each path is replaced in one rename, and the hand-back is idempotent: a
//! path already taken reads as changed by both to the same content, so a
//! hand-back a crash cut runs again from the start to the same result.
//! Only its record (`handback.json`) ends it. The copies stay, so the
//! child's check runs in its checkout after the integration, until
//! [`ChildWorkspace::close`]: then `base/`, the copy and its repository
//! go, and `tree/` becomes a symlink to the parent's workspace, so a child
//! woken later works there.
//!
//! The copy keeps the parent's tool trust ([`trust`]): the mise config
//! files the parent's workspace trusts are trusted in the copy too,
//! through the environment of the child's commands ([`tool_env`]).

use std::collections::BTreeSet;
use std::ffi::OsStr;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use eukhe_bend::rules::agent_tree::{self, Patch};
use serde::{Deserialize, Serialize};

mod check;
mod files;
mod git_view;
mod merge;
mod stamp;
mod trust;
mod units;

#[cfg(test)]
mod tests;

pub(crate) use check::PROGRESS_EVERY;
pub use check::{run_check, CheckConfig, CheckReport, CheckRun};
pub use eukhe_types::daemon::agent_tree::CheckOutcome;
pub(crate) use stamp::TreeStamp;
pub use stamp::WorkspaceDrift;
pub use units::{unit_of, unit_patch};

use files::{Copied, Listing};
use git_view::GitView;
use merge::Plan;

const MANIFEST: &str = "manifest.json";
const HANDBACK: &str = "handback.json";
const BASE: &str = "base";
const TREE: &str = "tree";
const CONFLICTS: &str = "conflicts";
/// The most paths an isolated workspace copies: a parent working in a
/// home directory without git must not clone it whole.
pub const MAX_WORKSPACE_FILES: usize = 100_000;

/// The variable a command run in `dir` gets so mise trusts there what the
/// parent's workspace trusts, when `dir` is a child's live copy (the
/// `tree/` of a created workspace not yet closed): its name
/// (`MISE_TRUSTED_CONFIG_PATHS`) and value (the copy's trusted config
/// files, then the host's own value). `None` anywhere else, and for a copy
/// whose parent trusts no mise config.
#[must_use]
pub fn tool_env(dir: &Path) -> Option<(&'static str, String)> {
    let root = dir
        .parent()
        .filter(|_| dir.file_name() == Some(OsStr::new(TREE)))?;
    if !fs::symlink_metadata(dir).is_ok_and(|meta| meta.is_dir()) {
        return None;
    }
    let manifest = read_json::<Manifest>(&root.join(MANIFEST)).ok()??;
    let inherited = std::env::var_os(trust::TRUSTED_CONFIG_PATHS);
    trust::trusted_value(&manifest.trusted, inherited.as_deref())
        .map(|value| (trust::TRUSTED_CONFIG_PATHS, value))
}

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

/// What a scoped hand-back did.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ScopedHandback {
    /// The paths the child changed whose content the parent's workspace
    /// now has.
    pub taken: Vec<String>,
    /// The paths the child changed outside its scope: never applied.
    pub outside: Vec<String>,
    /// The paths in the child's scope both changed differently (or whose
    /// place in the parent is blocked): the parent's content stayed.
    pub conflicts: Vec<String>,
    /// The directory that keeps the child's versions of `outside` and
    /// `conflicts`; `None` when both are empty.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub kept: Option<String>,
    /// The child's patch per unit (`Some(1)`: changed), for the crown's
    /// `Finish` event.
    pub patch: Patch,
}

impl ScopedHandback {
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
        if !self.outside.is_empty() {
            let _ = write!(
                text,
                " Outside the child's scope (not applied): {}.",
                self.outside.join(", ")
            );
        }
        if !self.conflicts.is_empty() {
            let _ = write!(
                text,
                " Conflicts (both changed; the parent's content stays): {}.",
                self.conflicts.join(", ")
            );
        }
        if let Some(kept) = &self.kept {
            let _ = write!(text, " The child's versions are in {kept}.");
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
    /// The copy's mise config files whose originals the parent trusts.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    trusted: Vec<PathBuf>,
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

    /// The hand-back wrote its record: the child's changes are back (its
    /// copies stay until [`Self::close`]).
    #[must_use]
    pub fn is_handed_back(&self) -> bool {
        self.root.join(HANDBACK).is_file()
    }

    /// The child's copies are there: created, and not closed.
    #[must_use]
    pub fn has_copies(&self) -> bool {
        self.is_created() && self.root.join(BASE).is_dir()
    }

    /// Copy `parent`'s workspace into `base/` and `tree/`, and make
    /// `tree/` a git repository of its own whose one commit is the copy
    /// ([`git_view`]). Idempotent: a workspace already created is kept, a
    /// create a crash cut starts over.
    ///
    /// # Errors
    ///
    /// The parent's workspace has more than [`MAX_WORKSPACE_FILES`]
    /// paths, a path cannot be listed, read or copied, or git fails on
    /// the copy.
    #[tracing::instrument(skip(self), fields(root = %self.root.display()))]
    pub async fn create(&self, parent: &Path) -> anyhow::Result<CopyReport> {
        self.create_asking(parent, OsStr::new(trust::MISE)).await
    }

    /// [`Self::create`], asking `mise` (the program) for the parent's
    /// trust.
    async fn create_asking(&self, parent: &Path, mise: &OsStr) -> anyhow::Result<CopyReport> {
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
        let trusted = trust::carried(mise, parent, &self.tree(), &paths).await;
        let staging = staging_of(&self.root);
        let report = {
            let (root, staging, parent) =
                (self.root.clone(), staging.clone(), parent.to_path_buf());
            tokio::task::spawn_blocking(move || copy_in(&root, &staging, &parent, &paths)).await??
        };
        match git_view::make(&staging.join(TREE)).await? {
            GitView::Made => {}
            GitView::NoGit => tracing::warn!(
                root = %self.root.display(),
                "no git to run: the child workspace has no git view of the child's changes"
            ),
        }
        let manifest = Manifest {
            parent: parent.to_path_buf(),
            copy: report,
            trusted,
        };
        let root = self.root.clone();
        tokio::task::spawn_blocking(move || seal(&staging, &root, &manifest)).await??;
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

    /// The paths the child added, modified or removed since its start,
    /// relative to the workspace (the files its check covers).
    ///
    /// # Errors
    ///
    /// The workspace has no copies (not created, or closed), or a path
    /// cannot be read.
    #[tracing::instrument(skip(self), fields(root = %self.root.display()))]
    pub async fn changed(&self) -> anyhow::Result<Vec<PathBuf>> {
        if !self.has_copies() {
            anyhow::bail!("{} holds no child copy", self.root.display());
        }
        let root = self.root.clone();
        Ok(
            tokio::task::spawn_blocking(move || changes(&root.join(BASE), &root.join(TREE)))
                .await??,
        )
    }

    /// Take the child's changes inside `scope` (a mask over `units`) back
    /// into the parent's workspace; see the module doc. Idempotent and
    /// resumable; the copies stay until [`Self::close`].
    ///
    /// # Errors
    ///
    /// `scope` and `units` differ in length, the workspace has no
    /// manifest, or a path cannot be read or replaced (the hand-back can
    /// run again).
    #[tracing::instrument(skip(self, units, scope), fields(root = %self.root.display()))]
    pub async fn hand_back_scoped(
        &self,
        units: &[String],
        scope: &[bool],
    ) -> anyhow::Result<ScopedHandback> {
        let (root, units, scope) = (self.root.clone(), units.to_vec(), scope.to_vec());
        tokio::task::spawn_blocking(move || hand_back_at(&root, &units, &scope)).await?
    }

    /// End a handed-back workspace: drop the base and the child's copy,
    /// and leave `tree/` a symlink to the parent's workspace. Idempotent.
    ///
    /// # Errors
    ///
    /// The hand-back has no record yet, or a copy cannot be removed.
    #[tracing::instrument(skip(self), fields(root = %self.root.display()))]
    pub async fn close(&self) -> anyhow::Result<()> {
        let root = self.root.clone();
        tokio::task::spawn_blocking(move || {
            let Some(manifest) = read_json::<Manifest>(&root.join(MANIFEST))? else {
                anyhow::bail!(
                    "{} is not a child workspace (no {MANIFEST})",
                    root.display()
                );
            };
            if !root.join(HANDBACK).is_file() {
                anyhow::bail!("{} is not handed back (no {HANDBACK})", root.display());
            }
            Ok(finish(&root, &manifest.parent)?)
        })
        .await?
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

/// The directory a create of the workspace at `root` stages its copies
/// in, renamed to `root` when complete: a workspace exists whole or not
/// at all.
fn staging_of(root: &Path) -> PathBuf {
    let mut staging = root.as_os_str().to_os_string();
    staging.push(".staging");
    PathBuf::from(staging)
}

/// Copy `paths` of `parent` into `staging`, after removing what an
/// earlier create a crash cut left at `root` and `staging`.
fn copy_in(
    root: &Path,
    staging: &Path,
    parent: &Path,
    paths: &BTreeSet<PathBuf>,
) -> anyhow::Result<CopyReport> {
    for dir in [root, staging] {
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
    Ok(report)
}

/// Write the manifest of the complete copies in `staging`, then rename
/// `staging` to `root`.
fn seal(staging: &Path, root: &Path, manifest: &Manifest) -> anyhow::Result<()> {
    write_json(&staging.join(MANIFEST), manifest)?;
    fs::rename(staging, root)?;
    Ok(())
}

/// The paths the child added, modified or removed, relative to the
/// workspace: every path of the base (ignored or not: the child may not
/// drop a path a .gitignore of its own hides) and every path of the
/// child's copy its .gitignore files do not ignore (its build output
/// stays), whose content in the copy differs from the base's.
fn changes(base: &Path, tree: &Path) -> io::Result<Vec<PathBuf>> {
    let mut paths = files::walk(base, Listing::All)?;
    paths.extend(files::walk(tree, Listing::NotIgnored)?);
    let mut changed = Vec::new();
    for path in paths {
        if files::content(&base.join(&path))? != files::content(&tree.join(&path))? {
            changed.push(path);
        }
    }
    Ok(changed)
}

/// `path`'s place in `parent` cannot take the child's file: a directory
/// there, or a file or symlink where one of its directories goes.
fn blocked(parent: &Path, path: &Path) -> io::Result<bool> {
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
}

/// The scoped hand-back of the workspace at `root`.
fn hand_back_at(root: &Path, units: &[String], scope: &[bool]) -> anyhow::Result<ScopedHandback> {
    if units.len() != scope.len() {
        anyhow::bail!(
            "a scope of {} entries over {} units",
            scope.len(),
            units.len()
        );
    }
    let Some(manifest) = read_json::<Manifest>(&root.join(MANIFEST))? else {
        anyhow::bail!(
            "{} is not a child workspace (no {MANIFEST})",
            root.display()
        );
    };
    let parent = manifest.parent;
    if let Some(done) = read_json::<ScopedHandback>(&root.join(HANDBACK))? {
        return Ok(done);
    }
    let (base, tree) = (root.join(BASE), root.join(TREE));
    let changed = changes(&base, &tree)?;
    let patch = unit_patch(units, &changed);
    let overlay = agent_tree::overlay(&vec![None; units.len()], &patch, scope);
    let keep = |path: &Path| files::replace(&tree.join(path), &root.join(CONFLICTS).join(path));
    let mut handback = ScopedHandback {
        taken: Vec::new(),
        outside: Vec::new(),
        conflicts: Vec::new(),
        kept: None,
        patch,
    };
    for path in &changed {
        let name = path.to_string_lossy().into_owned();
        let applies = unit_of(units, path)
            .and_then(|unit| overlay.patch.get(unit))
            .is_some_and(Option::is_some);
        if !applies {
            keep(path)?;
            handback.outside.push(name);
            continue;
        }
        let ours = files::content(&parent.join(path))?;
        let found = files::content(&base.join(path))?;
        let theirs = files::content(&tree.join(path))?;
        match merge::plan(ours.as_ref(), found.as_ref(), theirs.as_ref()) {
            Plan::Keep { taken } => {
                if taken {
                    handback.taken.push(name);
                }
            }
            Plan::Clash => {
                keep(path)?;
                handback.conflicts.push(name);
            }
            Plan::Take if blocked(&parent, path)? => {
                keep(path)?;
                handback.conflicts.push(name);
            }
            Plan::Take | Plan::Drop => {
                files::replace(&tree.join(path), &parent.join(path))?;
                handback.taken.push(name);
            }
        }
    }
    if !(handback.outside.is_empty() && handback.conflicts.is_empty()) {
        handback.kept = Some(root.join(CONFLICTS).to_string_lossy().into_owned());
    }
    write_json(&root.join(HANDBACK), &handback)?;
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
