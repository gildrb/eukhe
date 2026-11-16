//! The child's git view of its own work: a repository of its own in its
//! copy, made when the child first runs git there. Its index and its one
//! commit are `base/`, the copy as the child found it, so `git status`
//! and `git diff` show the child's changes since its start, whatever it
//! changed before its first git. The repository starts empty (no
//! template, no hooks) and takes nothing from the parent's: no history,
//! branch, remote or object store. Its objects are the base's files,
//! compressed once.
//!
//! The base commit is written as an object: `git status` compares the
//! index with `HEAD`, and without a commit every path reads as a new
//! staged file. Its author and committer are fixed text with time 0; no
//! identity is read from or set in the environment or the configuration.

use std::io;
use std::path::{Path, PathBuf};
use std::process::Stdio;

use anyhow::Context as _;

use crate::workspace_snapshot::git::git_command;

/// The base commit's object, after its `tree` line.
const BASE_COMMIT: &str = "author eukhe <eukhe@localhost> 0 +0000\n\
                           committer eukhe <eukhe@localhost> 0 +0000\n\
                           \n\
                           The workspace at the child's start\n";

/// No automatic garbage collection or maintenance: a background run
/// would outlive the build of the repository and its rename.
const NO_UPKEEP: [&str; 4] = ["-c", "gc.auto=0", "-c", "maintenance.auto=false"];

/// What asking for the view found or did.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GitView {
    /// The copy is a repository already.
    Present,
    /// The copy became a repository with the base commit.
    Made,
    /// No `git` program to run: the copy stays without a view.
    NoGit,
}

/// How one git step ended.
enum Step {
    /// It succeeded: its standard output, trimmed.
    Ran(String),
    NoGit,
}

/// Make `tree` (the child's copy) a repository whose index and commit
/// are `base`, built beside them under `root` and renamed into `tree` in
/// one step; a repository already in `tree` stays.
///
/// # Errors
///
/// A git step cannot start (other than a missing `git`) or fails, or the
/// repository cannot be renamed into place.
#[tracing::instrument(level = "debug")]
pub(super) async fn make(root: &Path, base: &Path, tree: &Path) -> anyhow::Result<GitView> {
    let target = tree.join(".git");
    if tokio::fs::symlink_metadata(&target).await.is_ok() {
        return Ok(GitView::Present);
    }
    let staging = root.join(format!("git.staging-{}", uuid::Uuid::new_v4().simple()));
    let view = match build(&staging, base).await {
        Ok(Some(git_dir)) => match tokio::fs::rename(&git_dir, &target).await {
            Ok(()) => Ok(GitView::Made),
            // Another git step of the child made it first.
            Err(_) if tokio::fs::symlink_metadata(&target).await.is_ok() => Ok(GitView::Present),
            Err(error) => Err(error.into()),
        },
        Ok(None) => Ok(GitView::NoGit),
        Err(error) => Err(error),
    };
    match tokio::fs::remove_dir_all(&staging).await {
        Err(error) if error.kind() != io::ErrorKind::NotFound => {
            tracing::warn!(%error, staging = %staging.display(), "cannot remove a git staging dir");
        }
        Ok(()) | Err(_) => {}
    }
    view
}

/// Build the repository in `staging`: an empty one, the base added to
/// its index, the base commit as `HEAD`. Its git dir; `None` when there
/// is no `git`.
async fn build(staging: &Path, base: &Path) -> anyhow::Result<Option<PathBuf>> {
    let git_dir = staging.join(".git");
    let commit = staging.join("base-commit");
    let [staging_arg, git_dir_arg, base_arg, commit_arg] =
        [staging, git_dir.as_path(), base, commit.as_path()].map(|path| {
            path.to_str()
                .with_context(|| format!("{} is not UTF-8", path.display()))
        });
    let (at, work_tree) = (
        format!("--git-dir={}", git_dir_arg?),
        format!("--work-tree={}", base_arg?),
    );
    let Step::Ran(_) = git(&["init", "--quiet", "--template=", staging_arg?], base).await? else {
        return Ok(None);
    };
    let Step::Ran(_) = git(&[&at, &work_tree, "add", "--all"], base).await? else {
        return Ok(None);
    };
    let Step::Ran(tree_id) = git(&[&at, "write-tree"], base).await? else {
        return Ok(None);
    };
    tokio::fs::write(&commit, format!("tree {tree_id}\n{BASE_COMMIT}")).await?;
    let hash = [&at, "hash-object", "-t", "commit", "-w", commit_arg?];
    let Step::Ran(commit_id) = git(&hash, base).await? else {
        return Ok(None);
    };
    let Step::Ran(_) = git(&[&at, "update-ref", "HEAD", &commit_id], base).await? else {
        return Ok(None);
    };
    Ok(Some(git_dir))
}

/// Run `git args` in `cwd`, without automatic upkeep.
async fn git(args: &[&str], cwd: &Path) -> anyhow::Result<Step> {
    let args: Vec<&str> = NO_UPKEEP.iter().chain(args).copied().collect();
    let output = git_command(&args, cwd).stdin(Stdio::null()).output().await;
    match output {
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(Step::NoGit),
        Err(error) => Err(error.into()),
        Ok(output) if output.status.success() => Ok(Step::Ran(
            String::from_utf8_lossy(&output.stdout).trim().to_owned(),
        )),
        Ok(output) => anyhow::bail!(
            "git {} in {}: {}",
            args.join(" "),
            cwd.display(),
            String::from_utf8_lossy(&output.stderr).trim()
        ),
    }
}
