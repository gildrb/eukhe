//! The child's git view of its own work: a repository of its own in its
//! copy, made at the spawn, whose one commit is the copy as the child
//! found it. `git status` and `git diff` in the copy show the child's
//! changes only. The repository starts empty (no template, no hooks) and
//! takes nothing from the parent's: no history, branch, remote or object
//! store, so the parent's `.git` stays out of the child's reach. Its
//! objects are the copy's files, compressed once.

use std::io;
use std::path::Path;
use std::process::Stdio;

use crate::workspace_snapshot::git::git_command;

/// The message of the base commit.
const BASE_MESSAGE: &str = "The workspace at the child's start";

/// The author and committer of the base commit.
const IDENTITY: [(&str, &str); 4] = [
    ("GIT_AUTHOR_NAME", "eukhe"),
    ("GIT_AUTHOR_EMAIL", "eukhe@localhost"),
    ("GIT_COMMITTER_NAME", "eukhe"),
    ("GIT_COMMITTER_EMAIL", "eukhe@localhost"),
];

/// No automatic garbage collection or maintenance: a background run
/// would outlive the create and its rename of the copy.
const NO_UPKEEP: [&str; 4] = ["-c", "gc.auto=0", "-c", "maintenance.auto=false"];

/// The steps that make the view: an empty repository, the copy added,
/// the base commit.
const STEPS: [&[&str]; 3] = [
    &["init", "--quiet", "--template="],
    &["add", "--all"],
    &[
        "commit",
        "--quiet",
        "--no-verify",
        "--no-gpg-sign",
        "--allow-empty",
        "--message",
        BASE_MESSAGE,
    ],
];

/// What making the view did.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum GitView {
    /// The copy is a repository with the base commit.
    Made,
    /// No `git` program to run: the copy stays without a view.
    NoGit,
}

/// Make the copy at `tree` a repository of its own whose one commit is
/// the copy.
///
/// # Errors
///
/// A git step cannot start (other than a missing `git`) or fails.
#[tracing::instrument(level = "debug")]
pub(super) async fn make(tree: &Path) -> anyhow::Result<GitView> {
    for step in STEPS {
        let args: Vec<&str> = NO_UPKEEP.iter().chain(step).copied().collect();
        let output = git_command(&args, tree)
            .envs(IDENTITY)
            .stdin(Stdio::null())
            .output()
            .await;
        match output {
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(GitView::NoGit),
            Err(error) => return Err(error.into()),
            Ok(output) if output.status.success() => {}
            Ok(output) => anyhow::bail!(
                "git {} in {}: {}",
                step.join(" "),
                tree.display(),
                String::from_utf8_lossy(&output.stderr).trim()
            ),
        }
    }
    Ok(GitView::Made)
}
