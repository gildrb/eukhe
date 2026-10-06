//! Where the session cwd sits in git, for the status line: the checked-out
//! branch and, inside a linked worktree, the project and worktree names.
//! Read from the `.git` files directly (no `git` process), on a background
//! task: the render path only reads the last probe the loop folded in.

use std::path::{Path, PathBuf};
use std::time::Duration;

use tokio::sync::mpsc;

/// How often the background probe re-reads the placement (a branch switch
/// shows within this window).
const REFRESH: Duration = Duration::from_secs(2);

/// The cwd's git placement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GitPlacement {
    /// The checked-out branch, or the short commit id of a detached HEAD.
    pub branch: Option<String>,
    /// Set when the cwd is inside a linked worktree.
    pub worktree: Option<LinkedWorktree>,
}

/// A linked worktree (`git worktree add`): the primary checkout's
/// directory name and the worktree's own directory name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinkedWorktree {
    pub project: String,
    pub name: String,
}

/// Probe the placement of `cwd`: the nearest ancestor holding `.git`.
/// `None` outside a repository or when the git files are unreadable.
#[must_use]
pub fn probe(cwd: &Path) -> Option<GitPlacement> {
    let root = cwd.ancestors().find(|dir| dir.join(".git").exists())?;
    let dot_git = root.join(".git");
    if dot_git.is_dir() {
        return Some(GitPlacement {
            branch: read_branch(&dot_git),
            worktree: None,
        });
    }
    // A `.git` file points at the real git dir: a linked worktree (its
    // git dir names the shared one in `commondir`) or a submodule.
    let pointer = std::fs::read_to_string(&dot_git).ok()?;
    let git_dir = root.join(pointer.strip_prefix("gitdir:")?.trim());
    Some(GitPlacement {
        branch: read_branch(&git_dir),
        worktree: linked_worktree(root, &git_dir),
    })
}

/// The project and worktree names of a linked worktree rooted at `root`.
fn linked_worktree(root: &Path, git_dir: &Path) -> Option<LinkedWorktree> {
    let common = std::fs::read_to_string(git_dir.join("commondir")).ok()?;
    let common = git_dir.join(common.trim());
    let common = std::fs::canonicalize(&common).unwrap_or(common);
    let primary = if common.file_name().is_some_and(|name| name == ".git") {
        common.parent()?
    } else {
        common.as_path()
    };
    let project = primary.file_name()?.to_string_lossy();
    let project = project.strip_suffix(".git").unwrap_or(&project);
    Some(LinkedWorktree {
        project: project.to_string(),
        name: root.file_name()?.to_string_lossy().into_owned(),
    })
}

/// The branch `HEAD` names, or the short id of a detached `HEAD`.
fn read_branch(git_dir: &Path) -> Option<String> {
    let head = std::fs::read_to_string(git_dir.join("HEAD")).ok()?;
    let head = head.trim();
    match head.strip_prefix("ref: ") {
        Some(reference) => Some(
            reference
                .strip_prefix("refs/heads/")
                .unwrap_or(reference)
                .to_string(),
        ),
        None => head.get(..7).map(str::to_string),
    }
}

/// Watch the placement of `cwd` on a background task: every change
/// (the first probe included, when it finds a repository) arrives on the
/// returned channel. The task ends when the receiver drops.
pub(crate) fn watch(cwd: PathBuf) -> mpsc::UnboundedReceiver<Option<GitPlacement>> {
    let (tx, rx) = mpsc::unbounded_channel();
    tokio::spawn(async move {
        let mut last: Option<GitPlacement> = None;
        loop {
            let dir = cwd.clone();
            let Ok(placement) = tokio::task::spawn_blocking(move || probe(&dir)).await else {
                return;
            };
            if placement != last {
                if tx.send(placement.clone()).is_err() {
                    return;
                }
                last = placement;
            }
            tokio::select! {
                () = tokio::time::sleep(REFRESH) => {}
                () = tx.closed() => return,
            }
        }
    });
    rx
}

#[cfg(test)]
mod tests {
    use super::*;

    fn write(path: &Path, text: &str) {
        std::fs::create_dir_all(path.parent().expect("parent")).expect("mkdir");
        std::fs::write(path, text).expect("write");
    }

    #[test]
    fn a_checkout_reports_its_branch_from_any_subdirectory() {
        let temp = tempfile::tempdir().expect("tempdir");
        let repo = temp.path().join("proj");
        write(&repo.join(".git/HEAD"), "ref: refs/heads/main\n");
        let nested = repo.join("src/deep");
        std::fs::create_dir_all(&nested).expect("mkdir");
        assert_eq!(
            probe(&nested),
            Some(GitPlacement {
                branch: Some("main".to_string()),
                worktree: None,
            })
        );
    }

    #[test]
    fn a_detached_head_reports_the_short_commit_id() {
        let temp = tempfile::tempdir().expect("tempdir");
        write(
            &temp.path().join(".git/HEAD"),
            "0123456789abcdef0123456789abcdef01234567\n",
        );
        assert_eq!(
            probe(temp.path()),
            Some(GitPlacement {
                branch: Some("0123456".to_string()),
                worktree: None,
            })
        );
    }

    #[test]
    fn a_linked_worktree_names_its_project_and_itself() {
        let temp = tempfile::tempdir().expect("tempdir");
        let common = temp.path().join("eukhe/.git");
        let git_dir = common.join("worktrees/eukhe-CLI");
        write(&common.join("HEAD"), "ref: refs/heads/main\n");
        write(&git_dir.join("HEAD"), "ref: refs/heads/CLI\n");
        write(&git_dir.join("commondir"), "../..\n");
        let worktree = temp.path().join("eukhe-CLI");
        write(
            &worktree.join(".git"),
            &format!("gitdir: {}\n", git_dir.display()),
        );
        assert_eq!(
            probe(&worktree),
            Some(GitPlacement {
                branch: Some("CLI".to_string()),
                worktree: Some(LinkedWorktree {
                    project: "eukhe".to_string(),
                    name: "eukhe-CLI".to_string(),
                }),
            })
        );
    }

    #[test]
    fn a_directory_outside_any_repository_has_no_placement() {
        let temp = tempfile::tempdir().expect("tempdir");
        assert_eq!(probe(temp.path()), None);
    }
}
