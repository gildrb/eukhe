//! The git-context concern (moved with its concern): the quiet git
//! probes and the header's git-context capture (TS captureGitContext).

use std::process::Stdio;

use super::{GitContext, Path};

/// Capture git context for the header (best effort; None outside a repo).
///
/// Contract (TS `captureGitContext`): every field is independently optional;
/// the context exists when at least one probe succeeds. `branch` is
/// `--show-current`, so a detached HEAD yields no branch. The remote URL is
/// normalized through the git-source parser when it parses, else kept
/// verbatim. The three probes run concurrently.
#[must_use]
pub fn capture_git_context(cwd: &Path) -> Option<GitContext> {
    let probes: [&[&str]; 3] = [
        &["rev-parse", "HEAD"],
        &["branch", "--show-current"],
        &["remote", "get-url", "origin"],
    ];
    // Spawn every probe before waiting on any.
    let children = probes.map(|args| {
        std::process::Command::new("git")
            .arg("--no-optional-locks")
            .args(args)
            .current_dir(cwd)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .ok()
    });
    let [commit, branch, remote] = children.map(|child| {
        child?
            .wait_with_output()
            .ok()
            .filter(|output| output.status.success())
            .and_then(|output| String::from_utf8(output.stdout).ok())
            .map(|stdout| stdout.trim().to_string())
            .filter(|value| !value.is_empty())
    });
    if commit.is_none() && branch.is_none() && remote.is_none() {
        return None;
    }
    Some(GitContext {
        // Display-only normalization: a remote that is not a valid package
        // source is recorded verbatim.
        repo_url: remote.map(|url| match crate::packages::parse_git_url(&url) {
            Ok(Some(source)) => source.repo,
            Ok(None) | Err(_) => url,
        }),
        commit,
        branch,
    })
}
