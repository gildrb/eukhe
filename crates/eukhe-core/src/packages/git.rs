//! git package operations: clone with optional ref checkout, npm dependency
//! install after clone, fetch/reset/clean updates against the upstream ref,
//! and removal with empty-parent pruning.

use std::path::{Component, Path, PathBuf};

use anyhow::{bail, Result};

use super::npm;
use super::process::{run_command, run_command_capture};
use super::source::{GitSource, SourceScope};
use super::NETWORK_TIMEOUT_MS;

/// Where git packages install for a scope.
///
/// # Errors
///
/// Fails when the joined host/path does not stay strictly below the scope's
/// install root (parse-time validation should make that unreachable; this
/// guards every install, update, and removal that acts on the path).
pub fn git_install_path(
    source: &GitSource,
    scope: SourceScope,
    cwd: &Path,
    agent_dir: &Path,
) -> Result<PathBuf> {
    let root = git_install_root(scope, cwd, agent_dir).unwrap_or_else(super::temporary_root);
    let path = match scope {
        SourceScope::Temporary => {
            super::temporary_dir(&format!("git-{}", source.host), Some(&source.path))
        }
        SourceScope::Project | SourceScope::User => root.join(&source.host).join(&source.path),
    };
    let contained = path.strip_prefix(&root).is_ok_and(|relative| {
        relative.components().next().is_some()
            && relative
                .components()
                .all(|component| matches!(component, Component::Normal(_)))
    });
    if !contained {
        bail!(
            "git package path {} escapes install root {}",
            path.display(),
            root.display()
        );
    }
    Ok(path)
}

/// Git install root (used for the `.gitignore` write); `None` for temporary.
pub fn git_install_root(scope: SourceScope, cwd: &Path, agent_dir: &Path) -> Option<PathBuf> {
    match scope {
        SourceScope::Temporary => None,
        SourceScope::Project => Some(cwd.join(super::CONFIG_DIR_NAME).join("git")),
        SourceScope::User => Some(agent_dir.join("git")),
    }
}

/// Clone the package repo and install its npm dependencies when present.
pub fn install_git(
    source: &GitSource,
    scope: SourceScope,
    cwd: &Path,
    agent_dir: &Path,
    npm_command: Option<&Vec<String>>,
) -> Result<()> {
    let target_dir = git_install_path(source, scope, cwd, agent_dir)?;
    if target_dir.exists() {
        return Ok(());
    }
    if let Some(git_root) = git_install_root(scope, cwd, agent_dir) {
        npm::ensure_gitignore(&git_root)?;
    }
    if let Some(parent) = target_dir.parent() {
        std::fs::create_dir_all(parent)?;
    }

    // `--` keeps the URL and target positional; the parser already rejects
    // option-like clone URLs and refs.
    run_command(
        "git",
        &[
            "clone",
            "--",
            &source.repo,
            &target_dir.display().to_string(),
        ],
        None,
    )?;
    if let Some(git_ref) = source.r#ref.as_deref() {
        // A trailing `--` makes git read the ref as a branch/commit, never a
        // pathspec; branch names still DWIM to their `origin/` tracking ref.
        run_command("git", &["checkout", git_ref, "--"], Some(&target_dir))?;
    }
    let package_json = target_dir.join("package.json");
    if package_json.exists() {
        let (program, args) = npm::npm_command(npm_command);
        let mut full_args = args;
        full_args.extend(npm::git_dependency_install_args(npm_command));
        run_command(
            &program,
            &full_args.iter().map(String::as_str).collect::<Vec<_>>(),
            Some(&target_dir),
        )?;
    }
    Ok(())
}

/// The upstream target a git package updates against: the tracking branch
/// when one exists, otherwise the remote HEAD after refreshing it.
struct GitUpdateTarget {
    git_ref: String,
    fetch_args: Vec<String>,
}

fn get_local_git_update_target(installed_path: &Path) -> GitUpdateTarget {
    let upstream = run_command_capture(
        "git",
        &["rev-parse", "--abbrev-ref", "@{upstream}"],
        Some(installed_path),
        Some(std::time::Duration::from_millis(NETWORK_TIMEOUT_MS)),
        &[],
    );
    let trimmed_upstream = upstream.unwrap_or_default();
    if let Some(branch) = trimmed_upstream.strip_prefix("origin/") {
        if !branch.is_empty() {
            return GitUpdateTarget {
                git_ref: "@{upstream}".to_string(),
                fetch_args: vec![
                    "fetch".into(),
                    "--prune".into(),
                    "--no-tags".into(),
                    "origin".into(),
                    format!("+refs/heads/{branch}:refs/remotes/origin/{branch}"),
                ],
            };
        }
    }

    // No usable upstream branch: re-detect the remote HEAD and fetch it.
    let _ = run_command(
        "git",
        &["remote", "set-head", "origin", "-a"],
        Some(installed_path),
    );
    let origin_head_ref = run_command_capture(
        "git",
        &["symbolic-ref", "refs/remotes/origin/HEAD"],
        Some(installed_path),
        Some(std::time::Duration::from_millis(NETWORK_TIMEOUT_MS)),
        &[],
    )
    .unwrap_or_default();
    let branch = origin_head_ref
        .trim()
        .trim_start_matches("refs/remotes/origin/");
    if !branch.is_empty() {
        return GitUpdateTarget {
            git_ref: "origin/HEAD".to_string(),
            fetch_args: vec![
                "fetch".into(),
                "--prune".into(),
                "--no-tags".into(),
                "origin".into(),
                format!("+refs/heads/{branch}:refs/remotes/origin/{branch}"),
            ],
        };
    }
    GitUpdateTarget {
        git_ref: "origin/HEAD".to_string(),
        fetch_args: vec![
            "fetch".into(),
            "--prune".into(),
            "--no-tags".into(),
            "origin".into(),
            "+HEAD:refs/remotes/origin/HEAD".into(),
        ],
    }
}

/// Update an installed git package: fetch the upstream target, hard-reset to
/// it when moved, prune untracked files, and reinstall dependencies.
pub fn update_git(
    source: &GitSource,
    scope: SourceScope,
    cwd: &Path,
    agent_dir: &Path,
    npm_command: Option<&Vec<String>>,
) -> Result<()> {
    let target_dir = git_install_path(source, scope, cwd, agent_dir)?;
    if !target_dir.exists() {
        return install_git(source, scope, cwd, agent_dir, npm_command);
    }

    let target = get_local_git_update_target(&target_dir);

    let fetch_args: Vec<String> = target.fetch_args;
    run_command(
        "git",
        &fetch_args.iter().map(String::as_str).collect::<Vec<_>>(),
        Some(&target_dir),
    )?;

    let timeout = Some(std::time::Duration::from_millis(NETWORK_TIMEOUT_MS));
    let local_head = run_command_capture(
        "git",
        &["rev-parse", "HEAD"],
        Some(&target_dir),
        timeout,
        &[],
    )?;
    let target_head = run_command_capture(
        "git",
        &["rev-parse", &target.git_ref],
        Some(&target_dir),
        timeout,
        &[],
    )?;
    if local_head == target_head {
        return Ok(());
    }

    run_command(
        "git",
        &["reset", "--hard", &target.git_ref],
        Some(&target_dir),
    )?;
    // Package checkouts must be pristine after an update.
    run_command("git", &["clean", "-fdx"], Some(&target_dir))?;

    if target_dir.join("package.json").exists() {
        let (program, args) = npm::npm_command(npm_command);
        let mut full_args = args;
        full_args.extend(npm::git_dependency_install_args(npm_command));
        run_command(
            &program,
            &full_args.iter().map(String::as_str).collect::<Vec<_>>(),
            Some(&target_dir),
        )?;
    }
    Ok(())
}

/// True when the remote head differs from the local HEAD (network probe).
pub fn git_has_available_update(installed_path: &Path) -> bool {
    let timeout = Some(std::time::Duration::from_millis(NETWORK_TIMEOUT_MS));
    let Ok(local_head) = run_command_capture(
        "git",
        &["rev-parse", "HEAD"],
        Some(installed_path),
        timeout,
        &[],
    ) else {
        return false;
    };
    let Ok(remote_head) = get_remote_git_head(installed_path) else {
        return false;
    };
    local_head != remote_head
}

/// Resolve the remote HEAD commit (`ls-remote` against the upstream branch,
/// falling back to the remote HEAD ref).
fn get_remote_git_head(installed_path: &Path) -> Result<String> {
    let timeout = Some(std::time::Duration::from_millis(NETWORK_TIMEOUT_MS));
    if let Some(upstream_ref) = get_git_upstream_ref(installed_path) {
        let output = run_git_remote_command(
            installed_path,
            &["ls-remote", "origin", &upstream_ref],
            timeout,
        )?;
        if let Some(head) = first_head_commit(&output) {
            return Ok(head);
        }
    }
    let output = run_git_remote_command(installed_path, &["ls-remote", "origin", "HEAD"], timeout)?;
    output
        .lines()
        .find(|line| first_head_commit(line).is_some() && line.trim_end().ends_with("HEAD"))
        .and_then(first_head_commit)
        .ok_or_else(|| anyhow::anyhow!("Failed to determine remote HEAD"))
}

/// Extract the 40-char commit hash from the first `ls-remote` line.
fn first_head_commit(output: &str) -> Option<String> {
    output.lines().find_map(|line| {
        let hash = line.split_whitespace().next()?;
        if hash.len() == 40 && hash.chars().all(|c| c.is_ascii_hexdigit()) {
            Some(hash.to_string())
        } else {
            None
        }
    })
}

/// `refs/heads/<branch>` for the tracked upstream branch, if any.
fn get_git_upstream_ref(installed_path: &Path) -> Option<String> {
    let upstream = run_command_capture(
        "git",
        &["rev-parse", "--abbrev-ref", "@{upstream}"],
        Some(installed_path),
        Some(std::time::Duration::from_millis(NETWORK_TIMEOUT_MS)),
        &[],
    )
    .ok()?;
    let branch = upstream.trim().strip_prefix("origin/")?;
    if branch.is_empty() {
        None
    } else {
        Some(format!("refs/heads/{branch}"))
    }
}

fn run_git_remote_command(
    installed_path: &Path,
    args: &[&str],
    timeout: Option<std::time::Duration>,
) -> Result<String> {
    run_command_capture(
        "git",
        args,
        Some(installed_path),
        timeout,
        &[("GIT_TERMINAL_PROMPT", "0")],
    )
}

/// Remove an installed git package and prune now-empty parent directories up
/// to the install root.
pub fn remove_git(
    source: &GitSource,
    scope: SourceScope,
    cwd: &Path,
    agent_dir: &Path,
) -> Result<()> {
    let target_dir = git_install_path(source, scope, cwd, agent_dir)?;
    if !target_dir.exists() {
        return Ok(());
    }
    match std::fs::remove_dir_all(&target_dir) {
        Ok(()) => {}
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => return Err(error.into()),
    }
    if let Some(install_root) = git_install_root(scope, cwd, agent_dir) {
        prune_empty_git_parents(&target_dir, &install_root);
    }
    Ok(())
}

fn prune_empty_git_parents(target_dir: &Path, install_root: &Path) {
    let mut current = target_dir
        .parent()
        .map(Path::to_path_buf)
        .unwrap_or_default();
    while current.starts_with(install_root) && current != install_root {
        if !current.exists() {
            match current.parent().map(Path::to_path_buf) {
                Some(parent) => current = parent,
                None => break,
            }
            continue;
        }
        let empty = std::fs::read_dir(&current).is_ok_and(|entries| entries.count() == 0);
        if !empty {
            break;
        }
        if std::fs::remove_dir_all(&current).is_err() {
            break;
        }
        match current.parent().map(Path::to_path_buf) {
            Some(parent) => current = parent,
            None => break,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn source_with_path(path: &str) -> GitSource {
        GitSource {
            repo: "https://h.io/user/repo".to_string(),
            host: "h.io".to_string(),
            path: path.to_string(),
            r#ref: None,
            pinned: false,
        }
    }

    #[test]
    fn remove_refuses_paths_outside_the_install_root() {
        let root = tempfile::tempdir().unwrap();
        let cwd = root.path().join("project");
        let agent_dir = root.path().join("agent");
        let victim = cwd.join("victim");
        std::fs::create_dir_all(&victim).unwrap();
        let install_root = cwd.join(super::super::CONFIG_DIR_NAME).join("git");

        for path in ["../../../victim", victim.to_str().unwrap()] {
            let escaped = install_root.join("h.io").join(path);
            let error = remove_git(
                &source_with_path(path),
                SourceScope::Project,
                &cwd,
                &agent_dir,
            )
            .unwrap_err();
            assert_eq!(
                error.to_string(),
                format!(
                    "git package path {} escapes install root {}",
                    escaped.display(),
                    install_root.display()
                )
            );
            assert!(victim.exists(), "{path}");
        }
    }

    #[test]
    fn install_path_stays_below_the_install_root() {
        let root = tempfile::tempdir().unwrap();
        let agent_dir = root.path().join("agent");
        let path = git_install_path(
            &source_with_path("user/repo"),
            SourceScope::User,
            root.path(),
            &agent_dir,
        )
        .unwrap();
        assert_eq!(path, agent_dir.join("git").join("h.io").join("user/repo"));
    }
}
