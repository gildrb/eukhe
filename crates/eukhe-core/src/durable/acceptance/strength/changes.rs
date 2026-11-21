//! The lines the task changed: the workspace against the commit it held
//! when the checks were set (its baseline), committed or not, and every
//! line of each untracked file that is not ignored. Only these lines are
//! broken on purpose: a check is judged on the code the task wrote.

use std::path::Path;

use super::super::workspace::{git, EMPTY_TREE};

/// One file the task changed and its changed lines (from 1, as the file
/// is now), in order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Changed {
    /// Relative to the workspace.
    pub(crate) path: String,
    pub(crate) lines: Vec<u32>,
}

/// Why the changed lines are unknown.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Unknown {
    /// The workspace is no git repository.
    NoRepository,
    /// git could not diff the workspace against the baseline.
    NoDiff(String),
}

impl Unknown {
    pub(crate) fn text(&self) -> String {
        match self {
            Self::NoRepository => {
                "the workspace is no git repository, so the lines the task changed are unknown"
                    .to_owned()
            }
            Self::NoDiff(baseline) => {
                format!("git could not diff the workspace against {baseline}")
            }
        }
    }
}

/// The commit the workspace at `cwd` holds now; `None` outside a git
/// repository or before its first commit.
pub(crate) async fn baseline(cwd: &Path) -> Option<String> {
    let cwd = cwd.to_path_buf();
    tokio::task::spawn_blocking(move || {
        git(&cwd, &["rev-parse", "--verify", "--quiet", "HEAD"])
            .map(|out| String::from_utf8_lossy(&out).trim().to_owned())
            .filter(|head| !head.is_empty())
    })
    .await
    .ok()
    .flatten()
}

/// The files under `cwd` the task changed since `baseline` (the empty tree
/// when `None`), with their changed lines.
///
/// # Errors
///
/// [`Unknown`]: no git repository, or no diff.
pub(crate) fn changed_lines(cwd: &Path, baseline: Option<&str>) -> Result<Vec<Changed>, Unknown> {
    git(cwd, &["rev-parse", "--show-toplevel"]).ok_or(Unknown::NoRepository)?;
    let base = baseline.unwrap_or(EMPTY_TREE);
    let diff = git(
        cwd,
        &[
            "diff",
            "--no-color",
            "--no-ext-diff",
            "--no-renames",
            "--relative",
            "--unified=0",
            base,
            "--",
        ],
    )
    .ok_or_else(|| Unknown::NoDiff(base.to_owned()))?;
    let mut changed = hunks(&String::from_utf8_lossy(&diff));
    let untracked =
        git(cwd, &["ls-files", "--others", "--exclude-standard", "-z"]).unwrap_or_default();
    for path in untracked
        .split(|byte| *byte == 0)
        .filter(|path| !path.is_empty())
        .map(|path| String::from_utf8_lossy(path).into_owned())
    {
        let Ok(text) = std::fs::read_to_string(cwd.join(&path)) else {
            // Binary or unreadable: nothing to break line by line.
            continue;
        };
        let count = u32::try_from(text.lines().count()).unwrap_or(u32::MAX);
        changed.push(Changed {
            path,
            lines: (1..=count).collect(),
        });
    }
    changed.sort_by(|a, b| a.path.cmp(&b.path));
    Ok(changed)
}

/// The new-side lines of each file of a `--unified=0` diff.
fn hunks(diff: &str) -> Vec<Changed> {
    let mut files: Vec<Changed> = Vec::new();
    let mut current: Option<Changed> = None;
    for line in diff.lines() {
        if let Some(path) = line.strip_prefix("+++ ") {
            files.extend(current.take().filter(|file| !file.lines.is_empty()));
            current = path.strip_prefix("b/").map(|path| Changed {
                path: path.to_owned(),
                lines: Vec::new(),
            });
        } else if let (Some(file), Some(range)) = (current.as_mut(), new_range(line)) {
            file.lines.extend(range);
        }
    }
    files.extend(current.filter(|file| !file.lines.is_empty()));
    files
}

/// The new-side lines of a hunk header `@@ -a[,b] +c[,d] @@`.
fn new_range(line: &str) -> Option<std::ops::Range<u32>> {
    let rest = line.strip_prefix("@@ ")?;
    let new = rest.split(' ').find_map(|word| word.strip_prefix('+'))?;
    let (start, count) = match new.split_once(',') {
        Some((start, count)) => (start.parse::<u32>().ok()?, count.parse::<u32>().ok()?),
        None => (new.parse::<u32>().ok()?, 1),
    };
    Some(start..start.saturating_add(count))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_diff_gives_the_new_lines_of_each_changed_file() {
        let diff = "diff --git a/src/a.rs b/src/a.rs\n--- a/src/a.rs\n+++ b/src/a.rs\n@@ -3 +3 @@\n-x\n+y\n@@ -10,0 +11,2 @@\n+p\n+q\ndiff --git a/gone.py b/gone.py\n--- a/gone.py\n+++ /dev/null\n@@ -1,2 +0,0 @@\n-a\n-b\ndiff --git a/b.py b/b.py\n--- a/b.py\n+++ b/b.py\n@@ -4,2 +3,0 @@\n-a\n-b\n";
        assert_eq!(
            hunks(diff),
            vec![Changed {
                path: "src/a.rs".to_owned(),
                lines: vec![3, 11, 12],
            }]
        );
    }

    #[test]
    fn the_task_s_lines_are_those_since_the_baseline_and_the_untracked_files() {
        let dir = tempfile::tempdir().expect("dir");
        let root = dir.path();
        let git_in = |args: &[&str]| {
            let status = std::process::Command::new("git")
                .args(args)
                .current_dir(root)
                .env("GIT_AUTHOR_NAME", "t")
                .env("GIT_AUTHOR_EMAIL", "t@t")
                .env("GIT_COMMITTER_NAME", "t")
                .env("GIT_COMMITTER_EMAIL", "t@t")
                .status()
                .expect("git");
            assert!(status.success(), "{args:?}");
        };
        git_in(&["init", "-q"]);
        std::fs::write(root.join("lib.py"), "a = 1\nb = 2\nc = 3\n").expect("write");
        git_in(&["add", "."]);
        git_in(&["-c", "commit.gpgsign=false", "commit", "-q", "-m", "base"]);
        let base = git(root, &["rev-parse", "HEAD"]).expect("head");
        let base = String::from_utf8_lossy(&base).trim().to_owned();
        std::fs::write(root.join("lib.py"), "a = 1\nb = 20\nc = 3\nd = 4\n").expect("write");
        // A commit made during the task still counts.
        git_in(&["-c", "commit.gpgsign=false", "commit", "-q", "-am", "task"]);
        std::fs::write(root.join("new.py"), "x = 1\ny = 2\n").expect("write");
        assert_eq!(
            changed_lines(root, Some(&base)),
            Ok(vec![
                Changed {
                    path: "lib.py".to_owned(),
                    lines: vec![2, 4],
                },
                Changed {
                    path: "new.py".to_owned(),
                    lines: vec![1, 2],
                },
            ])
        );
        let plain = tempfile::tempdir().expect("dir");
        assert_eq!(
            changed_lines(plain.path(), None),
            Err(Unknown::NoRepository)
        );
    }
}
