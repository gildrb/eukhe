//! The git side of autoresearch (port of omp `autoresearch/git.ts`): the
//! repository of the session, its `autoresearch/*` branch, the commit of
//! a kept run, the reset of every other run, and the paths a run changed.
//! It carries out what the Lab decided; it decides nothing about runs.
//! Every git command runs with [`eukhe_shell::GIT_UNTRUSTED_REPO_ARGS`]:
//! a repository's own configuration runs no hook, monitor or pager.

use std::path::{Path, PathBuf};
use std::process::Output;

use anyhow::{bail, Context as _};

/// The prefix of every autoresearch branch.
pub(crate) const BRANCH_PREFIX: &str = "autoresearch/";

/// The longest goal slug of a branch name.
const SLUG_MAX: usize = 48;

/// The dirty paths an error lists before it counts the rest.
const DIRTY_PREVIEW: usize = 5;

/// The git checkout of the session: its top-level directory.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Repo {
    pub(crate) root: PathBuf,
}

/// Where the session runs: the repository root (or the cwd without git)
/// and the branch checked out (`None`: no git, or a detached HEAD).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Workspace {
    pub(crate) root: PathBuf,
    pub(crate) repo: Option<Repo>,
    pub(crate) branch: Option<String>,
}

impl Workspace {
    /// The workspace of `cwd`: its git top level and branch, or `cwd`
    /// itself when it is in no git checkout (or git is missing).
    ///
    /// # Errors
    ///
    /// A git command of a found checkout fails.
    pub(crate) async fn of(cwd: &Path) -> anyhow::Result<Self> {
        let Ok(top) = git_in(cwd, &["rev-parse", "--show-toplevel"]).await else {
            return Ok(Self {
                root: cwd.to_path_buf(),
                repo: None,
                branch: None,
            });
        };
        if !top.status.success() {
            return Ok(Self {
                root: cwd.to_path_buf(),
                repo: None,
                branch: None,
            });
        }
        let repo = Repo {
            root: PathBuf::from(text(&top.stdout).trim()),
        };
        let branch = repo.branch().await?;
        Ok(Self {
            root: repo.root.clone(),
            repo: Some(repo),
            branch,
        })
    }

    /// Whether the branch checked out is an `autoresearch/*` branch.
    pub(crate) fn on_autoresearch_branch(&self) -> bool {
        self.branch
            .as_deref()
            .is_some_and(|branch| branch.starts_with(BRANCH_PREFIX))
    }
}

/// What [`ensure_branch`] found or did.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Branch {
    /// The session was on this autoresearch branch already.
    Kept(String),
    /// It created this branch from a clean tree and checked it out.
    Created(String),
    /// No git checkout: no branch, no commit, no reset.
    NoGit,
}

impl Branch {
    /// One line for the user and the model.
    pub(crate) fn line(&self) -> String {
        match self {
            Self::Kept(name) => format!("Using the autoresearch branch `{name}`."),
            Self::Created(name) => format!("Created and checked out the branch `{name}`."),
            Self::NoGit => "Not in a git repository: autoresearch runs without a branch, \
commits of kept runs, or resets of the others."
                .to_owned(),
        }
    }
}

/// Put the workspace on an `autoresearch/*` branch (omp
/// `ensureAutoresearchBranch`): keep the one checked out, else create
/// `autoresearch/<slug(goal)>-<YYYYMMDD>[-N]` from a clean tree.
///
/// # Errors
///
/// The tree has changes (a new branch needs a clean baseline), or a git
/// command fails.
pub(crate) async fn ensure_branch(
    workspace: &Workspace,
    goal: Option<&str>,
    date: &str,
) -> anyhow::Result<Branch> {
    let Some(repo) = &workspace.repo else {
        return Ok(Branch::NoGit);
    };
    if let Some(branch) = &workspace.branch {
        if branch.starts_with(BRANCH_PREFIX) {
            return Ok(Branch::Kept(branch.clone()));
        }
    }
    let dirty = repo.dirty_paths().await?;
    if !dirty.is_empty() {
        let mut preview = dirty
            .iter()
            .take(DIRTY_PREVIEW)
            .map(String::as_str)
            .collect::<Vec<_>>()
            .join(", ");
        if dirty.len() > DIRTY_PREVIEW {
            preview = format!("{preview} (+{} more)", dirty.len() - DIRTY_PREVIEW);
        }
        bail!(
            "the work tree has changes ({preview}). Commit or stash them before autoresearch \
starts: a new autoresearch/* branch needs a clean baseline. To keep a harness you wrote \
already, create the branch yourself (`git switch -c autoresearch/<name>`): autoresearch keeps it."
        );
    }
    let slug = match slug(goal.unwrap_or_default()) {
        slug if slug.is_empty() => "session".to_owned(),
        slug => slug,
    };
    let base = format!("{BRANCH_PREFIX}{slug}-{date}");
    let mut name = base.clone();
    let mut suffix = 2;
    while repo.branch_exists(&name).await? {
        name = format!("{base}-{suffix}");
        suffix += 1;
    }
    repo.run(&["checkout", "-q", "-b", &name]).await?;
    Ok(Branch::Created(name))
}

/// The goal as a branch-name slug: lower-case ASCII letters and digits,
/// every other run of characters one `-`, at most [`SLUG_MAX`] long.
pub(crate) fn slug(goal: &str) -> String {
    let mut out = String::new();
    for character in goal.chars() {
        if character.is_ascii_alphanumeric() {
            out.push(character.to_ascii_lowercase());
        } else if !out.is_empty() && !out.ends_with('-') {
            out.push('-');
        }
        if out.len() >= SLUG_MAX {
            break;
        }
    }
    out.truncate(SLUG_MAX);
    out.trim_end_matches('-').to_owned()
}

impl Repo {
    /// The branch checked out; `None` on a detached HEAD.
    async fn branch(&self) -> anyhow::Result<Option<String>> {
        let out = git_in(&self.root, &["symbolic-ref", "--quiet", "--short", "HEAD"]).await?;
        Ok(out
            .status
            .success()
            .then(|| text(&out.stdout).trim().to_owned()))
    }

    async fn branch_exists(&self, name: &str) -> anyhow::Result<bool> {
        let reference = format!("refs/heads/{name}");
        let out = git_in(
            &self.root,
            &["show-ref", "--verify", "--quiet", reference.as_str()],
        )
        .await?;
        Ok(out.status.success())
    }

    /// Every path that differs from `HEAD` or is untracked, relative to
    /// the root (both names of a rename).
    pub(crate) async fn dirty_paths(&self) -> anyhow::Result<Vec<String>> {
        let out = self
            .run(&["status", "--porcelain=v1", "-z", "--untracked-files=all"])
            .await?;
        Ok(parse_status(&text(&out.stdout)))
    }

    /// Commit every change of the tree with `message`; the note says what
    /// happened (`committed <sha>`, or `nothing to commit`).
    ///
    /// # Errors
    ///
    /// A git command fails (a hook refused the commit, no identity, ...).
    pub(crate) async fn commit_all(&self, message: &str) -> anyhow::Result<String> {
        self.run(&["add", "-A"]).await?;
        let staged = git_in(&self.root, &["diff", "--cached", "--quiet"]).await?;
        if staged.status.success() {
            return Ok("nothing to commit".to_owned());
        }
        self.run(&["commit", "-q", "-m", message]).await?;
        let head = self.run(&["rev-parse", "--short=12", "HEAD"]).await?;
        Ok(format!("committed {}", text(&head.stdout).trim()))
    }

    /// Drop every change since `HEAD`: `reset --hard HEAD`, then
    /// `clean -fd` (ignored files stay).
    ///
    /// # Errors
    ///
    /// A git command fails.
    pub(crate) async fn reset(&self) -> anyhow::Result<String> {
        self.run(&["reset", "-q", "--hard", "HEAD"]).await?;
        self.run(&["clean", "-q", "-fd"]).await?;
        Ok("work tree reset to HEAD".to_owned())
    }

    async fn run(&self, args: &[&str]) -> anyhow::Result<Output> {
        let out = git_in(&self.root, args).await?;
        if !out.status.success() {
            bail!(
                "git {} failed: {}",
                args.join(" "),
                text(&out.stderr).trim()
            );
        }
        Ok(out)
    }
}

/// The paths of a `git status --porcelain=v1 -z` listing.
fn parse_status(listing: &str) -> Vec<String> {
    let mut paths: Vec<String> = Vec::new();
    let mut fields = listing.split('\0');
    while let Some(entry) = fields.next() {
        if entry.len() < 4 {
            continue;
        }
        let (code, path) = entry.split_at(3);
        push_unique(&mut paths, path);
        // A rename or copy names its source in the next field.
        if code.starts_with('R') || code.starts_with('C') {
            if let Some(source) = fields.next() {
                push_unique(&mut paths, source);
            }
        }
    }
    paths
}

fn push_unique(paths: &mut Vec<String>, path: &str) {
    if !path.is_empty() && !paths.iter().any(|seen| seen == path) {
        paths.push(path.to_owned());
    }
}

/// A path spec as omp normalizes it: `/` separators, no leading `./`, no
/// trailing `/`; empty or `.` is the whole tree.
fn normalize(spec: &str) -> String {
    let spec = spec.trim().replace('\\', "/");
    let spec = spec.trim_start_matches("./").trim_end_matches('/');
    if spec.is_empty() {
        ".".to_owned()
    } else {
        spec.to_owned()
    }
}

/// Whether `path` is `spec` or lies under it.
fn within(path: &str, spec: &str) -> bool {
    let spec = normalize(spec);
    let path = normalize(path);
    spec == "." || path == spec || path.starts_with(&format!("{spec}/"))
}

/// The changed paths outside `scope` (when it names any) or inside
/// `off_limits` (omp `computeScopeDeviations`).
pub(crate) fn deviations(
    changed: &[String],
    scope: &[String],
    off_limits: &[String],
) -> Vec<String> {
    changed
        .iter()
        .filter(|path| {
            off_limits.iter().any(|spec| within(path, spec))
                || (!scope.is_empty() && !scope.iter().any(|spec| within(path, spec)))
        })
        .cloned()
        .collect()
}

async fn git_in(dir: &Path, args: &[&str]) -> anyhow::Result<Output> {
    tokio::process::Command::new("git")
        .args(eukhe_shell::GIT_UNTRUSTED_REPO_ARGS)
        .arg("-C")
        .arg(dir)
        .args(args)
        .stdin(std::process::Stdio::null())
        .kill_on_drop(true)
        .output()
        .await
        .with_context(|| format!("could not run git {}", args.join(" ")))
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

#[cfg(test)]
mod tests {
    use super::{deviations, parse_status, slug};

    #[test]
    fn slug_keeps_words_and_bounds_length() {
        assert_eq!(
            slug("Speed up the JSON parser!"),
            "speed-up-the-json-parser"
        );
        assert_eq!(slug("  --  "), "");
        assert_eq!(slug(&"a".repeat(60)).len(), 48);
        assert_eq!(slug(&format!("{}-b", "a".repeat(47))), "a".repeat(47));
    }

    #[test]
    fn status_lists_both_names_of_a_rename() {
        assert_eq!(
            parse_status(" M src/a.rs\0R  new.rs\0old.rs\0?? bench/x\0"),
            vec!["src/a.rs", "new.rs", "old.rs", "bench/x"]
        );
    }

    #[test]
    fn deviations_are_outside_scope_or_off_limits() {
        let changed = vec![
            "src/a.rs".to_owned(),
            "docs/x.md".to_owned(),
            "src/gen/b.rs".to_owned(),
        ];
        assert_eq!(
            deviations(&changed, &["./src/".to_owned()], &["src/gen".to_owned()]),
            vec!["docs/x.md", "src/gen/b.rs"]
        );
        assert_eq!(deviations(&changed, &[], &[]), Vec::<String>::new());
    }
}
