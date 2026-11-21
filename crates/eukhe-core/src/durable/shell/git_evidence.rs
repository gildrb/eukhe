//! The evidence of a `bash` call whose script is one `git push` or one
//! `git commit` (spec O9). Before the script runs, the call records the
//! ref the command moves and the commit that ref holds once it ran
//! ([`GitStep`], in the call's task through
//! [`ToolExecutionApi::probe`](eukhe_durable::harness::types::ToolExecutionApi::probe),
//! durable before it returns). A restart that finds the call cut looks at
//! that ref ([`probe`]): it holds the commit the command pushed or made,
//! the step landed; anything else tells nothing (a hook may have run), so
//! a git step is never seen clean.

use std::path::{Path, PathBuf};
use std::process::Stdio;
use std::sync::Arc;

use eukhe_bend::rules::once::Seen;
use eukhe_chord::json::{from_json, to_json, JsonValue};
use eukhe_durable::harness::effects::EffectKind;
use eukhe_durable::harness::types::ToolProbe;
use eukhe_durable::session::{SessionError, SessionResult};
use futures::FutureExt;
use serde::{Deserialize, Serialize};

use crate::workspace_snapshot::git::git_command;

/// The `git push` options a recorded push may carry: none forces an update
/// or pushes more than one ref.
const PUSH_FLAGS: [&str; 7] = [
    "-u",
    "--set-upstream",
    "-q",
    "--quiet",
    "-v",
    "--verbose",
    "--no-verify",
];

/// The `git commit` options that take the message from elsewhere than its
/// words (a file, another commit, a fixup).
const MESSAGE_ELSEWHERE: [&str; 8] = [
    "-F",
    "--file",
    "-C",
    "--reuse-message",
    "-c",
    "--reedit-message",
    "--fixup",
    "--squash",
];

/// A git command the call records evidence for, read from its words.
#[derive(Debug, Clone, PartialEq, Eq)]
enum GitCommand {
    /// `git push [<remote> [<src>[:<dst>]]]`; `None` where git's default
    /// applies.
    Push {
        remote: Option<String>,
        refspec: Option<Refspec>,
    },
    /// `git commit ...`, with its message when its words give it whole.
    Commit { message: Option<String> },
}

/// `<src>[:<dst>]` of a push that updates without force.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Refspec {
    src: String,
    dst: Option<String>,
}

/// The record of a call: the ref its git command moves and what that ref
/// holds once the command ran.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "git", rename_all = "camelCase")]
enum GitStep {
    /// The remote-tracking branch `refs/remotes/<remote>/<branch>` of
    /// `repo` holds `sha` once the remote took the push: git moves it only
    /// after the remote accepted the update.
    Push {
        repo: PathBuf,
        remote: String,
        branch: String,
        sha: String,
    },
    /// HEAD of `repo` has `head` as its first parent (`None`: the branch
    /// was unborn, so a root commit) and, when recorded, `message` as its
    /// message once the commit was made.
    Commit {
        repo: PathBuf,
        head: Option<String>,
        message: Option<String>,
    },
}

impl GitCommand {
    /// The git command `words` run, when it is a push or a commit this
    /// records.
    fn of(words: &[String]) -> Option<Self> {
        let [git, sub, rest @ ..] = words else {
            return None;
        };
        match (git.as_str(), sub.as_str()) {
            ("git", "push") => push(rest),
            ("git", "commit") => Some(Self::Commit {
                message: message(rest),
            }),
            _ => None,
        }
    }
}

/// A push of at most one remote and one refspec, with no option but
/// [`PUSH_FLAGS`].
fn push(rest: &[String]) -> Option<GitCommand> {
    let (flags, operands): (Vec<&str>, Vec<&str>) = rest
        .iter()
        .map(String::as_str)
        .partition(|word| word.starts_with('-'));
    if !flags.iter().all(|flag| PUSH_FLAGS.contains(flag)) {
        return None;
    }
    let refspec = match operands.as_slice() {
        [] | [_] => None,
        [_, spec] => Some(refspec(spec)?),
        _ => return None,
    };
    Some(GitCommand::Push {
        remote: operands.first().copied().map(str::to_owned),
        refspec,
    })
}

/// `spec` when it updates one ref without force (no `+`, no deletion).
fn refspec(spec: &str) -> Option<Refspec> {
    if spec.starts_with('+') {
        return None;
    }
    let (src, dst) = match spec.split_once(':') {
        Some((src, dst)) => (src, Some(dst)),
        None => (spec, None),
    };
    if src.is_empty() || dst.is_some_and(str::is_empty) {
        return None;
    }
    Some(Refspec {
        src: src.to_owned(),
        dst: dst.map(str::to_owned),
    })
}

/// The message the options of a `git commit` give whole: each `-m` or
/// `--message` value, joined into paragraphs as git joins them; `None`
/// with none, or with an option that takes it from elsewhere.
fn message(rest: &[String]) -> Option<String> {
    let mut paragraphs = Vec::new();
    let mut words = rest.iter();
    while let Some(word) = words.next() {
        let elsewhere = MESSAGE_ELSEWHERE
            .iter()
            .any(|option| word == option || word.starts_with(&format!("{option}=")));
        if elsewhere {
            return None;
        }
        if let Some(text) = word.strip_prefix("--message=") {
            paragraphs.push(text.to_owned());
        } else if word == "--message" {
            paragraphs.push(words.next()?.clone());
        } else if let Some(cluster) = word.strip_prefix('-').filter(|rest| !rest.starts_with('-')) {
            // Short options: those before `m` take no value; `m`'s is the
            // rest of the cluster or the next word.
            if let Some((before, attached)) = cluster.split_once('m') {
                if before.contains(['F', 'C', 'c', 't', 'S', 'u']) {
                    return None;
                }
                paragraphs.push(match attached {
                    "" => words.next()?.clone(),
                    attached => attached.to_owned(),
                });
            }
        }
    }
    (!paragraphs.is_empty()).then(|| paragraphs.join("\n\n"))
}

/// The record of a `bash` call whose script is `script`, run in `cwd`:
/// the evidence of its git step when the script is one push or commit
/// git can describe; `None` otherwise (the call records nothing).
///
/// # Errors
///
/// The record does not encode.
pub(super) async fn record(script: &str, cwd: &Path) -> SessionResult<Option<JsonValue>> {
    let Some(command) = eukhe_shell::literal_command(script)
        .as_deref()
        .and_then(GitCommand::of)
    else {
        return Ok(None);
    };
    match step(cwd, command).await {
        Some(step) => to_json(&step).map(Some).map_err(SessionError::other),
        None => Ok(None),
    }
}

/// What `command` run in `cwd` moves, read before it runs: the
/// repository's root and the ref with what it holds once the command ran.
/// `None` when git cannot tell (not a repository, a detached HEAD for a
/// push of the current branch, a remote it does not know, a source that is
/// no branch).
async fn step(cwd: &Path, command: GitCommand) -> Option<GitStep> {
    let repo = PathBuf::from(git(cwd, &["rev-parse", "--show-toplevel"]).await?);
    match command {
        GitCommand::Commit { message } => Some(GitStep::Commit {
            head: git(&repo, &["rev-parse", "--verify", "-q", "HEAD^{commit}"]).await,
            repo,
            message,
        }),
        GitCommand::Push { remote, refspec } => {
            let current = git(&repo, &["symbolic-ref", "--short", "-q", "HEAD"]).await;
            let remote = match remote {
                Some(remote) => remote,
                None => git(
                    &repo,
                    &["config", &format!("branch.{}.remote", current.as_deref()?)],
                )
                .await
                .unwrap_or_else(|| "origin".to_owned()),
            };
            // Only a configured remote has remote-tracking branches.
            git(&repo, &["config", &format!("remote.{remote}.url")]).await?;
            let (src, branch) = match refspec {
                Some(Refspec {
                    src,
                    dst: Some(dst),
                }) => {
                    let branch = branch_name(&dst)?.to_owned();
                    (src, branch)
                }
                Some(Refspec { src, dst: None }) => {
                    let full = git(&repo, &["rev-parse", "--symbolic-full-name", &src]).await?;
                    let branch = full.strip_prefix("refs/heads/")?.to_owned();
                    (src, branch)
                }
                None => {
                    let current = current?;
                    let branch = default_destination(&repo, &remote, &current).await?;
                    (format!("refs/heads/{current}"), branch)
                }
            };
            let sha = git(
                &repo,
                &["rev-parse", "--verify", "-q", &format!("{src}^{{commit}}")],
            )
            .await?;
            Some(GitStep::Push {
                repo,
                remote,
                branch,
                sha,
            })
        }
    }
}

/// The branch a push destination names: `refs/heads/<branch>` or a bare
/// name; any other ref (a tag, a note) is none.
fn branch_name(dst: &str) -> Option<&str> {
    match dst.strip_prefix("refs/heads/") {
        Some(branch) => Some(branch),
        None => (!dst.starts_with("refs/") && dst != "HEAD").then_some(dst),
    }
}

/// The branch of `remote` a push with no refspec updates from the local
/// branch `current`, as `push.default` says (default `simple`).
async fn default_destination(repo: &Path, remote: &str, current: &str) -> Option<String> {
    let mode = git(repo, &["config", "push.default"])
        .await
        .unwrap_or_else(|| "simple".to_owned());
    let tracked = git(repo, &["config", &format!("branch.{current}.remote")]).await;
    let upstream = if tracked.as_deref() == Some(remote) {
        git(repo, &["config", &format!("branch.{current}.merge")])
            .await
            .and_then(|merge| merge.strip_prefix("refs/heads/").map(str::to_owned))
    } else {
        None
    };
    match (mode.as_str(), upstream) {
        ("current", _) | ("simple", None) => Some(current.to_owned()),
        ("simple", Some(upstream)) => (upstream == current).then_some(upstream),
        ("upstream" | "tracking", upstream) => upstream,
        _ => None,
    }
}

/// The standard output of `git <args>` in `dir`, when it succeeds.
async fn git_output(dir: &Path, args: &[&str]) -> Option<String> {
    let output = git_command(args, dir)
        .stdin(Stdio::null())
        .stderr(Stdio::null())
        .output()
        .await
        .ok()?;
    if !output.status.success() {
        return None;
    }
    String::from_utf8(output.stdout).ok()
}

/// The one line `git <args>` prints in `dir`, when it succeeds with one.
async fn git(dir: &Path, args: &[&str]) -> Option<String> {
    let line = git_output(dir, args).await?;
    let line = line.trim_end_matches('\n');
    (!line.is_empty()).then(|| line.to_owned())
}

/// The probe of the `bash` tool: a call that recorded a git step is looked
/// at through git.
pub(super) fn probe() -> ToolProbe {
    ToolProbe {
        effect: EffectKind::Tool,
        look: Arc::new(|record: JsonValue| seen(record).boxed()),
    }
}

/// What the ref of `record` shows: it holds the commit the step pushed or
/// made, [`Seen::Landed`]; else (git cannot read it, a record that is not
/// a git step's) [`Seen::Dark`].
async fn seen(record: JsonValue) -> Seen {
    let Ok(step) = from_json::<GitStep>(&record) else {
        return Seen::Dark;
    };
    let landed = match step {
        GitStep::Push {
            repo,
            remote,
            branch,
            sha,
        } => {
            let tracking = format!("refs/remotes/{remote}/{branch}");
            git(&repo, &["rev-parse", "--verify", "-q", &tracking]).await == Some(sha)
        }
        GitStep::Commit {
            repo,
            head,
            message,
        } => {
            let made = git_output(&repo, &["log", "-1", "--format=%P%x00%B", "HEAD"]).await;
            match made.as_deref().and_then(|made| made.split_once('\0')) {
                Some((parents, made)) => {
                    parents.split_whitespace().next() == head.as_deref()
                        && message.is_none_or(|message| cleaned(&message) == cleaned(made))
                }
                None => false,
            }
        }
    };
    if landed {
        Seen::Landed
    } else {
        Seen::Dark
    }
}

/// A commit message as git's cleanup of a `-m` message leaves it: no
/// trailing whitespace on a line, no leading or trailing blank line, no
/// two blank lines in a row.
fn cleaned(message: &str) -> String {
    let mut lines: Vec<&str> = Vec::new();
    for line in message.lines().map(str::trim_end) {
        if line.is_empty() && lines.last().is_none_or(|last| last.is_empty()) {
            continue;
        }
        lines.push(line);
    }
    while lines.last().is_some_and(|last| last.is_empty()) {
        lines.pop();
    }
    lines.join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Run `git <args>` in `dir` (a throwaway repository: identity set
    /// here, the user's and system's git config ignored, so their signing
    /// settings never reach it), outside any repository the test runs in.
    fn run(dir: &Path, args: &[&str]) -> String {
        let output = std::process::Command::new("git")
            .args([
                "-c",
                "user.name=Test",
                "-c",
                "user.email=test@example.com",
                "-c",
                "init.defaultBranch=main",
                "-c",
                "core.hooksPath=/dev/null",
            ])
            .args(args)
            .current_dir(dir)
            .env("GIT_CONFIG_GLOBAL", "/dev/null")
            .env("GIT_CONFIG_NOSYSTEM", "1")
            .env_remove("GIT_DIR")
            .env_remove("GIT_WORK_TREE")
            .env_remove("GIT_INDEX_FILE")
            .env_remove("GIT_COMMON_DIR")
            .output()
            .unwrap();
        assert!(output.status.success(), "git {args:?}: {output:?}");
        String::from_utf8(output.stdout).unwrap().trim().to_owned()
    }

    fn words(script: &str) -> Option<GitCommand> {
        GitCommand::of(&eukhe_shell::literal_command(script)?)
    }

    async fn record_of(dir: &Path, script: &str) -> Option<GitStep> {
        record(script, dir)
            .await
            .unwrap()
            .map(|record| from_json(&record).unwrap())
    }

    async fn seen_of(step: &GitStep) -> Seen {
        seen(to_json(step).unwrap()).await
    }

    fn spec(src: &str, dst: Option<&str>) -> Refspec {
        Refspec {
            src: src.to_owned(),
            dst: dst.map(str::to_owned),
        }
    }

    #[test]
    fn only_one_plain_push_or_commit_is_a_git_step() {
        let push = |remote: Option<&str>, refspec| {
            Some(GitCommand::Push {
                remote: remote.map(str::to_owned),
                refspec,
            })
        };
        let commit = |message: Option<&str>| {
            Some(GitCommand::Commit {
                message: message.map(str::to_owned),
            })
        };
        assert_eq!(
            [
                "git push",
                "git push -u origin main",
                "git push origin HEAD:refs/heads/topic",
                "git push origin +main",
                "git push --force origin main",
                "git push origin :main",
                "git push origin main topic",
                "git commit -m 'one two'",
                "git commit -am x",
                "git commit -mx --message=y",
                "git commit -a",
                "git commit -F msg -m x",
                "git commit --fixup=HEAD",
                "git push && git commit -m x",
                "git status",
            ]
            .map(words),
            [
                push(None, None),
                push(Some("origin"), Some(spec("main", None))),
                push(Some("origin"), Some(spec("HEAD", Some("refs/heads/topic")))),
                None,
                None,
                None,
                None,
                commit(Some("one two")),
                commit(Some("x")),
                commit(Some("x\n\ny")),
                commit(None),
                commit(None),
                commit(None),
                None,
                None,
            ]
        );
    }

    #[tokio::test]
    async fn a_commit_landed_when_head_is_its_commit() {
        let dir = tempfile::tempdir().unwrap();
        let repo = std::fs::canonicalize(dir.path()).unwrap();
        run(&repo, &["init", "-q"]);
        std::fs::write(repo.join("a"), "a").unwrap();
        run(&repo, &["add", "a"]);
        let first = record_of(&repo, "git commit -m one").await;
        assert_eq!(
            first,
            Some(GitStep::Commit {
                repo: repo.clone(),
                head: None,
                message: Some("one".to_owned()),
            })
        );
        let first = first.unwrap();
        let unborn = seen_of(&first).await;
        run(&repo, &["commit", "-q", "-m", "one  \n"]);
        let rooted = seen_of(&first).await;
        let root = run(&repo, &["rev-parse", "HEAD"]);
        let second = record_of(&repo, "git commit --allow-empty -m two")
            .await
            .unwrap();
        let other = GitStep::Commit {
            repo: repo.clone(),
            head: Some(root.clone()),
            message: Some("other".to_owned()),
        };
        let any_message = GitStep::Commit {
            repo: repo.clone(),
            head: Some(root.clone()),
            message: None,
        };
        let before = [seen_of(&second).await, seen_of(&any_message).await];
        run(&repo, &["commit", "-q", "--allow-empty", "-m", "two"]);
        assert_eq!(
            [
                unborn,
                rooted,
                before[0],
                before[1],
                seen_of(&first).await,
                seen_of(&second).await,
                seen_of(&other).await,
                seen_of(&any_message).await,
            ],
            [
                Seen::Dark,
                Seen::Landed,
                Seen::Dark,
                Seen::Dark,
                Seen::Dark,
                Seen::Landed,
                Seen::Dark,
                Seen::Landed,
            ]
        );
    }

    #[tokio::test]
    async fn a_push_landed_when_its_remote_tracking_branch_holds_its_commit() {
        let dir = tempfile::tempdir().unwrap();
        let root = std::fs::canonicalize(dir.path()).unwrap();
        let (remote, repo) = (root.join("remote.git"), root.join("repo"));
        std::fs::create_dir(&remote).unwrap();
        std::fs::create_dir(&repo).unwrap();
        run(&remote, &["init", "-q", "--bare"]);
        run(&repo, &["init", "-q"]);
        run(
            &repo,
            &["remote", "add", "origin", remote.to_str().unwrap()],
        );
        run(&repo, &["commit", "-q", "--allow-empty", "-m", "one"]);
        run(&repo, &["tag", "v1"]);
        let sha = run(&repo, &["rev-parse", "HEAD"]);
        let push = |branch: &str| {
            Some(GitStep::Push {
                repo: repo.clone(),
                remote: "origin".to_owned(),
                branch: branch.to_owned(),
                sha: sha.clone(),
            })
        };
        let records = [
            record_of(&repo, "git push origin main").await,
            record_of(&repo, "git push").await,
            record_of(&repo, "git push origin HEAD:refs/heads/topic").await,
            record_of(&repo, "git push origin v1").await,
            record_of(&repo, "git push elsewhere main").await,
            record_of(&root, "git push origin main").await,
        ];
        assert_eq!(
            records,
            [push("main"), push("main"), push("topic"), None, None, None]
        );
        let main = push("main").unwrap();
        let before = seen_of(&main).await;
        run(&repo, &["push", "-q", "origin", "main"]);
        assert_eq!(
            [
                before,
                seen_of(&main).await,
                seen_of(&push("topic").unwrap()).await,
                seen(JsonValue::from(serde_json::json!({ "git": "other" }))).await,
            ],
            [Seen::Dark, Seen::Landed, Seen::Dark, Seen::Dark]
        );
    }
}
