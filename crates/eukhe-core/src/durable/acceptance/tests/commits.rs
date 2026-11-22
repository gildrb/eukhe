//! The intent judge reads the work committed since the checks were set.

use std::process::{Command, Stdio};

use super::super::workspace::git;
use super::*;

/// A task that ends in a commit, its working tree clean, passes its
/// intent check: the judge reads the commits made since the checks were
/// set and their diff, with the working tree.
#[tokio::test]
async fn a_task_that_ends_in_a_commit_passes_its_intent_check() {
    let setup = setup();
    let (harness, root) = setup.memory().await;
    let cwd = setup.cwd();
    let git_in = |args: &[&str]| {
        let status = Command::new("git")
            .args(args)
            .current_dir(cwd)
            .env("GIT_AUTHOR_NAME", "t")
            .env("GIT_AUTHOR_EMAIL", "t@t")
            .env("GIT_COMMITTER_NAME", "t")
            .env("GIT_COMMITTER_EMAIL", "t@t")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .expect("git runs");
        assert!(status.success(), "git {args:?}");
    };
    git_in(&["init", "-q", "-b", "main"]);
    std::fs::write(cwd.join("todo.py"), "todos = []\n").expect("write");
    git_in(&["add", "."]);
    git_in(&["-c", "commit.gpgsign=false", "commit", "-q", "-m", "base"]);
    setup
        .accept(&harness, &root, vec![CheckSpec::intent()], Some(1))
        .await;
    // The worker's work, committed on a new branch before its final
    // answer: the working tree is clean.
    git_in(&["checkout", "-q", "-b", "sqlite"]);
    std::fs::write(cwd.join("todo.py"), "import sqlite3\n").expect("write");
    git_in(&[
        "-c",
        "commit.gpgsign=false",
        "commit",
        "-q",
        "-am",
        "store the todos in sqlite",
    ]);
    let head = String::from_utf8_lossy(&git(cwd, &["rev-parse", "HEAD"]).expect("a head"))
        .trim()
        .to_owned();
    *setup.judge.reads_for.lock().expect("the judge") = Some("+import sqlite3".to_owned());
    setup
        .faux
        .set_responses(vec![call("work", "w1"), answer("committed on sqlite")]);

    run(
        &harness,
        &root,
        "store the todos in sqlite and commit it on a new branch sqlite",
    )
    .await;

    let requests = judge_requests(&setup);
    let evidence = &requests[0].evidence;
    assert!(
        evidence.contains(&format!(
            "Commits since the checks were set (`git log --stat`):\ncommit {head} (HEAD -> sqlite)\n"
        )),
        "{evidence}"
    );
    assert!(
        evidence.contains("\n    store the todos in sqlite\n"),
        "{evidence}"
    );
    let got = state(&harness, &root).await;
    assert_eq!(
        (
            got.label,
            got.checks[0].result.as_ref().map(|result| result.verdict),
            requests.len()
        ),
        (
            AcceptanceLabel::ChecksPassedNotCertified,
            Some(CheckVerdict::Confirmed),
            1
        )
    );
    harness.close(cx()).await.expect("close");
}
