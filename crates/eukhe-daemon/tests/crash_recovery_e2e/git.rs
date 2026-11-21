//! A `bash` call that is one `git commit` or one `git push` across
//! `kill -9` (spec O9). The session's cwd is a git repository with a bare
//! remote (`origin`, a path) and a staged file. The worker dies by
//! `SIGKILL` at a point of the call (`EUKHE_TEST_KILL_AT=tool:<point>`:
//! `probed` once the refs it moves are durable, before git runs; `ran`
//! once git ran, before the result is durable). After the restart:
//!
//! - cut before git ran: the ref shows nothing, and a repeat is not safe:
//!   treated as not run, listed once in the ledger with its cause; the
//!   commit or the push never happened.
//! - cut after git ran: the ref holds the commit it made or pushed:
//!   adopted, never run again, nothing in the ledger.
//!
//! Either way the run goes on to its answer with nobody asked.

use super::*;

/// The prompt tags the script answers with the `bash` call of one git
/// command.
pub(crate) const COMMIT_TAG: &str = "[git-commit]";
pub(crate) const PUSH_TAG: &str = "[git-push]";

/// The commit's message.
const MESSAGE: &str = "x";

/// The file beside the remote the remote's `post-receive` hook appends a
/// line to, once per push it takes.
const PUSHES: &str = "pushes";

/// The script of the call a turn tagged here makes.
pub(crate) fn script(prompt: &str) -> Option<String> {
    if prompt.contains(COMMIT_TAG) {
        Some(format!("git commit -m {MESSAGE}"))
    } else if prompt.contains(PUSH_TAG) {
        Some("git push origin main".to_owned())
    } else {
        None
    }
}

/// Run `git <args>` in `dir` (the test's throwaway repositories), outside
/// any repository the test runs in; answers its output.
fn git(dir: &Path, args: &[&str]) -> String {
    let output = Command::new("git")
        .args(args)
        .current_dir(dir)
        .env_remove("GIT_DIR")
        .env_remove("GIT_WORK_TREE")
        .env_remove("GIT_INDEX_FILE")
        .env_remove("GIT_COMMON_DIR")
        .output()
        .expect("git runs");
    assert!(output.status.success(), "git {args:?}: {output:?}");
    String::from_utf8(output.stdout)
        .expect("git prints text")
        .trim()
        .to_owned()
}

/// Make `repo` a repository on `main` with one commit, a staged file and
/// the bare remote `origin` at `remote`, whose hook counts the pushes it
/// takes. Each repository has its own identity and hooks.
fn set_up(repo: &Path, remote: &Path) {
    let quiet = repo.join("no-hooks");
    std::fs::create_dir(&quiet).expect("the hooks dir");
    git(repo, &["init", "-q", "-b", "main"]);
    for (key, value) in [
        ("user.name", "Test"),
        ("user.email", "test@example.com"),
        ("commit.gpgsign", "false"),
        ("core.hooksPath", quiet.to_str().expect("a UTF-8 path")),
    ] {
        git(repo, &["config", key, value]);
    }
    git(repo, &["commit", "-q", "--allow-empty", "-m", "base"]);
    std::fs::write(repo.join("staged.txt"), "staged\n").expect("the staged file");
    git(repo, &["add", "staged.txt"]);
    std::fs::create_dir(remote).expect("the remote dir");
    git(remote, &["init", "-q", "--bare", "-b", "main"]);
    let hooks = remote.join("hooks");
    let hook = hooks.join("post-receive");
    let pushes = remote.with_file_name(PUSHES);
    std::fs::write(
        &hook,
        format!("#!/bin/sh\necho pushed >> '{}'\n", pushes.display()),
    )
    .expect("the hook");
    let mut permissions = std::fs::metadata(&hook).expect("the hook").permissions();
    std::os::unix::fs::PermissionsExt::set_mode(&mut permissions, 0o755);
    std::fs::set_permissions(&hook, permissions).expect("the hook runs");
    git(
        remote,
        &[
            "config",
            "core.hooksPath",
            hooks.to_str().expect("a UTF-8 path"),
        ],
    );
    git(
        repo,
        &[
            "remote",
            "add",
            "origin",
            remote.to_str().expect("a UTF-8 path"),
        ],
    );
}

/// What the transcript says of the call.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Said {
    /// Its change landed: adopted.
    Landed,
    /// Treated as not run.
    Interrupted,
}

/// What a restart after a kill at `tool:<point>` left of the turn tagged
/// `tag`: what the transcript says of the call, the ledger's entries
/// (`(id, cause, names its run)`), the commits of `main` and the pushes
/// the remote took.
#[derive(Debug, PartialEq, Eq)]
struct Cut {
    said: Said,
    noted: Vec<(Value, Value, bool)>,
    commits: usize,
    pushes: usize,
}

fn git_cut_at(point: &str, tag: &str) -> Cut {
    let marks = tempfile::tempdir().expect("marker dir");
    let marker = marks.path().join("killed");
    let world = World::with_env(
        128_000,
        &json!({}),
        &[(
            "EUKHE_TEST_KILL_AT",
            format!("tool:{point}@{}", marker.display()),
        )],
    );
    let repo = world.dir.path();
    let remote = repo.join("remote.git");
    set_up(repo, &remote);
    let mut client = world.connect();
    let session_id = world.create(&mut client, 0);
    let worker = worker_pid(&mut client, &session_id);
    let message = prompt("t1", &[tag], 0);
    client.send(&json!({ "type": "prompt", "activeSessionId": session_id, "message": message }));
    let deadline = Instant::now() + WAIT;
    while !marker.exists() {
        assert!(
            Instant::now() < deadline,
            "no process reached tool:{point}\n{}",
            world.diagnostics()
        );
        std::thread::sleep(Duration::from_millis(20));
    }
    wait_dead(worker);
    drop(client);

    let mut client = reattach(&world, &session_id);
    wait_idle(&mut client, &session_id);
    // The run went on to its answer: nothing waited on a person.
    assert_transcript(&world, std::slice::from_ref(&message));
    let results: Vec<String> = messages_of(&world.transcript(), "toolResult")
        .iter()
        .filter(|(_, result)| result["toolCallId"] == "call-t1")
        .map(|(_, result)| texts(result).join("\n"))
        .collect();
    let [result] = results.as_slice() else {
        panic!("one result of the call: {results:?}");
    };
    let said = if result.contains(
        "Tool bash was interrupted and may have partially run. Check the state it changes \
         (files, processes, jobs) before you run it again.",
    ) {
        Said::Interrupted
    } else if result.contains("Tool bash was cut by a restart after its change landed") {
        Said::Landed
    } else {
        panic!("a result that is neither landed nor interrupted: {result}");
    };
    let listed = client.request(
        &json!({ "type": "get_unknown_effects", "activeSessionId": session_id }),
        WAIT,
    );
    assert_eq!(listed["success"], true, "get_unknown_effects: {listed}");
    let noted = listed["data"]["effects"]
        .as_array()
        .map(|effects| {
            effects
                .iter()
                .map(|effect| {
                    (
                        effect["id"].clone(),
                        effect["cause"].clone(),
                        effect["settledRun"].is_u64(),
                    )
                })
                .collect()
        })
        .unwrap_or_default();
    let commits = git(repo, &["rev-list", "--count", "main"])
        .parse()
        .expect("a count");
    let pushes = std::fs::read_to_string(remote.with_file_name(PUSHES))
        .map_or(0, |pushes| pushes.lines().count());
    Cut {
        said,
        noted,
        commits,
        pushes,
    }
}

/// The ledger of a call treated as not run.
fn not_run() -> Vec<(Value, Value, bool)> {
    vec![(json!("tool:call-t1"), json!("notRepeatSafe"), true)]
}

#[test]
fn a_git_commit_cut_before_it_ran_is_treated_as_not_run_and_never_made() {
    assert_eq!(
        git_cut_at("probed", COMMIT_TAG),
        Cut {
            said: Said::Interrupted,
            noted: not_run(),
            commits: 1,
            pushes: 0,
        }
    );
}

#[test]
fn a_git_commit_cut_after_it_ran_is_adopted_and_made_once() {
    assert_eq!(
        git_cut_at("ran", COMMIT_TAG),
        Cut {
            said: Said::Landed,
            noted: Vec::new(),
            commits: 2,
            pushes: 0,
        }
    );
}

#[test]
fn a_git_push_cut_before_it_ran_is_treated_as_not_run_and_never_pushed() {
    assert_eq!(
        git_cut_at("probed", PUSH_TAG),
        Cut {
            said: Said::Interrupted,
            noted: not_run(),
            commits: 1,
            pushes: 0,
        }
    );
}

#[test]
fn a_git_push_cut_after_it_ran_is_adopted_and_pushed_once() {
    assert_eq!(
        git_cut_at("ran", PUSH_TAG),
        Cut {
            said: Said::Landed,
            noted: Vec::new(),
            commits: 1,
            pushes: 1,
        }
    );
}
