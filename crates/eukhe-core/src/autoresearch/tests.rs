//! The autoresearch loop end to end on a real temporary git repository:
//! the branch, the harness commit, a baseline, a kept improvement and its
//! commit, a worse keep the Lab refuses, a discard that resets the tree, a
//! crash, the iteration cap, and the replay of the log after a reopen.

use std::path::Path;
use std::process::Command;
use std::sync::Arc;
use std::time::Duration;

use eukhe_bend::rules::autoresearch::{Direction, Mode, Status};
use eukhe_types::path_policy::PathPolicy;
use eukhe_types::shell::{AutoSet, ShellEffect};
use serde_json::{json, Value};

use super::git::{Branch, Workspace};
use super::ops::{InitArgs, LogArgs};
use super::runner::RunGate;
use super::store::Store;
use super::{Autoresearch, Refused};
use crate::durable::shell::SinkApprover;

const HARNESS: &str = "#!/usr/bin/env bash\nset -e\necho \"warming up\"\necho \"METRIC time_ms=$(cat value.txt)\"\necho \"METRIC size_kb=3\"\nexit \"$(cat exit.txt 2>/dev/null || echo 0)\"\n";

fn git(repo: &Path, args: &[&str]) -> String {
    let out = Command::new("git")
        .arg("-C")
        .arg(repo)
        .args(args)
        .output()
        .expect("git runs");
    assert!(
        out.status.success(),
        "git {args:?}: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).trim().to_owned()
}

/// A repository on `main` with one commit; a throwaway repo, so it
/// carries its own identity and never signs.
fn repository(dir: &Path) {
    git(dir, &["init", "-q", "-b", "main"]);
    git(dir, &["config", "user.name", "autoresearch test"]);
    git(dir, &["config", "user.email", "test@example.invalid"]);
    git(dir, &["config", "commit.gpgsign", "false"]);
    std::fs::write(dir.join("README"), "parser\n").unwrap();
    std::fs::write(dir.join("value.txt"), "10\n").unwrap();
    git(dir, &["add", "-A"]);
    git(dir, &["commit", "-q", "-m", "start"]);
}

fn lab(home: &Path, cwd: &Path) -> Autoresearch {
    let root = cwd.to_path_buf();
    Autoresearch::new(
        home,
        cwd.to_path_buf(),
        Arc::new(move |request: &str| RunGate {
            env: std::env::vars().collect(),
            auto: AutoSet::new(
                ShellEffect::ALL
                    .iter()
                    .copied()
                    .filter(|effect| !matches!(effect, ShellEffect::Secret)),
            ),
            paths: PathPolicy::new(vec![root.clone()], Vec::new(), Vec::new()),
            approver: SinkApprover {
                sink: None,
                call: request.to_owned(),
            },
        }),
    )
}

fn log(status: Status, description: &str) -> LogArgs {
    LogArgs {
        status,
        description: description.to_owned(),
        justification: None,
        flags: Vec::new(),
    }
}

async fn run(lab: &Autoresearch) -> Value {
    lab.run(Duration::from_secs(60), "test")
        .await
        .unwrap()
        .value
}

#[tokio::test]
async fn the_loop_runs_end_to_end_on_a_real_repository() {
    let home = tempfile::tempdir().unwrap();
    let repo_dir = tempfile::tempdir().unwrap();
    let repo = repo_dir.path().canonicalize().unwrap();
    repository(&repo);
    let lab = lab(home.path(), &repo);

    // `/autoresearch <goal>` from a clean tree: a new branch, mode on.
    let begun = lab.begin("Speed up the parser").await.unwrap();
    let date = crate::platform::local_time(std::time::SystemTime::now()).unwrap();
    let branch = format!(
        "autoresearch/speed-up-the-parser-{:04}{:02}{:02}",
        date.year, date.month, date.day
    );
    assert_eq!(begun.branch, Branch::Created(branch.clone()));
    assert!(!begun.configured);
    assert_eq!(git(&repo, &["branch", "--show-current"]), branch);

    // The harness, then init: the harness becomes the baseline commit.
    std::fs::write(repo.join("autoresearch.sh"), HARNESS).unwrap();
    let init = lab
        .init(InitArgs {
            name: "parser".to_owned(),
            metric: "time_ms".to_owned(),
            goal: Some("Speed up the parser".to_owned()),
            unit: "ms".to_owned(),
            direction: Direction::Lower,
            secondary: vec!["size_kb".to_owned()],
            scope: vec!["value.txt".to_owned()],
            off_limits: Vec::new(),
            constraints: vec!["keep the output identical".to_owned()],
            max_iterations: Some(4),
            new_segment: false,
        })
        .await
        .unwrap();
    assert!(init.started);
    assert_eq!(init.mode, Mode::On);
    assert_eq!(git(&repo, &["status", "--porcelain"]), "");
    assert_eq!(
        git(&repo, &["log", "-1", "--format=%s"]),
        "autoresearch: harness"
    );

    // Baseline: passes, parses both metrics, keeps (nothing to commit).
    let baseline = run(&lab).await;
    assert_eq!(baseline["run"]["passed"], json!(true));
    assert_eq!(baseline["run"]["metric"], json!("10"));
    assert_eq!(baseline["run"]["metrics"], json!([["size_kb", "3"]]));
    assert_eq!(baseline["exit_code"], json!(0));
    assert!(baseline["tail"]
        .as_str()
        .unwrap()
        .contains("METRIC time_ms=10"));
    let kept = lab.log(log(Status::Keep, "baseline")).await.unwrap();
    assert_eq!(kept.value["git"], json!("nothing to commit"));
    assert_eq!(kept.value["state"]["baseline"], json!("10"));

    // A better run kept: committed with its result.
    std::fs::write(repo.join("value.txt"), "8\n").unwrap();
    assert_eq!(run(&lab).await["run"]["metric"], json!("8"));
    let kept = lab.log(log(Status::Keep, "cache the table")).await.unwrap();
    assert!(kept.value["git"]
        .as_str()
        .unwrap()
        .starts_with("committed "));
    assert_eq!(
        git(&repo, &["log", "-1", "--format=%B"]),
        "cache the table\n\nResult: {\"status\":\"keep\",\"time_ms\":8}"
    );
    assert_eq!(kept.value["state"]["best"], json!("8"));

    // A worse run: the Lab refuses its keep and logs nothing; the discard
    // resets the tree (tracked change and untracked file).
    std::fs::write(repo.join("value.txt"), "9\n").unwrap();
    run(&lab).await;
    std::fs::write(repo.join("junk.txt"), "scratch\n").unwrap();
    let refused = lab.log(log(Status::Keep, "worse")).await.unwrap_err();
    assert!(refused.downcast_ref::<Refused>().is_some(), "{refused:#}");
    let discarded = lab.log(log(Status::Discard, "worse")).await.unwrap();
    assert_eq!(discarded.value["git"], json!("work tree reset to HEAD"));
    assert_eq!(
        std::fs::read_to_string(repo.join("value.txt")).unwrap(),
        "8\n"
    );
    assert!(!repo.join("junk.txt").exists());

    // A failing run: not passed, logged as a crash; the fourth log reaches
    // the cap, which stops the loop and turns the mode off.
    std::fs::write(repo.join("exit.txt"), "1\n").unwrap();
    let crashed = run(&lab).await;
    assert_eq!(crashed["run"]["passed"], json!(false));
    assert_eq!(crashed["exit_code"], json!(1));
    let stopped = lab
        .log(log(Status::Crash, "broke the build"))
        .await
        .unwrap();
    assert_eq!(stopped.value["stopped"], json!(true));
    assert_eq!(stopped.mode, Mode::Off);
    assert!(!repo.join("exit.txt").exists());

    // A reopen replays the log to the very same state.
    let live = lab.snapshot().await.unwrap();
    let workspace = Workspace::of(&repo).await.unwrap();
    let dir = Store::dir_of(
        &home.path().join("autoresearch"),
        &workspace.root,
        workspace.branch.as_deref(),
        true,
    );
    let (_, mut replayed) = Store::open(dir).unwrap();
    assert_eq!(replayed.snapshot().unwrap(), live);
}

/// The `autoresearch.init` host request of a real session, from a clean
/// tree that holds the harness: the init starts the loop's autonomous run
/// (its state a durable JSON document) and the reply is exact JSON. A
/// limit past `Number.MAX_SAFE_INTEGER` failed that commit after the init
/// had taken effect, so the model read a failure.
#[tokio::test]
async fn the_init_host_request_starts_the_loop_and_answers_exact_json() {
    use eukhe_ai::models::{create_models, CreateModelsOptions};
    use eukhe_ai::providers::faux::{faux_provider, RegisterFauxProviderOptions};
    use eukhe_chord::context::BACKGROUND_CONTEXT;
    use eukhe_durable::harness::types::ModelRef;

    use super::host::CONTINUATION;
    use crate::durable::goals::autonomous_state;
    use crate::durable::{open_session, HostCall, SessionConfig, SessionStorage};

    let home = tempfile::tempdir().unwrap();
    let repo_dir = tempfile::tempdir().unwrap();
    let repo = repo_dir.path().canonicalize().unwrap();
    repository(&repo);
    std::fs::write(repo.join("autoresearch.sh"), HARNESS).unwrap();
    git(&repo, &["add", "-A"]);
    git(&repo, &["commit", "-q", "-m", "harness"]);
    let faux = faux_provider(RegisterFauxProviderOptions::default());
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    let mut config = SessionConfig::new(
        home.path(),
        &repo,
        "019a0000-0000-7000-8000-0000000000a5",
        SessionStorage::Memory,
    );
    config.models = Some(models);
    config.model = Some(
        ModelRef {
            provider: "faux".to_owned(),
            model_id: "faux-1".to_owned(),
        }
        .into(),
    );
    let cx = &BACKGROUND_CONTEXT;
    let session = open_session(config, cx).await.expect("session opens");
    let init = session
        .deps()
        .host_requests
        .get("autoresearch.init")
        .expect("autoresearch.init is served");
    let reply = init(HostCall {
        data: json!({
            "name": "speedup-work-py",
            "metric": "time_ms",
            "goal": "speedup",
            "direction": "lower",
            "scope": ["value.txt"],
            "max_iterations": 3,
        }),
        cell_source_code: None,
        call: None,
    })
    .await
    .expect("autoresearch.init answers");
    eukhe_chord::json::to_json(&reply).expect("the reply is exact JSON");
    assert_eq!(reply["state"]["mode"], json!("on"));
    let autonomous = autonomous_state(session.harness(), session.root().id(), cx)
        .await
        .unwrap();
    assert_eq!(
        (autonomous.enabled, autonomous.continuation_prompt.as_str()),
        (true, CONTINUATION)
    );
    session.close(cx).await.unwrap();
}
