//! The `bash` tool under the S2 limits: its output bounded by the call's
//! truncation (whole under the opt-out), and a script past the blocking
//! budget detached as a job whose end settles it and whose kill stops it.
//! Every step runs unasked; a step that writes an own path is refused
//! and stops the script. A crash mid-script never runs it again
//! (`effect_once`).

use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;

use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_tool_call, FauxAssistantMessageOptions, FauxResponseStep,
};
use eukhe_durable::harness::types::{OmittedAt, OmittedOutput};
use eukhe_durable::harness::{OutputLimits, Truncation};
use eukhe_durable::types::SubmissionStatus;
use eukhe_types::job::JobSettled;
use eukhe_types::pi_ai::{JsonObject, StopReason};
use serde_json::{json, Value};

use super::*;
use crate::durable::jobs::{JobEnd, JobState};
use crate::durable::rlm::tests::{
    cx, entries, result_text, results, settle, submit, text, wait_for, Fixture, WAIT_MS,
};
use crate::durable::EukheSession;

/// A model step that calls `bash` with `script`.
fn bash(call_id: &str, script: &str) -> FauxResponseStep {
    let Value::Object(arguments) = json!({ "script": script }) else {
        unreachable!("an object literal");
    };
    faux_assistant_message(
        vec![faux_tool_call(
            "bash",
            arguments.into_iter().collect::<JsonObject>(),
            Some(call_id.to_owned()),
        )],
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )
    .into()
}

/// The transcript of `script` run under `truncation`.
async fn transcript_of(script: &str, truncation: Truncation) -> (String, Option<ToolDiagnostic>) {
    let dir = tempfile::tempdir().expect("temp dir");
    let transcript = Transcript::new(
        BoundedOutput::in_session(Some(dir.path()), "call-1", truncation),
        None,
    );
    let env = [("PATH".to_owned(), std::env::var("PATH").unwrap_or_default())];
    let paths = eukhe_types::path_policy::PathPolicy::new(
        vec![dir.path().to_path_buf()],
        Vec::new(),
        Vec::new(),
    );
    let ran = Shell::new(dir.path(), env, "bash")
        .run(script, &paths, &eukhe_shell::Unasked, &transcript)
        .await;
    assert_eq!(ran.end, End::Finished { status: 0 });
    transcript.projection()
}

/// Regression: the output goes through the call's truncation. Under the
/// cap the projection keeps its head and tail and the diagnostic counts
/// every dropped byte; under the opt-out every byte is kept.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn the_output_obeys_the_calls_truncation_and_its_opt_out() {
    let script = "yes | head -n 30000";
    let whole = format!(
        "$ yes\n$ head -n 30000\n{}[step 0 exited 141]\n",
        "y\n".repeat(30_000)
    );
    assert_eq!(
        transcript_of(script, Truncation::Off).await,
        (whole.clone(), None)
    );
    let limits = OutputLimits {
        max_bytes: 1_000,
        max_lines: 100,
        ..OutputLimits::default()
    };
    let (kept, diagnostic) = transcript_of(script, Truncation::On(limits)).await;
    let diagnostic = diagnostic.expect("an output_bounded diagnostic");
    let omitted = diagnostic.omitted.expect("the omitted bytes");
    assert_eq!(
        (
            diagnostic.code.as_deref(),
            kept.len() <= limits.max_bytes,
            whole.len() as u64 - kept.len() as u64,
            whole.starts_with(&kept[..20]),
            whole.ends_with("y\ny\n[step 0 exited 141]\n")
                && kept.ends_with("y\n[step 0 exited 141]\n"),
        ),
        (Some("output_bounded"), true, omitted.bytes, true, true)
    );
    assert!(
        matches!(
            omitted,
            OmittedOutput {
                at: OmittedAt::AfterLine(_),
                ..
            }
        ),
        "{omitted:?}"
    );
}

/// The blocking budget of the detach tests.
const BUDGET_MS: u64 = 400;

/// Open with a short budget and every settled job captured.
async fn open_detaching(
    fixture: &Fixture,
) -> (
    EukheSession,
    tokio::sync::mpsc::UnboundedReceiver<JobSettled>,
) {
    std::fs::write(
        fixture.dir.path().join("agent").join("settings.json"),
        json!({ "toolBlockingBudgetMs": BUDGET_MS }).to_string(),
    )
    .expect("settings");
    let (settled_tx, settled) = tokio::sync::mpsc::unbounded_channel();
    let session = fixture
        .open_configured(move |config| {
            config.job_settled = Some(Arc::new(move |job, _admitted| {
                let _closed_receiver_ends_the_test = settled_tx.send(job);
            }));
        })
        .await;
    (session, settled)
}

/// Run one `bash` call that detaches: its result text, its job, and the
/// job's id.
async fn detach(session: &EukheSession) -> (String, Value, Job) {
    let id = submit(session, "go").await;
    tokio::time::timeout(Duration::from_millis(WAIT_MS), settle(session, id))
        .await
        .expect("the turn ends while the script runs");
    let first = results(&entries(session).await);
    assert_eq!(first.len(), 1, "{first:?}");
    let details: Value = first[0].details.clone().expect("details");
    let job_id = details["job"]["id"].as_str().expect("a job id").to_owned();
    let job = session
        .deps()
        .jobs
        .get(&job_id)
        .expect("the job is in the table");
    (result_text(&first[0]), details, job)
}

/// Regression: a script past the blocking budget does not block the call;
/// the call settles `detached` with the output so far, the script runs
/// on as a job, and its end settles the job with its whole output.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_script_past_the_budget_detaches_and_its_end_settles_the_job() {
    let fixture = Fixture::new();
    fixture.faux.set_responses(vec![
        bash("b1", "echo started; sleep 2; echo finished"),
        text("the script runs on as a job"),
    ]);
    let (session, mut settled) = open_detaching(&fixture).await;
    let (partial, details, job) = detach(&session).await;
    // The output so far, then the harness's rendering of the `detached`
    // diagnostic, which names the job.
    let (output, harness) = partial.split_once('|').expect("the diagnostics part");
    assert_eq!(
        (
            output,
            harness.contains(&format!("[job-settled job:{}]", job.id())),
            &details["status"],
            &details["job"]["kind"],
            job.kind()
        ),
        (
            "$ echo started\nstarted\n$ sleep 2\n",
            true,
            &json!("detached"),
            &json!("shell"),
            JobKind::Shell
        )
    );
    let settled = tokio::time::timeout(Duration::from_secs(20), settled.recv())
        .await
        .expect("the job settles when the script ends")
        .expect("a settled job");
    let whole = "$ echo started\nstarted\n$ sleep 2\n$ echo finished\nfinished\n";
    assert_eq!(
        settled,
        JobSettled::Shell {
            job: job.id().clone(),
            status: CellStatus::Ok,
            output: whole.to_owned(),
        }
    );
    assert_eq!(job.ended().await, JobEnd::Exited(0));
    // The job counts every byte of the run, the bytes from before the
    // detach too.
    assert_eq!(
        job.state(),
        JobState::Ended {
            kept: whole.len() as u64,
            dropped: 0,
            end: JobEnd::Exited(0),
        }
    );
    session.close(cx()).await.expect("close");
}

/// Regression: the model edits while its check runs on as a job. The
/// job's settled output names the paths written after the detach, so the
/// check's result is not read as judging the tree as it stands.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_job_names_the_paths_written_while_it_ran() {
    let fixture = Fixture::new();
    let work = fixture.dir.path().join("work");
    std::fs::write(work.join("lib.rs"), "pub fn a() {}\n").expect("lib.rs");
    let gate = fixture.dir.path().join("gate");
    let made = std::process::Command::new("mkfifo")
        .arg(&gate)
        .status()
        .expect("mkfifo");
    assert!(made.success(), "mkfifo {}", gate.display());
    let step = format!("cat {} >/dev/null", gate.display());
    let script = format!("sh -c \"{step}\"");
    fixture.faux.set_responses(vec![
        bash("b1", &script),
        text("the check runs on as a job"),
    ]);
    let (session, mut settled) = open_detaching(&fixture).await;
    let (_, _, job) = detach(&session).await;
    // The edit lands while the script holds the gate open; the gate's
    // byte ends the script.
    tokio::task::spawn_blocking(move || {
        let mut opened = std::fs::OpenOptions::new()
            .write(true)
            .open(&gate)
            .expect("the gate");
        std::fs::write(work.join("lib.rs"), "pub fn a() {}\npub fn b() {}\n").expect("the edit");
        std::io::Write::write_all(&mut opened, b"go").expect("the gate's byte");
    })
    .await
    .expect("the edit's task");
    let settled = tokio::time::timeout(Duration::from_secs(20), settled.recv())
        .await
        .expect("the job settles when the script ends")
        .expect("a settled job");
    assert_eq!(
        settled,
        JobSettled::Shell {
            job: job.id().clone(),
            status: CellStatus::Ok,
            output: format!(
                "$ sh -c '{step}'\n[The workspace changed while the job ran (1 path: lib.rs): \
                 its result judged no single tree state.]\n"
            ),
        }
    );
    session.close(cx()).await.expect("close");
}

/// The kill of a detached script's job stops it and every process it
/// started; the job settles killed.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn the_kill_of_a_detached_script_stops_it() {
    let fixture = Fixture::new();
    fixture.faux.set_responses(vec![
        bash("b1", "echo started; sleep 30; echo late"),
        text("the script runs on as a job"),
    ]);
    let (session, mut settled) = open_detaching(&fixture).await;
    let (_, _, job) = detach(&session).await;
    job.kill();
    let settled = tokio::time::timeout(Duration::from_secs(10), settled.recv())
        .await
        .expect("the killed job settles at once")
        .expect("a settled job");
    assert_eq!(
        settled,
        JobSettled::Shell {
            job: job.id().clone(),
            status: CellStatus::Killed,
            output:
                "$ echo started\nstarted\n$ sleep 30\n[killed: the job's kill stopped the script]\n"
                    .to_owned(),
        }
    );
    assert_eq!(job.ended().await, JobEnd::Killed);
    session.close(cx()).await.expect("close");
}

/// Speculation, then effect (`effect_once` in `laws/tool_call.bend`): a
/// crash while a `bash` call runs (an unsafe tool: a step may have
/// written) settles it `interrupted` after the reopen, and its script
/// never runs again.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_resume_never_runs_a_bash_call_a_crash_interrupted_again() {
    let fixture = Fixture::new();
    // A budget past the test: the call blocks, it never detaches as a job.
    std::fs::write(
        fixture.dir.path().join("agent").join("settings.json"),
        json!({ "toolBlockingBudgetMs": WAIT_MS }).to_string(),
    )
    .expect("settings");
    fixture
        .faux
        .set_responses(vec![bash("b1", "echo run >> runs; sleep 60"), text("done")]);
    let runs = fixture.dir.path().join("work").join("runs");
    let session = fixture.open_configured(|_| {}).await;
    let id = submit(&session, "go").await;
    wait_for("the script's first step", || {
        let ran = std::fs::read_to_string(&runs).is_ok_and(|text| text == "run\n");
        async move { ran }
    })
    .await;
    // The worker dies mid-script: nothing more commits.
    session.harness().close(cx()).await.expect("harness close");
    drop(session);

    let session = fixture.open_configured(|_| {}).await;
    assert_eq!(settle(&session, id).await, SubmissionStatus::Done);
    let all = results(&entries(&session).await);
    assert_eq!(
        (
            all.len(),
            result_text(&all[0]),
            std::fs::read_to_string(&runs).expect("the script's file")
        ),
        (
            1,
            "<harness>\n[error] Tool bash was interrupted and may have partially run. Check the state it changes (files, processes, jobs) before you run it again.\n</harness>".to_owned(),
            "run\n".to_owned()
        )
    );
    session.close(cx()).await.expect("close");
}

/// Every step runs unasked, a write outside the workspace too; a step
/// that writes an own path (here eukhe's settings) is refused, and it and
/// every step after it do not run. The model is told the path and why.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn every_step_runs_unasked_and_an_own_write_stops_the_script() {
    let fixture = Fixture::new();
    fixture.faux.set_responses(vec![
        bash(
            "b1",
            "echo one > one.txt\nsh -c 'echo two > two.txt'\necho three > ../three.txt\necho x > ../agent/settings.json\necho four > four.txt",
        ),
        text("done"),
    ]);
    let session = fixture.open_configured(|_| {}).await;
    let settings = fixture.dir.path().join("agent").join("settings.json");
    let settings_before = std::fs::read_to_string(&settings).ok();
    let id = submit(&session, "go").await;
    tokio::time::timeout(Duration::from_millis(WAIT_MS), settle(&session, id))
        .await
        .expect("the turn ends");
    let work = fixture.dir.path().join("work");
    let read = |path: PathBuf| std::fs::read_to_string(path).ok();
    let own = std::fs::canonicalize(fixture.dir.path().join("agent"))
        .expect("the agent dir")
        .join("settings.json");
    assert_eq!(
        (
            results(&entries(&session).await)
                .iter()
                .map(result_text)
                .collect::<Vec<_>>(),
            read(work.join("one.txt")),
            read(work.join("two.txt")),
            read(fixture.dir.path().join("three.txt")),
            read(settings) == settings_before,
            read(work.join("four.txt")),
        ),
        (
            vec![format!(
                "$ echo one >one.txt\n$ sh -c 'echo two > two.txt'\n$ echo three >../three.txt\n\
[stopped at step 3 (read+write+protected): `echo x >../agent/settings.json` and the steps after it \
did not run: {} is part of eukhe's own config and credentials; no agent may write it.]\n",
                own.display()
            )],
            Some("one\n".to_owned()),
            Some("two\n".to_owned()),
            Some("three\n".to_owned()),
            true,
            None,
        )
    );
    session.close(cx()).await.expect("close");
}

#[test]
fn a_script_names_git_by_the_word_or_a_path_ending_in_it() {
    let scripts = [
        "git status",
        "cd src && /usr/bin/git diff",
        "echo x; git",
        "ls .git",
        "git-lfs ls-files",
        "echo digit",
    ];
    assert_eq!(
        scripts.map(names_git),
        [true, true, true, false, false, false]
    );
}

/// Regression: an isolated child's copy had no repository, so `git
/// status` failed there. The first script that names git makes it, from
/// the copy as the child found it: an edit made before still shows.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn the_first_script_naming_git_in_a_childs_copy_shows_the_childs_changes() {
    let fixture = Fixture::new();
    let parent = fixture.dir.path().join("work");
    std::fs::write(parent.join("a.txt"), "a0\n").expect("parent file");
    let workspace = ChildWorkspace::at(fixture.dir.path().join("ws"));
    workspace.create(&parent, &[]).await.expect("child copy");
    let tree = workspace.tree();
    std::fs::write(tree.join("a.txt"), "a-child\n").expect("child edit");
    let before = tree.join(".git").exists();
    fixture.faux.set_responses(vec![
        bash("b1", "echo x"),
        bash("b2", "git status --porcelain"),
        text("done"),
    ]);
    let session = fixture
        .open_configured(|config| config.cwd = tree.clone())
        .await;
    let id = submit(&session, "go").await;
    tokio::time::timeout(Duration::from_millis(WAIT_MS), settle(&session, id))
        .await
        .expect("the turn ends");
    let texts: Vec<String> = results(&entries(&session).await)
        .iter()
        .map(result_text)
        .collect();
    assert_eq!(
        (
            before,
            texts.first().cloned(),
            texts
                .get(1)
                .is_some_and(|text| text.ends_with("\n M a.txt\n")),
            tree.join(".git").is_dir(),
        ),
        (false, Some("$ echo x\nx\n".to_owned()), true, true),
        "{texts:?}"
    );
    session.close(cx()).await.expect("close");
}
