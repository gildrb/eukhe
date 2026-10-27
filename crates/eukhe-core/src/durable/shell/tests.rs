//! The `bash` tool under the S2 limits: its output bounded by the call's
//! truncation (whole under the opt-out), and a script past the blocking
//! budget detached as a job whose end settles it and whose kill stops it.
//! The gate's refusal texts, and the default auto set against its model
//! (`bend/approvals.bend` `default_auto`).

use std::fmt::Write as _;
use std::future::Future;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;

use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_tool_call, FauxAssistantMessageOptions, FauxResponseStep,
};
use eukhe_durable::harness::types::{OmittedAt, OmittedOutput};
use eukhe_durable::harness::{OutputLimits, Truncation};
use eukhe_durable::testing::bridge::{compare, Scenario};
use eukhe_types::pi_ai::{JsonObject, StopReason};
use eukhe_types::shell::ShellEffects;
use serde_json::{json, Value};

use super::*;
use crate::durable::jobs::{JobEnd, JobState};
use crate::durable::rlm::tests::{
    cx, entries, result_text, results, settle, submit, text, Fixture, WAIT_MS,
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

/// Answers no gated step (the scripts here have none).
struct Never;

impl Approver for Never {
    fn approve(&self, _ask: Ask) -> impl Future<Output = Answer> + Send {
        std::future::ready(Answer::Unanswered)
    }
}

/// The transcript of `script` run under `truncation`.
async fn transcript_of(script: &str, truncation: Truncation) -> (String, Option<ToolDiagnostic>) {
    let dir = tempfile::tempdir().expect("temp dir");
    let transcript = Transcript::new(BoundedOutput::in_session(
        Some(dir.path()),
        "call-1",
        truncation,
    ));
    let env = [("PATH".to_owned(), std::env::var("PATH").unwrap_or_default())];
    let paths = eukhe_types::path_policy::PathPolicy::new(
        vec![dir.path().to_path_buf()],
        Vec::new(),
        Vec::new(),
    );
    let ran = Shell::new(dir.path(), env, "bash")
        .run(
            script,
            AutoSet::new([ShellEffect::Read]),
            &paths,
            &Never,
            &transcript,
        )
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

/// Open with a short budget, `exec` in the auto set, and every settled
/// job captured.
async fn open_detaching(
    fixture: &Fixture,
) -> (
    EukheSession,
    tokio::sync::mpsc::UnboundedReceiver<JobSettled>,
) {
    std::fs::write(
        fixture.dir.path().join("agent").join("settings.json"),
        json!({
            "toolBlockingBudgetMs": BUDGET_MS,
            "shell": { "autoEffects": ["read", "exec"] },
        })
        .to_string(),
    )
    .expect("settings");
    let (settled_tx, settled) = tokio::sync::mpsc::unbounded_channel();
    let session = fixture
        .open_configured(move |config| {
            config.job_settled = Some(Arc::new(move |job| {
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

/// Each answer of the approval sink that is not a yes becomes its
/// refusal's text, and each text ends with a next step for the model.
#[test]
fn every_refusal_text_names_what_failed_and_the_next_step() {
    let next = [
        Refusal::Denied,
        Refusal::Unanswered,
        Refusal::GatewayRefused,
    ]
    .map(|refusal| RefusalText::of(refusal).next.is_empty());
    let texts = [
        ShellAnswer::Approve,
        ShellAnswer::Deny,
        ShellAnswer::Unanswered,
        ShellAnswer::GatewayRefused,
    ]
    .map(|answer| RefusalText::of_answer(answer).map(|text| text.to_string()));
    assert_eq!(
        (next, texts),
        (
            [false, false, false],
            [
                None,
                Some(
                    "the user denied it. Do not try it again unless the user asks for it."
                        .to_owned()
                ),
                Some(
                    "it needs the user's approval, and no client answered. Ask the user to attach \
a client, or to allow its effect in shell.autoEffects if that is read, write, exec, net, \
outside, protected or secret; or use read-only steps."
                        .to_owned()
                ),
                Some(
                    "the session runs only from the phone gateway, and from there a step that \
writes eukhe's protected files (its config and credentials, a .git or .eukhe dir, a PATH dir) \
never runs when the user's auto set does not already run it. Ask the user to run it from the \
eukhe TUI or the dashboard."
                        .to_owned()
                ),
            ]
        )
    );
}

/// The auto set of a session whose user sets no `shell.autoEffects`
/// against its model (`bend/approvals.bend` `default_auto`, law
/// `default_auto_is_grantable`): the effects
/// it holds, and for each of the 127 steps of one to seven effects
/// whether the gate runs it unasked.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn the_default_auto_set_is_its_model() {
    let fixture = Fixture::new();
    let session = fixture.open_configured(|_| {}).await;
    let auto = auto_set(&session.deps().settings);
    let mut events = "d\n".to_owned();
    let mut transcript = ShellEffect::ALL
        .into_iter()
        .filter(|&effect| auto.allows(ShellEffects::of(&[effect])))
        .fold("d".to_owned(), |mut line, effect| {
            write!(line, " {}", effect.code()).unwrap();
            line
        });
    transcript.push('\n');
    for mask in 1u8..1 << ShellEffect::ALL.len() {
        let effects: Vec<ShellEffect> = ShellEffect::ALL
            .into_iter()
            .filter(|&effect| mask & 1 << effect.code() != 0)
            .collect();
        events.push('a');
        for effect in &effects {
            write!(events, " {}", effect.code()).unwrap();
        }
        events.push('\n');
        let gated = if auto.allows(ShellEffects::of(&effects)) {
            "unasked"
        } else {
            "asks"
        };
        writeln!(transcript, "a {gated}").unwrap();
    }
    compare(
        "bridge/bridge_approvals.bend",
        [Scenario {
            name: "the default auto set".to_owned(),
            events,
            transcript,
        }],
    );
    session.close(cx()).await.expect("close");
}

/// Regression: the default auto set held only read, write, exec and net,
/// so in a session whose user set none, a write outside the workspace
/// asked, and a subagent writing its notes to /tmp stopped every turn
/// for a yes. Now every effect runs unasked: with no client
/// to answer, the whole script runs.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn with_no_auto_set_a_write_outside_the_workspace_runs_unasked() {
    let fixture = Fixture::new();
    fixture.faux.set_responses(vec![
        bash(
            "b1",
            "echo one > one.txt\nsh -c 'echo two > two.txt'\necho three > ../three.txt\necho four > four.txt",
        ),
        text("done"),
    ]);
    let session = fixture
        .open_configured(|config| config.shell_approval = None)
        .await;
    let id = submit(&session, "go").await;
    tokio::time::timeout(Duration::from_millis(WAIT_MS), settle(&session, id))
        .await
        .expect("the turn ends");
    let work = fixture.dir.path().join("work");
    let read = |path: PathBuf| std::fs::read_to_string(path).ok();
    assert_eq!(
        (
            results(&entries(&session).await)
                .iter()
                .map(result_text)
                .collect::<Vec<_>>(),
            read(work.join("one.txt")),
            read(work.join("two.txt")),
            read(fixture.dir.path().join("three.txt")),
            read(work.join("four.txt")),
        ),
        (
            vec![
                "$ echo one >one.txt\n$ sh -c 'echo two > two.txt'\n$ echo three >../three.txt\n$ \
echo four >four.txt\n"
                    .to_owned()
            ],
            Some("one\n".to_owned()),
            Some("two\n".to_owned()),
            Some("three\n".to_owned()),
            Some("four\n".to_owned()),
        )
    );
    session.close(cx()).await.expect("close");
}
