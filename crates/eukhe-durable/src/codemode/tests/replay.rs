//! Scripts that survive a crash or a close/reopen: the rerun replays the
//! journal without running finished nested calls again and reaches the same
//! result; a changed sandbox, module version, passed deadline, or a script
//! that takes another path ends the call with an error.

use std::path::Path;
use std::sync::Arc;

use eukhe_chord::json::{from_json, to_json, JsonValue};

use super::{
    add_tool, bump, codemode_result, counter, options, queue_script, sandbox, setup, setup_with,
    text, Runs, Setup,
};
use crate::codemode::sandbox::{CodemodeSandbox, CodemodeSandboxOptions};
use crate::codemode::{
    create_codemode_extension, CodemodeJournal, CodemodeRunState, CODEMODE_JOURNAL_DOC,
    CODEMODE_RUN_DOC,
};
use crate::harness::tests::chat_support::{open_chat, ChatSetup, OpenChat};
use crate::harness::tests::support::context;
use crate::harness::tests::task_support::{deferred, Deferred};
use crate::harness::tool::tests::nested_support::{
    hang, is_nested, nested_tasks, open_sqlite, settle, sqlite_path, submit_go, text_result,
    tool_tasks,
};
use crate::harness::tool::tests::support::tool_with;
use crate::harness::types::ToolReplay;
use crate::harness::Harness;
use crate::session::tests::support::ControlledStorage;
use crate::types::{Storage, SubmissionId, SubmissionStatus, TaskId};

/// A script whose first call finishes and whose second blocks the first time
/// it runs. `Math.random()` and `Date.now()` reach the blocking call's
/// arguments, so a replay that saw other values would make another call.
const SCRIPT: &str = r#"const r = Math.random();
const t = Date.now();
const a = await tools.echo({ text: "one" });
const b = await tools.block({ r, t, n: new Date(t).getUTCHours() });
console.log("got", a);
return { a, b };"#;

/// Install `block`: replay-safe; its first run resolves `started` and runs
/// until its call is aborted; later runs return `unblocked`.
fn add_block(chat: &ChatSetup, runs: &Runs) -> Deferred {
    let started = deferred::<()>();
    let calls = counter();
    let (runs, signal) = (runs.clone(), started.clone());
    let tool = tool_with(
        "block",
        move |args, _, cx| {
            runs.push(format!("block:{args}"));
            let first = bump(&calls) == 1;
            let signal = signal.clone();
            async move {
                if first {
                    signal.resolve(());
                    return Err(hang(&cx).await);
                }
                Ok(text_result("unblocked"))
            }
        },
        |tool| tool.replay = Some(ToolReplay::Safe),
    );
    crate::harness::tests::support::add_tool(&chat.registry, tool, None).unwrap();
    started
}

/// The test setup with `block` installed.
fn blocking(setup: Setup) -> (Setup, Deferred) {
    let started = add_block(&setup.chat, &setup.runs);
    (setup, started)
}

/// The code mode call's task: the only tool task the model made.
async fn codemode_task(harness: &Harness) -> TaskId {
    tool_tasks(harness)
        .await
        .into_iter()
        .find(|record| !is_nested(record))
        .expect("the code mode task")
        .id
}

/// Change the code mode call's documents while the Harness does not run
/// tasks.
async fn tamper(
    harness: &Harness,
    change: impl FnOnce(&mut CodemodeRunState, &mut CodemodeJournal) + Send + 'static,
) {
    let task = codemode_task(harness).await;
    harness
        .commit(
            move |tx| async move {
                let run = tx.doc(&CODEMODE_RUN_DOC, task).await?;
                let journal = tx.doc(&CODEMODE_JOURNAL_DOC, task).await?;
                let mut run_state: CodemodeRunState = from_json(&run.value()?)?;
                let mut journal_state: CodemodeJournal = from_json(&journal.value()?)?;
                change(&mut run_state, &mut journal_state);
                run.set("start", to_json(&run_state.start)?)?;
                journal.set("entries", to_json(&journal_state.entries)?)?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
}

/// Run [`SCRIPT`] until `block` runs, then close the Harness.
async fn interrupted(setup: &Setup, started: &Deferred, path: &Path) -> SubmissionId {
    queue_script(&setup.chat, SCRIPT);
    let opened = open_sqlite(path, &setup.chat).await;
    let id = submit_go(&opened.root).await;
    started.wait().await;
    opened.harness.close(context()).await.unwrap();
    id
}

/// Reopen, let the call finish, and return its result.
async fn resumed(
    setup: &Setup,
    path: &Path,
    id: SubmissionId,
) -> (OpenChat, eukhe_types::pi_ai::ToolResultMessage) {
    let opened = open_sqlite(path, &setup.chat).await;
    opened.harness.resume().unwrap();
    assert_eq!(settle(&opened.harness, id).await, SubmissionStatus::Done);
    let result = codemode_result(&opened).await;
    (opened, result)
}

/// The two runs of `block` had the same arguments: the replay saw the same
/// clock and randomness.
fn assert_blocked_twice_alike(runs: &[String]) {
    let blocks: Vec<&String> = runs
        .iter()
        .filter(|run| run.starts_with("block:"))
        .collect();
    assert_eq!(blocks.len(), 2, "{runs:?}");
    assert_eq!(blocks[0], blocks[1]);
}

/// What the script returns when nothing interrupts it.
async fn uninterrupted() -> String {
    let setup = setup();
    let runs = setup.runs.clone();
    add_tool(
        &setup.chat,
        &runs,
        "block",
        |_| text_result("unblocked"),
        |_| {},
    );
    text(&super::run_script(&setup, SCRIPT).await)
}

#[tokio::test]
async fn a_script_killed_mid_call_replays_to_the_same_result_without_rerunning_finished_calls() {
    let (setup, started) = blocking(setup());
    let storage = ControlledStorage::new();
    queue_script(&setup.chat, SCRIPT);
    let crashed = open_chat(Arc::clone(&storage) as Arc<dyn Storage>, &setup.chat, None)
        .await
        .unwrap();
    let id = submit_go(&crashed.root).await;
    started.wait().await;
    // The worker dies: its Harness is abandoned without close, its script
    // and blocked call frozen. A new Harness opens the same storage.
    let recovered = open_chat(Arc::clone(&storage) as Arc<dyn Storage>, &setup.chat, None)
        .await
        .unwrap();
    recovered.harness.resume().unwrap();
    assert_eq!(settle(&recovered.harness, id).await, SubmissionStatus::Done);
    let result = codemode_result(&recovered).await;
    assert!(!result.is_error, "{}", text(&result));
    assert_eq!(text(&result), uninterrupted().await);
    let runs = setup.runs.all();
    assert_eq!(
        runs.iter().filter(|run| run.starts_with("echo:")).count(),
        1,
        "{runs:?}"
    );
    assert_blocked_twice_alike(&runs);
    // No nested call was made again: `c1` and `c2` only.
    assert_eq!(nested_tasks(&recovered.harness).await.len(), 2);
    recovered.harness.close(context()).await.unwrap();
    drop(crashed);
}

#[tokio::test]
async fn a_script_interrupted_by_close_resumes_after_reopen() {
    let (setup, started) = blocking(setup());
    let (_directory, path) = sqlite_path("pi-durable-codemode-");
    let id = interrupted(&setup, &started, &path).await;
    let (opened, result) = resumed(&setup, &path, id).await;
    assert!(!result.is_error, "{}", text(&result));
    assert_eq!(text(&result), uninterrupted().await);
    let runs = setup.runs.all();
    assert_eq!(
        runs.iter().filter(|run| run.starts_with("echo:")).count(),
        1
    );
    assert_blocked_twice_alike(&runs);
    // The call's documents retired with its task.
    let task = codemode_task(&opened.harness).await;
    let run = opened
        .harness
        .snapshot(&CODEMODE_RUN_DOC, task, context())
        .await
        .unwrap();
    let journal = opened
        .harness
        .snapshot(&CODEMODE_JOURNAL_DOC, task, context())
        .await
        .unwrap();
    assert_eq!((run, journal), (None, None));
    opened.harness.close(context()).await.unwrap();
}

/// Interrupt [`SCRIPT`], change its documents with `change`, and return the
/// rerun's result text.
async fn tampered(
    setup: &Setup,
    started: &Deferred,
    change: impl FnOnce(&mut CodemodeRunState, &mut CodemodeJournal) + Send + 'static,
) -> eukhe_types::pi_ai::ToolResultMessage {
    let (_directory, path) = sqlite_path("pi-durable-codemode-");
    let id = interrupted(setup, started, &path).await;
    let opened = open_sqlite(&path, &setup.chat).await;
    tamper(&opened.harness, change).await;
    opened.harness.close(context()).await.unwrap();
    let (opened, result) = resumed(setup, &path, id).await;
    opened.harness.close(context()).await.unwrap();
    result
}

#[tokio::test]
async fn a_replay_that_issues_other_calls_than_the_journal_ends_with_an_error() {
    let (setup, started) = blocking(setup());
    let result = tampered(&setup, &started, |_, journal| {
        journal.entries[0].issued_after = Some(5);
    })
    .await;
    assert!(result.is_error);
    assert_eq!(
        text(&result),
        "The script took a different path when resumed after a restart: after result 1 it had made 2 calls, where it had made 5"
    );
    assert_eq!(
        setup
            .runs
            .all()
            .iter()
            .filter(|run| run.starts_with("echo:"))
            .count(),
        1
    );
}

#[tokio::test]
async fn a_replay_whose_call_differs_from_a_journaled_global_ends_with_an_error() {
    let (setup, started) = blocking(setup());
    let result = tampered(&setup, &started, |_, journal| {
        journal.entries[0].global = Some(crate::codemode::JournalGlobal {
            name: "searchTools".to_owned(),
            args: Some(JsonValue::parse(r#"["x"]"#).unwrap()),
            outcome: crate::codemode::CodemodeOutcome::Ok { value: None },
        });
    })
    .await;
    assert!(result.is_error);
    assert_eq!(
        text(&result),
        r#"The script took a different path when resumed after a restart: call 1 is tools.echo({"text":"one"}), but was a call to searchTools"#
    );
}

#[tokio::test]
async fn a_changed_module_version_or_passed_deadline_refuses_the_replay() {
    let (setup, started) = blocking(setup());
    let result = tampered(&setup, &started, |run, _| {
        run.start.as_mut().unwrap().version = 0;
    })
    .await;
    assert_eq!(
        (result.is_error, text(&result)),
        (
            true,
            format!(
                "The script cannot resume: it started under code mode version 0, this is {}.",
                crate::codemode::CODEMODE_MODULE_VERSION
            )
        )
    );

    let (setup, started) = blocking(super::setup());
    let result = tampered(&setup, &started, |run, _| {
        run.start.as_mut().unwrap().deadline = Some(1.0);
    })
    .await;
    assert_eq!(
        (result.is_error, text(&result)),
        (
            true,
            "Script timed out: its deadline passed while it was interrupted.".to_owned()
        )
    );
    assert_eq!(
        setup
            .runs
            .all()
            .iter()
            .filter(|run| run.starts_with("echo:"))
            .count(),
        1
    );
}

#[tokio::test]
async fn a_changed_sandbox_fingerprint_refuses_the_replay() {
    let (setup, started) = blocking(setup());
    let (_directory, path) = sqlite_path("pi-durable-codemode-");
    let id = interrupted(&setup, &started, &path).await;
    let before = sandbox().fingerprint().to_owned();
    let changed = CodemodeSandbox::new(CodemodeSandboxOptions {
        memory_limit_bytes: Some(64 * 1024 * 1024),
    });
    let after = changed.fingerprint().to_owned();
    setup
        .chat
        .registry
        .install(create_codemode_extension(options(changed)))
        .unwrap();
    let (opened, result) = resumed(&setup, &path, id).await;
    assert_eq!(
        (result.is_error, text(&result)),
        (
            true,
            format!("The script cannot resume: the sandbox changed since it started ({before} -> {after}).")
        )
    );
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn a_global_is_answered_from_the_journal_on_replay() {
    let calls = counter();
    let seen = Arc::clone(&calls);
    let global = crate::codemode::CodemodeGlobal {
        name: "ticket".to_owned(),
        spread: false,
        execute: Arc::new(move |_, _, _| {
            let n = bump(&seen);
            Box::pin(async move { Ok(Some(JsonValue::from(format!("ticket-{n}")))) })
        }),
    };
    let (setup, started) = blocking(setup_with(crate::codemode::CodemodeToolOptions {
        globals: vec![global],
        ..options(sandbox())
    }));
    let (_directory, path) = sqlite_path("pi-durable-codemode-");
    queue_script(
        &setup.chat,
        r"const t = await ticket();
const b = await tools.block({ t });
return [t, b];",
    );
    let opened = open_sqlite(&path, &setup.chat).await;
    let id = submit_go(&opened.root).await;
    started.wait().await;
    opened.harness.close(context()).await.unwrap();
    let (opened, result) = resumed(&setup, &path, id).await;
    assert_eq!(
        text(&result).lines().last(),
        Some(r#"["ticket-1","unblocked"]"#)
    );
    assert_eq!(calls.load(std::sync::atomic::Ordering::SeqCst), 1);
    opened.harness.close(context()).await.unwrap();
}
