//! The watch's clock (rule H5): a child that shows no progress is stopped
//! and reported stalled, polls that keep failing report it unreachable,
//! a child that keeps progressing outlives the stall budget, and a
//! reopened parent polls its child at once.

use super::*;
use crate::durable::children::task::ChildCheckpoint;
use crate::durable::children::watch::{Vigil, CHILD_POLL_FAILURES};
use eukhe_types::input_origin::ChildFailure;

/// A Harness clock that leaps 40 s on every read: each pause between
/// polls (at most 32 s) has passed by the next read, so the polls run back
/// to back while the clock runs far past the stall budget.
fn leaping(setup: &mut Setup) {
    let ticks = Arc::new(std::sync::atomic::AtomicU32::new(0));
    setup.now = Some(Arc::new(move || {
        f64::from(ticks.fetch_add(1, Ordering::SeqCst)) * 40_000.0
    }));
}

/// The cancels and stops the host received.
fn cancel_keys(host: &FakeHost) -> Vec<String> {
    lock(&host.state)
        .cancels
        .iter()
        .map(|cancel| cancel.idempotency_key.clone())
        .collect()
}

/// What the watch sends a stuck child: its run aborted, then its agent
/// stopped (the regression: the agent was left running).
fn stopped(row: &ChildRow) -> [String; 2] {
    [
        format!("rlm:{}:cancel", row.task_id),
        format!("rlm:{}:stop", row.task_id),
    ]
}

/// Wait for the child's report to reach the parent; its row.
async fn reported(opened: &Opened, row: &ChildRow) -> ChildRow {
    eventually(|| async {
        row_of(&opened.harness, row.task_id)
            .await
            .is_some_and(|row| row.status == ChildStatus::Error)
    })
    .await;
    opened
        .harness
        .wait_for_task(TaskId::<Value>::from_number(row.task_id), cx())
        .await
        .unwrap();
    opened.root.wait_for_idle(cx()).await.unwrap();
    row_of(&opened.harness, row.task_id).await.unwrap()
}

/// Regression (H5): a child that is alive but shows no progress (its
/// token never changes) is stopped and reported stalled once
/// `subagentStallMs` (default 10 min) passed. The old watch polled it
/// forever and the parent never heard of it again.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_hung_child_is_stopped_and_reported_stalled() {
    let mut setup = setup();
    leaping(&mut setup);
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let row = spawn_child(&opened, &setup).await;
    lock(&host.state).tokens.insert(row.session_id.clone(), 7);
    setup.faux.append_responses(vec![answer("noted")]);
    host.settle(&row.session_id, RlmChildRunState::Running, None);

    let stalled = reported(&opened, &row).await;
    let error = "RLM child showed no progress for 600 s and was stopped";
    assert_eq!(stalled.error.as_deref(), Some(error));
    assert_eq!(stalled.progress, Some(7));
    assert_eq!(
        user_texts(&opened.root, "[child-").await,
        [format!(
            "[child-failed: stalled child:{}]\n\n{error}",
            row.session_name
        )]
    );
    assert_eq!(cancel_keys(&host), stopped(&row));
    assert!(lock(&setup.reports).is_empty());
    opened.harness.close(cx()).await.unwrap();
}

/// Regression (H5): a child whose polls fail `CHILD_POLL_FAILURES` times
/// in a row (its worker alive but not answering) is stopped and reported
/// unreachable. The old watch counted no failed poll and polled forever.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn failing_polls_report_the_child_unreachable() {
    let mut setup = setup();
    leaping(&mut setup);
    // A stall budget the failed polls never reach.
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(
        dir.path().join("settings.json"),
        json!({ "subagentStallMs": 1_000_000_000_u64 }).to_string(),
    )
    .unwrap();
    setup.settings = Arc::new(EukheSettings::new(dir.path(), dir.path()));
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let row = spawn_child(&opened, &setup).await;
    setup.faux.append_responses(vec![answer("noted")]);
    lock(&host.state).failing_waits = usize::try_from(CHILD_POLL_FAILURES).unwrap();
    host.changed.send_modify(|value| *value += 1);

    let unreachable = reported(&opened, &row).await;
    let error = format!(
        "RLM child could not be reached in {CHILD_POLL_FAILURES} polls in a row and was stopped: \
         Session worker is overloaded; retry later"
    );
    assert_eq!(unreachable.error.as_deref(), Some(&*error));
    assert_eq!(
        user_texts(&opened.root, "[child-").await,
        [format!(
            "[child-failed: unreachable child:{}]\n\n{error}",
            row.session_name
        )]
    );
    assert_eq!(
        lock(&host.state).polls,
        usize::try_from(CHILD_POLL_FAILURES).unwrap()
    );
    assert_eq!(cancel_keys(&host), stopped(&row));
    opened.harness.close(cx()).await.unwrap();
}

/// A child that keeps progressing (a new token at every poll) is never
/// stalled, however long it runs: it reports normally once it answers.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_progressing_child_outlives_the_stall_budget() {
    let mut setup = setup();
    leaping(&mut setup);
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let row = spawn_child(&opened, &setup).await;
    {
        let mut fake = lock(&host.state);
        fake.tokens.insert(row.session_id.clone(), 0);
        fake.ticking = true;
    }
    host.settle(&row.session_id, RlmChildRunState::Running, None);
    // 40 polls, each 80 s of Harness time or more: far past 10 min.
    eventually(|| async { lock(&host.state).polls >= 40 }).await;
    let watched = row_of(&opened.harness, row.task_id).await.unwrap();
    assert_eq!(
        (watched.status, watched.error),
        (ChildStatus::Running, None)
    );
    assert_eq!(
        user_texts(&opened.root, "[child-").await,
        Vec::<String>::new()
    );

    setup.faux.append_responses(vec![answer("thanks")]);
    host.settle(
        &row.session_id,
        RlmChildRunState::Answered {
            answer_preview: Some("done".to_owned()),
        },
        None,
    );
    opened
        .harness
        .wait_for_task(TaskId::<Value>::from_number(row.task_id), cx())
        .await
        .unwrap();
    opened.root.wait_for_idle(cx()).await.unwrap();
    assert_eq!(
        user_texts(&opened.root, "[child-").await,
        [format!(
            "[child-exited: no-reply child:{}]\n\nLast assistant text: done",
            row.session_name
        )]
    );
    assert!(cancel_keys(&host).is_empty());
    opened.harness.close(cx()).await.unwrap();
}

/// A paused child (its tree paused, `pause_workers`) shows no progress,
/// but it owes none: the time its watch sees it paused is not the stall
/// clock's, so it is never reported stalled; once it runs again and
/// answers, it reports normally.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_paused_child_is_not_stalled() {
    let mut setup = setup();
    leaping(&mut setup);
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let row = spawn_child(&opened, &setup).await;
    {
        let mut fake = lock(&host.state);
        fake.tokens.insert(row.session_id.clone(), 7);
        fake.paused.insert(row.session_id.clone());
    }
    host.settle(&row.session_id, RlmChildRunState::Running, None);
    // 40 polls, each 80 s of Harness time or more: far past 10 min.
    eventually(|| async { lock(&host.state).polls >= 40 }).await;
    let watched = row_of(&opened.harness, row.task_id).await.unwrap();
    assert_eq!(
        (watched.status, watched.error),
        (ChildStatus::Running, None)
    );
    assert!(cancel_keys(&host).is_empty());

    lock(&host.state).paused.clear();
    setup.faux.append_responses(vec![answer("thanks")]);
    host.settle(
        &row.session_id,
        RlmChildRunState::Answered {
            answer_preview: Some("done".to_owned()),
        },
        None,
    );
    opened
        .harness
        .wait_for_task(TaskId::<Value>::from_number(row.task_id), cx())
        .await
        .unwrap();
    opened.root.wait_for_idle(cx()).await.unwrap();
    assert_eq!(
        user_texts(&opened.root, "[child-").await,
        [format!(
            "[child-exited: no-reply child:{}]\n\nLast assistant text: done",
            row.session_name
        )]
    );
    assert!(cancel_keys(&host).is_empty());
    opened.harness.close(cx()).await.unwrap();
}

/// Regression (H5): a reopened (restarted) parent polls its child at once,
/// whatever pause the closed session scheduled. A poll that the daemon's
/// own shutdown failed left a 4 s pause in the checkpoint, and the
/// restarted parent waited it out before it saw that the child's run was
/// interrupted: its roster read the child as `running` meanwhile. The
/// Harness clock stands still here, so a pause the reopened watch waited
/// out would never end.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_reopened_parent_polls_its_child_at_once() {
    let mut setup = setup();
    setup.now = Some(Arc::new(|| 1_000.0));
    let host = FakeHost::new();
    let storage = Arc::new(GatedStorage {
        inner: Arc::new(MemoryStorage::new()),
        refuse_terminal: AtomicBool::new(false),
        refused: AtomicUsize::new(0),
    });
    lock(&host.state).failing_waits = 1;
    let first = open(
        Arc::clone(&storage) as Arc<dyn Storage>,
        &setup,
        Arc::clone(&host),
    )
    .await;
    let row = spawn_child(&first, &setup).await;
    // The first poll fails: the watch pauses 4 s before the next one.
    let paused = ChildCheckpoint::Watch {
        poll: 1,
        next_poll_at: 5_000.0,
        vigil: Vigil {
            progress: None,
            quiet_ms: 0.0,
            failures: 1,
        },
    };
    eventually(|| async {
        let stored = storage
            .inner
            .task(TaskId::from_number(row.task_id), cx())
            .await
            .unwrap()
            .expect("the child task is stored");
        stored
            .state
            .checkpoint()
            .map(|checkpoint| eukhe_chord::json::from_json::<ChildCheckpoint>(checkpoint).unwrap())
            == Some(paused.clone())
    })
    .await;
    first.harness.close(cx()).await.unwrap();

    // The child's run stopped while its parent was down.
    let error = "RLM child run was interrupted: the child stopped mid-run while its parent session was down";
    host.settle(
        &row.session_id,
        RlmChildRunState::Failed {
            failure: ChildFailure::Interrupted,
            error: error.to_owned(),
        },
        None,
    );
    setup.faux.append_responses(vec![answer("noted")]);
    let second = open(
        Arc::clone(&storage) as Arc<dyn Storage>,
        &setup,
        Arc::clone(&host),
    )
    .await;
    let interrupted = reported(&second, &row).await;
    assert_eq!(
        interrupted,
        ChildRow {
            status: ChildStatus::Error,
            error: Some(error.to_owned()),
            failure: Some(ChildFailure::Interrupted),
            settled: true,
            ..row.clone()
        }
    );
    assert_eq!(
        user_texts(&second.root, "[child-").await,
        [format!(
            "[child-failed: interrupted child:{}]\n\n{error}",
            row.session_name
        )]
    );
    assert_eq!(lock(&host.state).polls, 2);
    second.harness.close(cx()).await.unwrap();
}
