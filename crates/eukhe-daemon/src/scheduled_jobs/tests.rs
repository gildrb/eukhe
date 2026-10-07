//! The scheduled-jobs unit battery: the fire/defer decision, the durable
//! delivery (request ids, the heartbeat queue-key replacement), the target
//! verification, and the mutation hook.
use std::sync::Arc;

use super::*;
use crate::durable_test_support::{
    created_worker, wait_busy, worker_entries, worker_inbox, worker_rows,
};

const SESSION: &str = "cron-session";

/// An active job bound to the worker's live session (`every 10s`, never
/// run): a heartbeat on `delivery_mode`, or a plain cron job.
fn job_for(
    worker: &Worker,
    id: &str,
    prompt: &str,
    heartbeat: Option<DeliveryMode>,
) -> AgentCronJob {
    let (binding, _) = live_binding(&lock(&worker.core)).expect("a persisted session");
    AgentCronJob {
        id: id.to_owned(),
        status: JobStatus::Active,
        source: heartbeat.map(|_| "rlm_heartbeat".to_owned()),
        runtime_kind: None,
        delivery_mode: heartbeat,
        active_session_id: binding.active_session_id,
        session_id: binding.session_id,
        session_file: binding.session_file,
        cwd: binding.cwd,
        label: None,
        prompt: prompt.to_owned(),
        schedule: eukhe_core::cron::AgentCronSchedule {
            kind: eukhe_core::cron::ScheduleKind::Interval,
            expression: "every 10s".to_owned(),
            interval_ms: Some(10_000),
        },
        created_at: "2026-09-22T00:00:00.000Z".to_owned(),
        updated_at: "2026-09-22T00:00:00.000Z".to_owned(),
        next_run_at: None,
        last_run_at: None,
        last_skipped_at: None,
        last_error: None,
        run_count: 0,
    }
}

/// A worker whose first run holds the model request (later inputs queue).
async fn busy_worker() -> (tempfile::TempDir, Arc<Worker>) {
    let (dir, worker) = created_worker(
        SESSION,
        json!([{ "text": "held", "delayMs": 600_000 }, "ack"]),
    )
    .await;
    let prompt = worker
        .dispatch(
            "prompt",
            &json!({ "activeSessionId": SESSION, "message": "work" }),
        )
        .await;
    assert!(prompt.success, "{prompt:?}");
    wait_busy(&worker, true).await;
    (dir, worker)
}

/// Fire `job` on a background task (the fire waits for its settle).
fn fire(
    worker: &Arc<Worker>,
    job: AgentCronJob,
) -> tokio::task::JoinHandle<anyhow::Result<Option<&'static str>>> {
    let hooks = Arc::clone(&worker.scheduled.hooks);
    tokio::spawn(async move { hooks.run_job(&job).await })
}

/// Poll until the inbox holds `count` items.
async fn wait_inbox(worker: &Worker, count: usize) -> Vec<(String, String)> {
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(10);
    loop {
        let inbox = worker_inbox(worker).await;
        if inbox.len() == count {
            return inbox;
        }
        assert!(
            std::time::Instant::now() < deadline,
            "the inbox never reached {count} items: {inbox:?}"
        );
        tokio::time::sleep(std::time::Duration::from_millis(10)).await;
    }
}

const HEARTBEAT_TEXT: &str = "[heartbeat: every 10s run#0]\n\nprint hello world";

/// An idle session's heartbeat fire runs as the turn carrying the
/// `heartbeat_prompt` row (TS `promptHeartbeat`), and settles as a run.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_heartbeat_fire_runs_its_row_and_settles_as_a_run() {
    let (_dir, worker) = created_worker(SESSION, json!(["ack"])).await;
    let job = job_for(
        &worker,
        "hb-1",
        "print hello world",
        Some(DeliveryMode::Steer),
    );
    let outcome = worker.scheduled.hooks.run_job(&job).await.expect("fire");
    assert_eq!(outcome, None, "an answered fire is a run");

    let rows = worker_rows(&worker, "eukhe.custom").await;
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0]["customType"], json!("heartbeat_prompt"));
    assert_eq!(
        rows[0]["content"],
        json!([{ "type": "text", "text": HEARTBEAT_TEXT }])
    );
    assert_eq!(rows[0]["details"]["jobId"], json!("hb-1"));
    assert_eq!(rows[0]["details"]["runCount"], json!(0));
    let kinds: Vec<String> = worker_entries(&worker)
        .await
        .into_iter()
        .map(|entry| entry.kind)
        .filter(|kind| kind != "pi.system")
        .collect();
    assert_eq!(kinds, ["eukhe.custom", "pi.user", "pi.assistant"]);
}

/// A fire repeated for the same run (a crash before the store recorded
/// it) dedupes onto the admitted submission: one row, one turn.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_repeated_fire_of_one_run_never_duplicates() {
    let (_dir, worker) = created_worker(SESSION, json!(["ack", "again"])).await;
    let job = job_for(
        &worker,
        "hb-1",
        "print hello world",
        Some(DeliveryMode::Steer),
    );
    for _ in 0..2 {
        let outcome = worker.scheduled.hooks.run_job(&job).await.expect("fire");
        assert_eq!(outcome, None);
    }
    let users = worker_entries(&worker)
        .await
        .into_iter()
        .filter(|entry| entry.kind == "pi.user")
        .count();
    assert_eq!(users, 1);
    assert_eq!(worker_rows(&worker, "eukhe.custom").await.len(), 1);
}

/// A busy session queues a steer heartbeat on its lane (card + prompt); a
/// later fire replaces the queued one (the TS `heartbeat:<id>` queue key),
/// whose fire settles as a skip. A plain cron job queues as a follow-up.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_later_heartbeat_fire_replaces_the_queued_one() {
    let (_dir, worker) = busy_worker().await;
    let first = job_for(
        &worker,
        "hb-1",
        "print hello world",
        Some(DeliveryMode::Steer),
    );
    let first_fire = fire(&worker, first.clone());
    assert_eq!(
        wait_inbox(&worker, 2).await,
        vec![
            ("write".to_owned(), String::new()),
            ("steer".to_owned(), HEARTBEAT_TEXT.to_owned()),
        ]
    );
    let mut second = first;
    second.run_count = 1;
    let second_fire = fire(&worker, second);
    assert_eq!(
        first_fire
            .await
            .expect("first fire")
            .expect("first outcome"),
        Some("skipped"),
        "the replaced fire never ran"
    );
    let inbox = wait_inbox(&worker, 2).await;
    assert_eq!(
        inbox[1],
        (
            "steer".to_owned(),
            "[heartbeat: every 10s run#1]\n\nprint hello world".to_owned()
        )
    );

    let cron = job_for(&worker, "cron-1", "run the report", None);
    let cron_fire = fire(&worker, cron);
    let inbox = wait_inbox(&worker, 3).await;
    assert_eq!(
        inbox[2],
        ("followUp".to_owned(), "run the report".to_owned())
    );

    let aborted = worker
        .dispatch(
            "abort_and_clear_queue",
            &json!({ "activeSessionId": SESSION }),
        )
        .await;
    assert!(aborted.success, "{aborted:?}");
    assert_eq!(
        second_fire.await.expect("second fire").expect("outcome"),
        Some("skipped")
    );
    assert_eq!(
        cron_fire.await.expect("cron fire").expect("outcome"),
        Some("skipped")
    );
}

/// The kernel mutation hook withdraws a dropped heartbeat's queued fire
/// (TS `removeQueuedHeartbeatFollowUp`) and re-arms the scheduler.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn the_mutation_hook_withdraws_a_dropped_heartbeats_queued_fire() {
    let (_dir, worker) = busy_worker().await;
    let job = job_for(
        &worker,
        "hb-1",
        "print hello world",
        Some(DeliveryMode::Steer),
    );
    let fired = fire(&worker, job.clone());
    wait_inbox(&worker, 2).await;
    let hook = worker.scheduled.mutation_hook();
    hook(
        eukhe_core::session_engine::host_requests::RlmHeartbeatMutation {
            job,
            drop_queued: true,
        },
    )
    .await;
    assert_eq!(worker_inbox(&worker).await, Vec::<(String, String)>::new());
    assert_eq!(
        fired.await.expect("fire").expect("outcome"),
        Some("skipped")
    );
    let aborted = worker
        .dispatch("abort", &json!({ "activeSessionId": SESSION }))
        .await;
    assert!(aborted.success, "{aborted:?}");
}

/// The delivery-side verification (TS `isPersistedCronJobRunnable`): a
/// fire whose target was killed (archived) or deleted cancels the
/// session's jobs and skips instead of reviving it.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_fire_at_a_killed_or_deleted_session_cancels_and_skips() {
    let (dir, worker) = created_worker(SESSION, json!(["ack"])).await;
    let mut gone = job_for(&worker, "hb-gone", "nudge", Some(DeliveryMode::Steer));
    gone.session_file = dir
        .path()
        .join("agent/sessions/0192a000-dead-7000-8000-000000000000")
        .to_string_lossy()
        .into_owned();
    let created = worker
        .scheduled
        .store()
        .create_rlm_heartbeat(&CreateAgentCronJobInput {
            active_session_id: gone.active_session_id.clone(),
            session_id: gone.session_id.clone(),
            session_file: gone.session_file.clone(),
            cwd: gone.cwd.clone(),
            source: Some("rlm_heartbeat".to_owned()),
            prompt: "nudge".to_owned(),
            schedule_text: "every 10s".to_owned(),
            delivery_mode: Some(DeliveryMode::Steer),
            ..Default::default()
        })
        .expect("create");
    assert_eq!(created.session_file, gone.session_file);
    assert_eq!(
        worker
            .scheduled
            .hooks
            .run_job(&created)
            .await
            .expect("fire"),
        Some("skipped")
    );
    let listed = worker.scheduled.store().list();
    assert!(
        listed
            .iter()
            .filter(|job| job.id == created.id)
            .all(|job| job.status != JobStatus::Active),
        "the dead target's jobs cancel: {listed:?}"
    );

    let live = job_for(&worker, "hb-live", "nudge", Some(DeliveryMode::Steer));
    let hosted = worker.session.get().expect("hosted");
    meta::mark_archived(hosted.harness(), &BACKGROUND_CONTEXT)
        .await
        .expect("archive");
    assert_eq!(
        worker.scheduled.hooks.run_job(&live).await.expect("fire"),
        Some("skipped")
    );
    assert_eq!(worker_rows(&worker, "eukhe.custom").await.len(), 0);
}

/// The kernel cron wiring binds kernel-created heartbeats to the live
/// identity: the active session id, the durable id, the storage directory.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn the_kernel_cron_wiring_binds_the_live_session() {
    let (_dir, worker) = created_worker(SESSION, json!(["ack"])).await;
    let (binding, artifacts) = live_binding(&lock(&worker.core)).expect("persisted");
    let wiring = worker.kernel_cron_wiring(
        &binding.session_id,
        Some(Path::new(&binding.session_file)),
        &binding.cwd,
    );
    let bound = wiring.binding.expect("binding");
    assert_eq!(bound.active_session_id, SESSION);
    assert_eq!(bound.session_id, binding.session_id);
    assert_eq!(bound.session_file, binding.session_file);
    assert!(wiring.mutation_hook.is_some());
    let artifacts = artifacts.expect("artifact dir");
    assert!(
        artifacts.ends_with(Path::new("session-artifacts").join(&binding.session_id)),
        "{}",
        artifacts.display()
    );
}
