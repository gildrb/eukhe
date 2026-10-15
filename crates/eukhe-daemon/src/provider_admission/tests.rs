//! The supervisor's provider admission over real connection loops: workers
//! (registered tokens) share one limit, a released or abandoned slot goes to
//! the oldest waiter, a dead worker's slot and queue place are reclaimed
//! when its sockets close, a full queue fails at once, a settings change
//! applies without a restart, and the compactor's background slots (the
//! supervisor's own, or a worker's over its link) give way to workers'
//! requests.

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::Duration;

use eukhe_core::admission::{
    AdmissionError, AdmissionHandle, AdmissionRejected, AdmissionRequest, AdmissionSnapshot,
    ProviderAdmission, QueuedNotice,
};
use eukhe_types::daemon::AdmissionPriority::{self, Background, Interactive};
use eukhe_types::platform::transport::TransportStream;
use futures::FutureExt as _;
use serde_json::{json, Map, Value};
use tempfile::TempDir;

use super::LinkAdmission;
use crate::registry::ResidentWorker;
use crate::supervisor::{Supervisor, SupervisorOptions};
use crate::supervisor_link::SupervisorLink;

struct Harness {
    dir: TempDir,
    supervisor: Arc<Supervisor>,
    socket: PathBuf,
    accept: tokio::task::JoinHandle<()>,
}

impl Drop for Harness {
    fn drop(&mut self) {
        self.accept.abort();
    }
}

fn descriptor(dir: &Path, token: &str) -> eukhe_types::daemon::DaemonWorkerDescriptor {
    eukhe_types::daemon::DaemonWorkerDescriptor {
        version: 1,
        worker_id: format!("w-{token}"),
        pid: 4242,
        process_start_id: None,
        socket_path: dir
            .join(format!("{token}.sock"))
            .to_string_lossy()
            .to_string(),
        recovery_journal_path: dir
            .join(format!("{token}-recovery.jsonl"))
            .to_string_lossy()
            .to_string(),
        orphan_process_journal_path: None,
        supervisor_socket_path: dir.join("d.sock").to_string_lossy().to_string(),
        authentication_token: token.to_string(),
        worker_instance_id: None,
        root_active_session_id: format!("a-{token}"),
        owner_client_id: None,
        root_session_id: None,
        session_file: None,
        session_dir: None,
        created_at: "t".to_string(),
        updated_at: "t".to_string(),
        lifecycle: eukhe_types::daemon::DaemonWorkerLifecycle::Ready,
        create_command: eukhe_types::daemon::DurableDaemonCreateCommand {
            session_path: None,
            no_session: None,
            rest: Map::default(),
        },
        consecutive_failures: 0,
        stop_requested_at: None,
        archive_on_stop: None,
        last_failure_at: None,
        last_error: None,
        rest: Map::default(),
    }
}

/// A supervisor serving `d.sock` with one registered worker per token and
/// `settings` as its global settings.
async fn harness(settings: &Value, tokens: &[&str]) -> Harness {
    let dir = TempDir::new().unwrap();
    let agent_dir = dir.path().join("agent");
    std::fs::create_dir_all(&agent_dir).unwrap();
    std::fs::write(agent_dir.join("settings.json"), settings.to_string()).unwrap();
    let socket = dir.path().join("d.sock");
    let supervisor = Arc::new(
        Supervisor::new(SupervisorOptions {
            socket_path: socket.clone(),
            agent_dir,
        })
        .unwrap(),
    );
    for token in tokens {
        supervisor
            .registry
            .insert(ResidentWorker::new(
                format!("w-{token}"),
                descriptor(dir.path(), token),
                dir.path().join(format!("{token}.json")),
            ))
            .await;
    }
    let listener = tokio::net::UnixListener::bind(&socket).unwrap();
    let serving = Arc::clone(&supervisor);
    let accept = tokio::spawn(async move {
        while let Ok((stream, _)) = listener.accept().await {
            let supervisor = Arc::clone(&serving);
            let stream: Box<dyn TransportStream> = Box::new(stream);
            tokio::spawn(async move { supervisor.handle_client(stream).await });
        }
    });
    Harness {
        dir,
        supervisor,
        socket,
        accept,
    }
}

impl Harness {
    fn worker(&self, token: &str) -> LinkAdmission {
        LinkAdmission::new(self.socket.clone(), token.to_owned())
    }

    fn snapshot(&self) -> AdmissionSnapshot {
        self.supervisor.provider_admission.snapshot("p")
    }

    /// Wait until the provider's interactive counters read
    /// `active`/`waiting`.
    async fn settles_at(&self, active: u32, waiting: u32) {
        let expected = AdmissionSnapshot {
            active,
            waiting,
            ..AdmissionSnapshot::default()
        };
        let deadline = tokio::time::Instant::now() + Duration::from_secs(5);
        while self.snapshot() != expected {
            assert!(
                tokio::time::Instant::now() < deadline,
                "the counters stayed at {:?}, expected {expected:?}",
                self.snapshot()
            );
            tokio::time::sleep(Duration::from_millis(5)).await;
        }
    }
}

fn request(notices: &Arc<AtomicUsize>) -> AdmissionRequest {
    let notices = Arc::clone(notices);
    AdmissionRequest {
        provider_id: "p".to_owned(),
        priority: Interactive,
        on_queued: QueuedNotice::new(move || {
            notices.fetch_add(1, Ordering::SeqCst);
        }),
    }
}

#[tokio::test]
async fn workers_share_the_limit_and_a_released_slot_goes_to_the_waiter() {
    let harness = harness(&json!({ "providerMaxInFlight": { "p": 1 } }), &["a", "b"]).await;
    let notices = Arc::new(AtomicUsize::new(0));
    let held = harness
        .worker("a")
        .acquire(request(&notices))
        .await
        .expect("a free slot");
    let b = harness.worker("b");
    let waiter_notices = Arc::clone(&notices);
    let waiting = tokio::spawn(async move { b.acquire(request(&waiter_notices)).await });
    harness.settles_at(1, 1).await;
    drop(held);
    let _granted = waiting.await.unwrap().expect("granted after the release");
    harness.settles_at(1, 0).await;
    // Only the request that had to wait heard the queued frame.
    assert_eq!(notices.load(Ordering::SeqCst), 1);
}

#[tokio::test]
async fn a_dead_workers_slot_and_queue_place_are_reclaimed() {
    let harness = harness(&json!({ "providerMaxInFlight": { "p": 1 } }), &["a", "b"]).await;
    let command = json!({
        "type": "provider_admission_acquire",
        "workerToken": "a",
        "providerId": "p",
    });
    // Worker `a` holds the slot over its link connection; its process
    // dying closes that socket, exactly like dropping the connection.
    let link = SupervisorLink::new(harness.socket.clone());
    let (response, dying) = link
        .hold(command.clone(), Duration::from_secs(5), |_| {})
        .await
        .expect("the held acquire");
    assert!(response.success, "{response:?}");
    let b = harness.worker("b");
    let notices = Arc::new(AtomicUsize::new(0));
    let waiter_notices = Arc::clone(&notices);
    let waiting = tokio::spawn(async move { b.acquire(request(&waiter_notices)).await });
    harness.settles_at(1, 1).await;
    drop(dying);
    let held_by_b = waiting.await.unwrap().expect("the reclaimed slot");
    harness.settles_at(1, 0).await;

    // A worker that dies while it waits leaves the queue.
    let waiting_link = SupervisorLink::new(harness.socket.clone());
    let dying_waiter = tokio::spawn(async move {
        waiting_link
            .hold(command, Duration::from_secs(5), |_| {})
            .await
            .map(|_| ())
    });
    harness.settles_at(1, 1).await;
    dying_waiter.abort();
    harness.settles_at(1, 0).await;
    drop(held_by_b);
    harness.settles_at(0, 0).await;
}

#[tokio::test]
async fn a_full_queue_fails_at_once() {
    let harness = harness(
        &json!({ "providerMaxInFlight": { "p": 1 }, "providerMaxQueued": 0 }),
        &["a", "b"],
    )
    .await;
    let notices = Arc::new(AtomicUsize::new(0));
    let _held = harness
        .worker("a")
        .acquire(request(&notices))
        .await
        .expect("a free slot");
    let rejected = harness.worker("b").acquire(request(&notices)).await;
    assert_eq!(
        rejected.err(),
        Some(AdmissionError::QueueFull(AdmissionRejected {
            provider_id: "p".to_owned(),
            queue_limit: 0,
        }))
    );
    harness.settles_at(1, 0).await;
}

#[tokio::test]
async fn an_unknown_worker_is_refused() {
    let harness = harness(&json!({ "providerMaxInFlight": { "p": 1 } }), &["a"]).await;
    let notices = Arc::new(AtomicUsize::new(0));
    let refused = harness.worker("forged").acquire(request(&notices)).await;
    assert_eq!(
        refused.err(),
        Some(AdmissionError::Unavailable {
            provider_id: "p".to_owned(),
            reason: "Worker authentication failed".to_owned(),
        })
    );
    harness.settles_at(0, 0).await;
}

#[tokio::test]
async fn a_raised_limit_applies_without_a_restart() {
    let harness = harness(
        &json!({ "providerMaxInFlight": { "p": 1 } }),
        &["a", "b", "c"],
    )
    .await;
    let notices = Arc::new(AtomicUsize::new(0));
    let _held = harness
        .worker("a")
        .acquire(request(&notices))
        .await
        .expect("a free slot");
    let b = harness.worker("b");
    let waiter_notices = Arc::clone(&notices);
    let waiting = tokio::spawn(async move { b.acquire(request(&waiter_notices)).await });
    harness.settles_at(1, 1).await;
    std::fs::write(
        harness.dir.path().join("agent").join("settings.json"),
        json!({ "providerMaxInFlight": { "p": 10 } }).to_string(),
    )
    .unwrap();
    // The next request reads the changed file: the raise admits the
    // waiter and the newcomer.
    let _third = harness
        .worker("c")
        .acquire(request(&notices))
        .await
        .expect("room under the raised limit");
    let _second = waiting.await.unwrap().expect("admitted by the raise");
    harness.settles_at(3, 0).await;
}

/// Fail instead of hanging when a step never comes.
async fn within<F: std::future::Future>(future: F) -> F::Output {
    tokio::time::timeout(Duration::from_secs(30), future)
        .await
        .expect("the step comes")
}

/// A request of class `priority` to `p`; the receiver hears when it has
/// to wait.
fn watched(priority: AdmissionPriority) -> (AdmissionRequest, tokio::sync::oneshot::Receiver<()>) {
    let (queued, waited) = tokio::sync::oneshot::channel();
    let request = AdmissionRequest {
        provider_id: "p".to_owned(),
        priority,
        on_queued: QueuedNotice::new(move || {
            // The test may have stopped listening.
            let _ = queued.send(());
        }),
    };
    (request, waited)
}

/// Interactive, then background counters.
fn classes(
    active: u32,
    waiting: u32,
    background: u32,
    background_waiting: u32,
) -> AdmissionSnapshot {
    AdmissionSnapshot {
        active,
        waiting,
        background_active: background,
        background_waiting,
    }
}

/// The supervisor's own compactor takes background slots of the registry
/// its workers share. At a limit of one, a worker's request takes the slot
/// from it at once; the compactor's next request waits, and the slot goes
/// to a worker's waiting request (the next round of a turn) before it.
#[tokio::test]
async fn a_workers_request_preempts_the_supervisors_compactor_at_a_limit_of_one() {
    let harness = harness(&json!({ "providerMaxInFlight": { "p": 1 } }), &["a", "b"]).await;
    let compactor = AdmissionHandle::new(Arc::clone(&harness.supervisor.provider_admission));
    let background = compactor
        .acquire(watched(Background).0)
        .await
        .expect("a free slot");
    let first = within(harness.worker("a").acquire(watched(Interactive).0))
        .await
        .expect("admitted at once");
    within(background.preempted()).await;
    let (request, compactor_waits) = watched(Background);
    let resumed = tokio::spawn(compactor.acquire(request));
    within(compactor_waits).await.expect("the compactor waits");
    let b = harness.worker("b");
    let (request, round_waits) = watched(Interactive);
    let next_round = tokio::spawn(async move { b.acquire(request).await });
    within(round_waits).await.expect("the next round waits");
    let while_first_runs = harness.snapshot();
    drop(first);
    let next_round = within(next_round)
        .await
        .unwrap()
        .expect("the waiting round's slot");
    let while_next_round_runs = harness.snapshot();
    drop(next_round);
    let resumed = within(resumed)
        .await
        .unwrap()
        .expect("the compactor's slot");
    drop(background);
    assert_eq!(
        (
            while_first_runs,
            while_next_round_runs,
            harness.snapshot(),
            resumed.preempted().now_or_never()
        ),
        (
            classes(1, 1, 0, 1),
            classes(1, 0, 0, 1),
            classes(0, 0, 1, 0),
            None
        )
    );
}

/// A worker that owns the chat runs its compactor's requests as background
/// slots over its link: on an unlimited provider they wait while another
/// worker's request runs, and the next one preempts them through the link.
#[tokio::test]
async fn a_workers_background_slot_is_preempted_over_its_link() {
    let harness = harness(&json!({}), &["a", "b"]).await;
    let running = within(harness.worker("b").acquire(watched(Interactive).0))
        .await
        .expect("an unlimited provider admits at once");
    let compactor = harness.worker("a");
    let (request, waited) = watched(Background);
    let waiting = tokio::spawn(async move { compactor.acquire(request).await });
    within(waited).await.expect("the compactor waits");
    let while_session_runs = harness.snapshot();
    drop(running);
    let background = within(waiting)
        .await
        .unwrap()
        .expect("its slot once the session's request ended");
    let _next = within(harness.worker("b").acquire(watched(Interactive).0))
        .await
        .expect("admitted at once");
    within(background.preempted()).await;
    assert_eq!(
        (while_session_runs, harness.snapshot()),
        (classes(1, 0, 0, 1), classes(1, 0, 0, 0))
    );
}
