//! Races of two processes on one jobs file (audit R1–R4). Two stores on
//! one path stand for two processes (a CLI and the daemon, each with its
//! own store); real threads run them at once. Each test checks an
//! invariant a correct store keeps whatever the interleaving: a user
//! mutation reads, decides and writes under the lock on the current file,
//! and the lock of a live holder is never taken or released by another.
//! The loops are bounded by [`RACE_BUDGET`], so a store that blocks or a
//! failed assertion never hangs the test.

use std::collections::HashMap;
use std::path::Path;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::mpsc;
use std::time::{Duration, Instant, UNIX_EPOCH};

use super::{
    input, AgentCronJobStore, DispatchOutcome, DispatchResultOptions, RlmHeartbeatUpdate,
    SessionBinding,
};
use crate::cron::{JobSource, JobStatus};
use crate::platform::lock_dir::LockDir;

const T0: u64 = 1_700_000_000_000;
/// The period of every job here ("every 10m").
const EVERY: u64 = 600_000;
/// The longest any race loop of a test runs.
const RACE_BUDGET: Duration = Duration::from_secs(12);

/// Two stores on one jobs file: two processes sharing it.
fn two_stores(dir: &tempfile::TempDir) -> (AgentCronJobStore, AgentCronJobStore) {
    let path = dir.path().join("jobs.json");
    (
        AgentCronJobStore::new(path.clone()),
        AgentCronJobStore::new(path),
    )
}

/// R1, a lost user edit reported as success: a CLI cancel read a job
/// before a daemon claim pass wrote it (a newer `updated_at`), and its
/// write lost the merge, while `cancel` still answered the job cancelled.
/// Both processes take their times from one clock, each before it reads
/// the file, so a cancel loses only to a pass that wrote between its read
/// and its write.
/// Invariant: every job whose `cancel` returned `Ok(Some(_))` is cancelled
/// on file once the claim passes are over.
#[test]
fn a_cancel_is_never_undone_by_a_concurrent_claim_pass() {
    const JOBS: usize = 150;
    let dir = tempfile::tempdir().unwrap();
    let (daemon, cli) = two_stores(&dir);
    let ids: Vec<String> = (0..JOBS)
        .map(|index| {
            cli.create(&input(&format!("job {index}"), "every 10m", T0))
                .unwrap()
                .id
        })
        .collect();
    // One clock for both processes, a period per tick: every job is due
    // again at each pass, whose writes get `updated_at` = its tick.
    let clock = AtomicU64::new(T0);
    let tick = || clock.fetch_add(EVERY, Ordering::SeqCst) + EVERY;
    let cancelling = AtomicBool::new(true);
    let acknowledged: Vec<String> = std::thread::scope(|scope| {
        scope.spawn(|| {
            let deadline = Instant::now() + RACE_BUDGET;
            let mut running = Vec::new();
            while cancelling.load(Ordering::Acquire) && Instant::now() < deadline {
                let at = tick();
                if let Ok(claimed) = daemon.claim_due(at, at) {
                    running.extend(claimed);
                }
                std::thread::sleep(Duration::from_millis(1));
            }
        });
        let acknowledged = ids
            .iter()
            .filter(|id| matches!(cli.cancel(id, tick()), Ok(Some(_))))
            .cloned()
            .collect();
        cancelling.store(false, Ordering::Release);
        acknowledged
    });
    let on_file: HashMap<String, JobStatus> = cli
        .list()
        .into_iter()
        .map(|job| (job.id, job.status))
        .collect();
    let undone: Vec<(&String, Option<&JobStatus>)> = acknowledged
        .iter()
        .map(|id| (id, on_file.get(id)))
        .filter(|(_, status)| *status != Some(&JobStatus::Cancelled))
        .collect();
    assert!(
        !acknowledged.is_empty(),
        "R1: no cancel was acknowledged, so the race was not exercised"
    );
    assert!(
        undone.is_empty(),
        "R1: {} of {} acknowledged cancels were undone by a concurrent claim pass \
         (job id, status on file): {undone:?}",
        undone.len(),
        acknowledged.len()
    );
}

/// R2, a rebind lost with no clock dependency: `rebind_session_jobs`
/// keeps a job's `updated_at`, so another process's user write (here a
/// label edit of another job) that read the old binding before the rebind
/// and wrote after it wins the merge with an equal `updated_at`.
/// Invariant: once a rebind has returned and every user write that may
/// have read the file before it has finished, the job has the binding the
/// rebind wrote.
#[test]
fn a_rebind_is_never_undone_by_a_concurrent_user_write() {
    const ROUNDS: u64 = 60;
    let dir = tempfile::tempdir().unwrap();
    let (restorer, writer) = two_stores(&dir);
    let mut bound = input("bound", "every 10m", T0);
    bound.active_session_id = "live-0".to_string();
    bound.session_file = "/w/f.jsonl".to_string();
    let job = restorer.create(&bound).unwrap();
    let mut other = input("other", "every 10m", T0);
    other.source = Some(JobSource::RlmHeartbeat);
    other.active_session_id = "live-other".to_string();
    other.session_id = "session-other".to_string();
    other.session_file = "/w/g.jsonl".to_string();
    let other = writer.create_rlm_heartbeat(&other).unwrap();
    let started = AtomicU64::new(0);
    let finished = AtomicU64::new(0);
    let rebinding = AtomicBool::new(true);
    let undone: Vec<(String, Option<String>)> = std::thread::scope(|scope| {
        scope.spawn(|| {
            let deadline = Instant::now() + RACE_BUDGET;
            let mut edit = 0;
            while rebinding.load(Ordering::Acquire) && Instant::now() < deadline {
                edit += 1;
                started.fetch_add(1, Ordering::SeqCst);
                let _ = writer.update_rlm_heartbeat(
                    "live-other",
                    &other.id,
                    &RlmHeartbeatUpdate {
                        label: Some(format!("edit {edit}")),
                        now: Some(T0 + edit),
                        ..Default::default()
                    },
                );
                finished.fetch_add(1, Ordering::SeqCst);
            }
        });
        let deadline = Instant::now() + RACE_BUDGET;
        let mut undone = Vec::new();
        for round in 1..=ROUNDS {
            if Instant::now() >= deadline {
                break;
            }
            let live = format!("live-{round}");
            let binding = SessionBinding {
                active_session_id: live.clone(),
                session_id: "session-1".to_string(),
                session_file: "/w/f.jsonl".to_string(),
                cwd: "/w".to_string(),
            };
            if restorer.rebind_session_jobs(&binding, T0 + round).is_err() {
                continue;
            }
            // A user write that read the file before the rebind landed
            // has started by now: wait until it has written.
            let in_flight = started.load(Ordering::SeqCst);
            while finished.load(Ordering::SeqCst) < in_flight && Instant::now() < deadline {
                std::thread::yield_now();
            }
            let binding_on_file = restorer
                .list()
                .into_iter()
                .find(|found| found.id == job.id)
                .map(|found| found.active_session_id);
            if binding_on_file.as_deref() != Some(live.as_str()) {
                undone.push((live, binding_on_file));
            }
        }
        rebinding.store(false, Ordering::Release);
        undone
    });
    assert!(
        undone.is_empty(),
        "R2: {} of {ROUNDS} rebinds were undone by a concurrent user write \
         (rebound to, binding on file): {undone:?}",
        undone.len()
    );
}

/// R3, a double run: a user write (a label-only RLM heartbeat edit, later
/// than every claim) read the job still due at occurrence N before a claim
/// pass claimed N, and its write won the merge, putting the next run back
/// to N; the claim record survived (a user write replaces only jobs), and
/// the next pass claimed N again.
/// Invariant: no (job id, scheduled occurrence) is dispatched twice.
#[test]
fn a_claimed_occurrence_never_runs_twice() {
    const PASSES: u64 = 4_000;
    /// The user's clock: later than every claim and finish.
    const USER_NOW: u64 = T0 + (PASSES + 2) * EVERY;
    let dir = tempfile::tempdir().unwrap();
    let (scheduler, user) = two_stores(&dir);
    let mut heartbeat = input("watch pods", "every 10m", T0);
    heartbeat.source = Some(JobSource::RlmHeartbeat);
    let job = user.create_rlm_heartbeat(&heartbeat).unwrap();
    let scheduling = AtomicBool::new(true);
    let (passes, doubled) = std::thread::scope(|scope| {
        scope.spawn(|| {
            let deadline = Instant::now() + RACE_BUDGET;
            let mut edit = 0;
            while scheduling.load(Ordering::Acquire) && Instant::now() < deadline {
                edit += 1;
                let _ = user.update_rlm_heartbeat(
                    "live-1",
                    &job.id,
                    &RlmHeartbeatUpdate {
                        label: Some(format!("label {edit}")),
                        now: Some(USER_NOW),
                        ..Default::default()
                    },
                );
            }
        });
        let deadline = Instant::now() + RACE_BUDGET;
        let mut runs: HashMap<(String, String), u32> = HashMap::new();
        let mut doubled = Vec::new();
        let mut passes = 0;
        for pass in 1..=PASSES {
            if Instant::now() >= deadline || !doubled.is_empty() {
                break;
            }
            passes = pass;
            let at = T0 + pass * EVERY;
            let Ok(claimed) = scheduler.claim_due(at, at) else {
                continue;
            };
            for running in claimed {
                let dispatch = running.dispatch();
                let scheduled_for = scheduler
                    .read_states()
                    .into_iter()
                    .flat_map(|state| state.dispatches)
                    .find(|record| record.id == dispatch.id)
                    .map_or_else(
                        || "<no claim record>".to_string(),
                        |record| record.scheduled_for,
                    );
                let key = (dispatch.job.id.clone(), scheduled_for);
                let count = runs.entry(key.clone()).or_default();
                *count += 1;
                if *count > 1 {
                    doubled.push((pass, key));
                }
                // The run ends; the finish step is retried past a busy lock.
                let result = DispatchResultOptions {
                    now: Some(at),
                    outcome: DispatchOutcome::Ran,
                    error: None,
                };
                while scheduler
                    .record_dispatch_result(&dispatch.id, &result)
                    .is_err()
                    && Instant::now() < deadline
                {}
            }
        }
        scheduling.store(false, Ordering::Release);
        (passes, doubled)
    });
    assert!(
        doubled.is_empty(),
        "R3: an occurrence was dispatched twice within {passes} claim passes \
         (pass, (job id, scheduled for)): {doubled:?}"
    );
}

/// Age a lock directory past every staleness threshold, as a holder
/// suspended past it (or a clock jump) leaves it.
fn age_lock(lock: &Path) {
    std::fs::File::open(lock)
        .and_then(|opened| opened.set_modified(UNIX_EPOCH + Duration::from_secs(1)))
        .expect("the held lock directory exists and can be aged");
}

/// R4, the lock taken from a live holder: process A holds the jobs file
/// lock inside a pass (its state loaded) and is suspended past the 30 s
/// staleness threshold; process B judges the lock stale, takes it, claims
/// a due job and releases; A resumes and writes the state it loaded, so
/// B's claim record is lost. A's release (no owner check) also removes the
/// lock of a newer holder.
/// Invariants: a rival pass either fails to get the lock or its claim
/// records survive the holder's write; and a holder's release never
/// removes a lock directory another holder created.
#[test]
fn a_live_lock_holder_is_never_robbed() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("jobs.json");
    let holder = AgentCronJobStore::new(path.clone());
    let rival = AgentCronJobStore::new(path.clone());
    holder.create(&input("tick", "every 10m", T0)).unwrap();
    let lock = LockDir::path_for(&path);
    let (holding_tx, holding_rx) = mpsc::channel();
    let (go_tx, go_rx) = mpsc::channel::<()>();
    let held_by = &holder;
    let (rival_claims, successor, successor_survived) = std::thread::scope(|scope| {
        let held = scope.spawn(move || {
            held_by.mutate_states(|state| {
                let _ = holding_tx.send(());
                let _ = go_rx.recv_timeout(RACE_BUDGET);
                for job in &mut state.jobs {
                    job.label = Some("edited while holding the lock".to_string());
                }
                Vec::new()
            })
        });
        holding_rx
            .recv_timeout(RACE_BUDGET)
            .expect("the holder takes the lock");
        // The holder is suspended past the staleness threshold.
        age_lock(&lock);
        let rival_claims = rival.claim_due(T0 + EVERY, T0 + EVERY);
        // A newer holder of the lock, if it can take it now.
        let successor = LockDir::acquire(&path, Duration::from_secs(30)).ok();
        let _ = go_tx.send(());
        let _ = held.join();
        let successor_survived = successor.as_ref().map(|_| lock.is_dir());
        (rival_claims, successor, successor_survived)
    });
    drop(successor);
    let records: Vec<String> = holder
        .read_states()
        .into_iter()
        .flat_map(|state| state.dispatches)
        .map(|record| record.id)
        .collect();
    let lost_claims: Vec<String> = rival_claims
        .as_ref()
        .map(|claimed| {
            claimed
                .iter()
                .map(|running| running.dispatch().id.clone())
                .filter(|id| !records.contains(id))
                .collect()
        })
        .unwrap_or_default();
    assert!(
        lost_claims.is_empty() && successor_survived != Some(false),
        "R4: the lock was taken from its live holder: rival claims lost from the file: \
         {lost_claims:?} (claim records on file: {records:?}); a newer holder's lock \
         removed by the robbed holder's release: {}",
        successor_survived == Some(false)
    );
}
