use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::Duration;

use eukhe_ai::models::{create_models, CreateModelsOptions};
use eukhe_bend::rules::once::Mode;
use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_chord::json::{from_json, JsonValue};
use eukhe_durable::errors::StorageError;
use eukhe_durable::harness::effects::{EffectKind, EffectResolution, EffectsState, EFFECTS_DOC};
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::HarnessOptions;
use eukhe_durable::harness::{
    Conversation, ConversationEntryQuery, Harness, OutputLimits, RootOptions, Truncation,
};
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::types::{
    AnyTaskRecord, ConversationId, ConversationQuery, ConversationRecord, Cursor, DocumentAddress,
    DocumentId, DocumentPoint, DocumentQuery, DocumentRecord, EntryId, EntryQuery, EntryRecord,
    Page, Seq, Storage, StorageWrite, StoredDocument, StoredEntry, SubmissionId, SubmissionQuery,
    SubmissionRecord, TaskId, TaskQuery,
};
use eukhe_types::job::JobId;
use futures::future::BoxFuture;
use futures::FutureExt;
use tokio::sync::mpsc;

use super::tree::{commit_start, settle_stale, write_records, JobEnded, JOB_DOC};
use super::{
    lock, wait_until, Job, JobEnd, JobEvent, JobKind, JobSpec, JobState, JobTable, Wait,
    JOB_DOC_KIND,
};
use crate::durable::deps::SessionClosing;
use crate::durable::HarnessCell;

fn capped(max_bytes: usize) -> Truncation {
    Truncation::On(OutputLimits {
        max_bytes,
        ..OutputLimits::default()
    })
}

fn id(id: &str) -> JobId {
    JobId::new(id).expect("id")
}

/// A table on an open Harness over `storage`, with the Harness and its
/// root (the main conversation). Its writer does not run: the ends wait
/// in its queue.
async fn table_on(storage: Arc<dyn Storage>) -> (JobTable, Harness, Conversation) {
    let cx = &BACKGROUND_CONTEXT;
    let options = HarnessOptions::new(
        create_models(CreateModelsOptions::default()),
        Arc::new(create_registry()),
    );
    let harness = Harness::open(storage, options, cx).await.expect("open");
    let root = harness
        .root(RootOptions::default(), cx)
        .await
        .expect("a root");
    harness.resume().expect("resume");
    let cell = HarnessCell::default();
    cell.set(harness.clone(), root.clone());
    (JobTable::new(cell), harness, root)
}

async fn table() -> JobTable {
    table_on(Arc::new(MemoryStorage::new())).await.0
}

/// Record and start a job of `kind` whose kill is `kill`.
async fn start_with(table: &JobTable, job: &str, kind: JobKind, label: &str, spec: JobSpec) -> Job {
    let record = table
        .record_start(id(job), kind, label.to_owned())
        .await
        .expect("the start records");
    table.start(record, spec)
}

/// A job whose kill counts the signals it got in `kills`.
async fn start(
    table: &JobTable,
    job: &str,
    truncation: Truncation,
    kills: &Arc<AtomicUsize>,
) -> Job {
    let kills = Arc::clone(kills);
    start_with(
        table,
        job,
        JobKind::UserBash,
        "sleep 1",
        JobSpec {
            truncation,
            written: 0,
            kill: Box::new(move |_| {
                kills.fetch_add(1, Ordering::SeqCst);
            }),
        },
    )
    .await
}

/// The core carries an exit code as the i64's two 32-bit words: every code
/// comes back as it went, the negative ones and the extremes included.
#[test]
fn every_exit_code_crosses_the_core_exactly() {
    for code in [i64::MIN, -1, 0, 1, 255, i64::from(u32::MAX) + 1, i64::MAX] {
        let ended = JobState::Ended {
            kept: 2,
            dropped: 0,
            end: JobEnd::Exited(code),
        };
        assert_eq!(
            JobState::Live {
                kept: 2,
                dropped: 0
            }
            .step(None, JobEvent::Exited(code)),
            (ended, Some(JobEnd::Exited(code)))
        );
        assert_eq!(ended.step(None, JobEvent::Killed), (ended, None));
    }
}

/// Output past the wire's largest Nat saturates the bytes kept plus
/// dropped there, as Rust counted them before (`job_feed_fills`).
#[test]
fn output_past_the_wire_saturates_the_counts() {
    let near = eukhe_bend::wire::NAT_MAX - 10;
    assert_eq!(
        JobState::Live {
            kept: near,
            dropped: 0
        }
        .step(None, JobEvent::Output(u64::MAX)),
        (
            JobState::Live {
                kept: eukhe_bend::wire::NAT_MAX,
                dropped: 0
            },
            None
        )
    );
}

#[tokio::test]
async fn a_capped_job_keeps_the_cap_counts_the_rest_and_reports_one_end() {
    let table = table().await;
    let mut queue = table.take_queue().expect("queue");
    let kills = Arc::default();
    let job = start(&table, "bash-1", capped(10), &kills).await;
    for event in [
        JobEvent::Output(6),
        JobEvent::Output(6),
        JobEvent::Exited(3),
        JobEvent::Output(5),
        JobEvent::Killed,
    ] {
        job.record(event);
    }
    assert_eq!(
        job.state(),
        JobState::Ended {
            kept: 10,
            dropped: 2,
            end: JobEnd::Exited(3),
        }
    );
    // The writer gets exactly one end.
    let mut ends = Vec::new();
    while let Ok(ended) = queue.try_recv() {
        ends.push(ended);
    }
    assert_eq!(
        ends,
        vec![JobEnded {
            id: id("bash-1"),
            end: JobEnd::Exited(3),
        }]
    );
    // An ended job takes no kill.
    job.kill();
    assert_eq!(kills.load(Ordering::SeqCst), 0);
}

#[tokio::test]
async fn the_opt_out_keeps_every_byte() {
    let table = table().await;
    let job = start(&table, "bash-1", Truncation::Off, &Arc::default()).await;
    job.record(JobEvent::Output(1 << 40));
    job.record(JobEvent::Output(7));
    assert_eq!(
        job.state(),
        JobState::Live {
            kept: (1 << 40) + 7,
            dropped: 0,
        }
    );
}

/// A rewind sends the kill to the running jobs that started after its
/// target entry was committed, as the compiled core decides (entry
/// `job_rewind`); an entry the table did not see, or no target, stops
/// every running job.
#[tokio::test]
async fn a_rewind_kills_the_running_jobs_that_started_after_its_target() {
    let table = table().await;
    let kills = Arc::new(AtomicUsize::new(0));
    let _first = start(&table, "bash-first", Truncation::default(), &kills).await;
    lock(&table.entries).last = Some(Seq::from_number(4));
    let _before = start(&table, "bash-before", Truncation::default(), &kills).await;
    {
        let mut entries = lock(&table.entries);
        entries
            .commits
            .insert(EntryId::from_number(7), Seq::from_number(5));
        entries.last = Some(Seq::from_number(5));
    }
    let _orphan = start(&table, "bash-orphan", Truncation::default(), &kills).await;
    let ended = start(&table, "bash-ended", Truncation::default(), &kills).await;
    ended.record(JobEvent::Exited(0));
    let stopped = |target: Option<EntryId>| -> Vec<String> {
        table
            .rewind_to(target)
            .iter()
            .map(|job| job.id().as_str().to_owned())
            .collect()
    };
    assert_eq!(stopped(Some(EntryId::from_number(7))), vec!["bash-orphan"]);
    // The kill is the owner's signal; the owner reports the end.
    assert_eq!(kills.load(Ordering::SeqCst), 1);
    let every = vec!["bash-first", "bash-before", "bash-orphan"];
    assert_eq!(stopped(Some(EntryId::from_number(9))), every);
    assert_eq!(stopped(None), every);
    assert_eq!(kills.load(Ordering::SeqCst), 7);
}

/// A job that starts after its run wrote output (a detached cell or
/// script) counts those bytes first, under the cap, so it counts every
/// byte of the run.
#[tokio::test]
async fn a_job_counts_the_output_written_before_it_started() {
    let table = table().await;
    let job = start_with(
        &table,
        "shell-1",
        JobKind::Shell,
        "yes | head",
        JobSpec {
            truncation: capped(10),
            written: 15,
            kill: Box::new(|_| {}),
        },
    )
    .await;
    assert_eq!(
        job.state(),
        JobState::Live {
            kept: 10,
            dropped: 5
        }
    );
    job.record(JobEvent::Output(3));
    assert_eq!(
        job.state(),
        JobState::Live {
            kept: 10,
            dropped: 8
        }
    );
}

/// The start record is durable when the caller may launch the job: its
/// node is in the store before the job starts. A start whose record does
/// not commit answers an error, and no job starts.
#[tokio::test]
async fn a_job_starts_only_once_its_start_record_is_durable() {
    let cx = &BACKGROUND_CONTEXT;
    let (table, harness, _root) = table_on(Arc::new(RefusingJob {
        inner: MemoryStorage::new(),
        refused: "bash-bad",
    }))
    .await;
    let record = table
        .record_start(id("bash-1"), JobKind::UserBash, "sleep 1".to_owned())
        .await
        .expect("the start records");
    // The launch: what the store holds of the job when its owner may run
    // it.
    let node = harness
        .snapshot(&JOB_DOC, "bash-1", cx)
        .await
        .expect("a read")
        .map(|value| {
            from_json::<serde_json::Value>(&JsonValue::Object(value)).expect("a job document")
        });
    let job = table.start(
        record,
        JobSpec {
            truncation: Truncation::default(),
            written: 0,
            kill: Box::new(|_| {}),
        },
    );
    let refused = table
        .record_start(id("bash-bad"), JobKind::UserBash, "sleep 1".to_owned())
        .await;
    let started: Vec<String> = table
        .jobs()
        .iter()
        .map(|job| job.id().as_str().to_owned())
        .collect();
    assert_eq!(
        (node, job.is_running(), refused.is_err(), started),
        (
            Some(serde_json::json!({ "kind": "bash", "label": "sleep 1" })),
            true,
            true,
            vec!["bash-1".to_owned()]
        )
    );
    harness.close(cx).await.expect("close");
}

/// A job of an earlier process is reported interrupted once and noted
/// once in the ledger, whatever the mode its run came back in: a crash
/// that cut the commit retiring its node (the node is there again) admits
/// the same notice again, which the harness drops; once the node is gone
/// nothing more is reported.
#[tokio::test]
async fn a_stale_job_is_reported_interrupted_once() {
    let cx = &BACKGROUND_CONTEXT;
    let (_table, harness, root) = table_on(Arc::new(MemoryStorage::new())).await;
    let closing = SessionClosing::default();
    let cut = id("shell-cut");
    commit_start(&harness, &cut, JobKind::Shell, "make test")
        .await
        .expect("the start records");
    settle_stale(&harness, &root, &closing, &cut, Mode::Resume)
        .await
        .expect("the first open settles it");
    // The retire did not commit: the next open finds the node again.
    commit_start(&harness, &cut, JobKind::Shell, "make test")
        .await
        .expect("the node again");
    settle_stale(&harness, &root, &closing, &cut, Mode::Stop)
        .await
        .expect("the next open settles it");
    settle_stale(&harness, &root, &closing, &cut, Mode::Resume)
        .await
        .expect("a later open finds nothing");

    let notices: Vec<String> = root
        .entries(ConversationEntryQuery::default(), 100, None, cx)
        .await
        .expect("the entries")
        .items
        .iter()
        .filter(|entry| entry.kind == "eukhe.custom")
        .map(|entry| format!("{:?}", entry.model))
        .filter(|model| model.contains("[job-settled job:shell-cut status:interrupted]"))
        .collect();
    let ledger: Vec<(String, EffectKind, String, Option<EffectResolution>)> = harness
        .snapshot(&EFFECTS_DOC, root.id(), cx)
        .await
        .expect("the ledger reads")
        .map(|value| from_json::<EffectsState>(&JsonValue::Object(value)).expect("a ledger"))
        .unwrap_or_default()
        .unknown
        .into_iter()
        .map(|effect| (effect.id, effect.kind, effect.what, effect.resolution))
        .collect();
    let node = harness
        .snapshot(&JOB_DOC, "shell-cut", cx)
        .await
        .expect("a read");
    assert_eq!(
        (notices.len(), ledger, node.is_none()),
        (
            1,
            vec![(
                "job:shell-cut".to_owned(),
                EffectKind::Job,
                "make test".to_owned(),
                None
            )],
            true
        )
    );
    harness.close(cx).await.expect("close");
}

#[tokio::test(start_paused = true)]
async fn the_wait_settles_before_the_deadline_and_detaches_at_it() {
    let table = table().await;
    let job = start(&table, "bash-1", Truncation::default(), &Arc::default()).await;
    let budget = Duration::from_millis(30);

    let settled = {
        let job = job.clone();
        tokio::spawn(async move {
            tokio::time::sleep(Duration::from_millis(10)).await;
            job.record(JobEvent::Exited(0));
        })
    };
    let waited = wait_until(tokio::time::Instant::now() + budget, job.ended()).await;
    assert_eq!(waited, Wait::Settled(JobEnd::Exited(0)));
    settled.await.expect("the exit task");

    // A job that exits 40 ms from now, past the budget.
    let late = start(&table, "bash-late", Truncation::default(), &Arc::default()).await;
    let exit = {
        let late = late.clone();
        tokio::spawn(async move {
            tokio::time::sleep(Duration::from_millis(40)).await;
            late.record(JobEvent::Exited(0));
        })
    };
    let started = tokio::time::Instant::now();
    let waited = wait_until(started + budget, late.ended()).await;
    assert_eq!((waited, started.elapsed()), (Wait::Detached, budget));
    exit.await.expect("the exit task");
    // A passed deadline detaches even when the end is ready: within one
    // poll the host sends the timer's tick before the end.
    assert_eq!(
        wait_until(started + budget, late.ended()).await,
        Wait::Detached
    );
}

/// One event a scripted wait sees: output, an exit, the kill, or one
/// millisecond of the paused tokio clock.
#[derive(Clone, Copy)]
enum Step {
    Output(u64),
    Exit(i64),
    Kill,
    Tick,
}

/// What a scripted wait answered after each step: nothing yet, or its
/// answer.
type Answers = Vec<Option<Wait<JobEnd>>>;

/// The answers a blocking wait with a `budget` of milliseconds gives
/// after each of `steps`, on a job whose kill ends it at once: polled
/// once after every step, and kept once it answered.
async fn wait_transcript(budget: u64, steps: &[Step]) -> Answers {
    let table = table().await;
    let job = start_with(
        &table,
        "job",
        JobKind::UserBash,
        "",
        JobSpec {
            truncation: Truncation::default(),
            written: 0,
            kill: Box::new(|job| {
                job.record(JobEvent::Killed);
            }),
        },
    )
    .await;
    let mut wait = Box::pin(wait_until(
        tokio::time::Instant::now() + Duration::from_millis(budget),
        job.ended(),
    ));
    let mut answer = None;
    let mut answers = Vec::new();
    for step in steps {
        match *step {
            Step::Output(bytes) => job.record(JobEvent::Output(bytes)),
            Step::Exit(code) => job.record(JobEvent::Exited(code)),
            Step::Kill => job.kill(),
            Step::Tick => tokio::time::advance(Duration::from_millis(1)).await,
        }
        if answer.is_none() {
            answer = (&mut wait).now_or_never();
        }
        answers.push(answer);
    }
    answers
}

/// The tokio timer against the job's end, step by step, as `bend/job.bend`
/// `wait` answers: output never settles, an exit or the kill settles while
/// budget is left, the budget's last tick detaches, and an end after the
/// detach leaves the wait detached.
#[tokio::test(start_paused = true)]
async fn the_wait_answers_each_step_as_the_model_waits() {
    use Step::{Exit, Kill, Output, Tick};
    let exited = |code| Some(Wait::Settled(JobEnd::Exited(code)));
    let killed = Some(Wait::Settled(JobEnd::Killed));
    let detached = Some(Wait::Detached);
    let cases: [(u64, Vec<Step>, Answers); 5] = [
        (
            2,
            vec![Output(3), Tick, Exit(1), Kill],
            vec![None, None, exited(1), exited(1)],
        ),
        (
            3,
            vec![Tick, Output(4), Tick, Kill, Exit(2)],
            vec![None, None, None, killed, killed],
        ),
        (
            2,
            vec![Tick, Output(1), Tick, Exit(0), Tick],
            vec![None, None, detached, detached, detached],
        ),
        (
            1,
            vec![Tick, Kill, Output(2)],
            vec![detached, detached, detached],
        ),
        (0, vec![Output(5), Exit(0)], vec![detached, detached]),
    ];
    for (budget, steps, expected) in cases {
        assert_eq!(wait_transcript(budget, &steps).await, expected);
    }
}

/// Delegates to `inner`, but a read of the `eukhe.job` document `refused`
/// fails: the record of that job fails its commit, and every record in
/// the same batch with it.
struct RefusingJob {
    inner: MemoryStorage,
    refused: &'static str,
}

impl Storage for RefusingJob {
    fn commit<'a>(
        &'a self,
        writes: &'a [StorageWrite],
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Seq, StorageError>> {
        self.inner.commit(writes, cx)
    }

    fn mint_id(&self) -> BoxFuture<'_, Result<u64, StorageError>> {
        self.inner.mint_id()
    }

    fn conversation<'a>(
        &'a self,
        id: ConversationId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<ConversationRecord>, StorageError>> {
        self.inner.conversation(id, cx)
    }

    fn scan_conversations<'a>(
        &'a self,
        query: &'a ConversationQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<ConversationRecord>, StorageError>> {
        self.inner.scan_conversations(query, limit, cursor, cx)
    }

    fn entry<'a>(
        &'a self,
        id: EntryId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredEntry>, StorageError>> {
        self.inner.entry(id, cx)
    }

    fn entry_in<'a>(
        &'a self,
        conversation_id: ConversationId,
        id: EntryId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredEntry>, StorageError>> {
        self.inner.entry_in(conversation_id, id, cx)
    }

    fn find_latest_head_marker<'a>(
        &'a self,
        conversation_id: ConversationId,
        at_or_before_entry_id: Option<EntryId>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<EntryRecord>, StorageError>> {
        self.inner
            .find_latest_head_marker(conversation_id, at_or_before_entry_id, cx)
    }

    fn scan_entries<'a>(
        &'a self,
        query: &'a EntryQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<EntryRecord>, StorageError>> {
        self.inner.scan_entries(query, limit, cursor, cx)
    }

    fn task<'a>(
        &'a self,
        id: TaskId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<AnyTaskRecord>, StorageError>> {
        self.inner.task(id, cx)
    }

    fn scan_tasks<'a>(
        &'a self,
        query: &'a TaskQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<AnyTaskRecord>, StorageError>> {
        self.inner.scan_tasks(query, limit, cursor, cx)
    }

    fn submission<'a>(
        &'a self,
        id: SubmissionId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<SubmissionRecord>, StorageError>> {
        self.inner.submission(id, cx)
    }

    fn scan_submissions<'a>(
        &'a self,
        query: &'a SubmissionQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<SubmissionRecord>, StorageError>> {
        self.inner.scan_submissions(query, limit, cursor, cx)
    }

    fn submission_by_request<'a>(
        &'a self,
        conversation_id: ConversationId,
        request_id: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<SubmissionRecord>, StorageError>> {
        self.inner
            .submission_by_request(conversation_id, request_id, cx)
    }

    fn find_document<'a>(
        &'a self,
        address: &'a DocumentAddress,
        at: DocumentPoint,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<DocumentRecord>, StorageError>> {
        if address.kind == JOB_DOC_KIND && address.key.as_deref() == Some(self.refused) {
            return futures::future::ready(Err(StorageError::request("the job read is refused")))
                .boxed();
        }
        self.inner.find_document(address, at, cx)
    }

    fn document<'a>(
        &'a self,
        id: DocumentId,
        at: DocumentPoint,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredDocument>, StorageError>> {
        self.inner.document(id, at, cx)
    }

    fn scan_documents<'a>(
        &'a self,
        query: &'a DocumentQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<DocumentRecord>, StorageError>> {
        self.inner.scan_documents(query, limit, cursor, cx)
    }

    fn close<'a>(&'a self, cx: &'a Context) -> BoxFuture<'a, Result<(), StorageError>> {
        self.inner.close(cx)
    }
}

/// A batch whose commit fails loses no end: the writer commits the ends
/// one at a time, the end of an absent node retires nothing, and the end
/// that fails alone goes to the main conversation as a notice.
#[tokio::test]
async fn a_failed_batch_commits_its_ends_one_at_a_time_and_notes_the_one_that_fails() {
    let cx = &BACKGROUND_CONTEXT;
    let (_table, harness, root) = table_on(Arc::new(RefusingJob {
        inner: MemoryStorage::new(),
        refused: "bash-bad",
    }))
    .await;
    commit_start(&harness, &id("bash-good"), JobKind::UserBash, "sleep 1")
        .await
        .expect("the good start records");
    let (records, queue) = mpsc::unbounded_channel();
    for job in ["bash-bad", "bash-good", "bash-gone"] {
        records
            .send(JobEnded {
                id: id(job),
                end: JobEnd::Killed,
            })
            .expect("the queue is open");
    }
    drop(records);
    write_records(harness.clone(), queue).await;

    let good = harness
        .snapshot(&JOB_DOC, "bash-good", cx)
        .await
        .expect("a read")
        .is_some();
    // Each entry: its kind, and whether its model message names the job
    // whose end failed.
    let notices: Vec<(String, bool)> = root
        .entries(ConversationEntryQuery::default(), 100, None, cx)
        .await
        .expect("the entries")
        .items
        .iter()
        .map(|entry| {
            let model = format!("{:?}", entry.model);
            (
                entry.kind.clone(),
                model.contains("[job-record-failed]") && model.contains("the job bash-bad"),
            )
        })
        .collect();
    assert_eq!(
        (good, notices),
        (false, vec![("eukhe.custom".to_owned(), true)])
    );
    harness.close(cx).await.expect("close");
}
