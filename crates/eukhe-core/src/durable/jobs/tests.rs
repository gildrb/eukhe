use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::Duration;

use eukhe_ai::models::{create_models, CreateModelsOptions};
use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::errors::StorageError;
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::HarnessOptions;
use eukhe_durable::harness::{
    ConversationEntryQuery, Harness, OutputLimits, RootOptions, Truncation,
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

use super::tree::{write_records, JobRecord, JOB_DOC};
use super::{
    lock, wait_until, Job, JobEnd, JobEvent, JobKind, JobSpec, JobState, JobTable, Wait,
    JOB_DOC_KIND,
};

fn capped(max_bytes: usize) -> Truncation {
    Truncation::On(OutputLimits {
        max_bytes,
        ..OutputLimits::default()
    })
}

/// A job whose kill counts the signals it got in `kills`.
fn start(table: &JobTable, id: &str, truncation: Truncation, kills: &Arc<AtomicUsize>) -> Job {
    let kills = Arc::clone(kills);
    table.start(JobSpec {
        id: JobId::new(id).expect("id"),
        kind: JobKind::UserBash,
        label: "sleep 1".to_owned(),
        truncation,
        written: 0,
        kill: Box::new(move |_| {
            kills.fetch_add(1, Ordering::SeqCst);
        }),
    })
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

#[test]
fn a_capped_job_keeps_the_cap_counts_the_rest_and_reports_one_end() {
    let table = JobTable::default();
    let mut queue = table.take_queue().expect("queue");
    let kills = Arc::default();
    let job = start(&table, "bash-1", capped(10), &kills);
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
    // The writer gets the start and exactly one end.
    let mut records = Vec::new();
    while let Ok(record) = queue.try_recv() {
        records.push(match record {
            JobRecord::Start { id, kind, label } => format!("start {id} {} {label}", kind.name()),
            JobRecord::End { id, end } => format!("end {id} {end:?}"),
        });
    }
    assert_eq!(
        records,
        vec![
            "start bash-1 bash sleep 1".to_owned(),
            "end bash-1 Exited(3)".to_owned()
        ]
    );
    // An ended job takes no kill.
    job.kill();
    assert_eq!(kills.load(Ordering::SeqCst), 0);
}

#[test]
fn the_opt_out_keeps_every_byte() {
    let table = JobTable::default();
    let job = start(&table, "bash-1", Truncation::Off, &Arc::default());
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
#[test]
fn a_rewind_kills_the_running_jobs_that_started_after_its_target() {
    let table = JobTable::default();
    let kills = Arc::new(AtomicUsize::new(0));
    let _first = start(&table, "bash-first", Truncation::default(), &kills);
    lock(&table.entries).last = Some(Seq::from_number(4));
    let _before = start(&table, "bash-before", Truncation::default(), &kills);
    {
        let mut entries = lock(&table.entries);
        entries
            .commits
            .insert(EntryId::from_number(7), Seq::from_number(5));
        entries.last = Some(Seq::from_number(5));
    }
    let _orphan = start(&table, "bash-orphan", Truncation::default(), &kills);
    let ended = start(&table, "bash-ended", Truncation::default(), &kills);
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
#[test]
fn a_job_counts_the_output_written_before_it_started() {
    let table = JobTable::default();
    let job = table.start(JobSpec {
        id: JobId::new("shell-1").expect("id"),
        kind: JobKind::Shell,
        label: "yes | head".to_owned(),
        truncation: capped(10),
        written: 15,
        kill: Box::new(|_| {}),
    });
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

#[tokio::test(start_paused = true)]
async fn the_wait_settles_before_the_deadline_and_detaches_at_it() {
    let table = JobTable::default();
    let job = start(&table, "bash-1", Truncation::default(), &Arc::default());
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
    let late = start(&table, "bash-late", Truncation::default(), &Arc::default());
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

/// A batch whose commit fails loses no record: the writer commits the
/// records one at a time, the end of an absent node retires nothing, and
/// the record that fails alone goes to the main conversation as a notice.
#[tokio::test]
async fn a_failed_batch_commits_its_records_one_at_a_time_and_notes_the_one_that_fails() {
    let cx = &BACKGROUND_CONTEXT;
    let storage = Arc::new(RefusingJob {
        inner: MemoryStorage::new(),
        refused: "bash-bad",
    });
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
    let (records, queue) = mpsc::unbounded_channel();
    let id = |id: &str| JobId::new(id).expect("id");
    for record in [
        JobRecord::Start {
            id: id("bash-bad"),
            kind: JobKind::UserBash,
            label: "sleep 1".to_owned(),
        },
        JobRecord::Start {
            id: id("bash-good"),
            kind: JobKind::UserBash,
            label: "sleep 1".to_owned(),
        },
        JobRecord::End {
            id: id("bash-gone"),
            end: JobEnd::Killed,
        },
    ] {
        records.send(record).expect("the queue is open");
    }
    drop(records);
    write_records(harness.clone(), queue).await;

    let good = harness
        .snapshot(&JOB_DOC, "bash-good", cx)
        .await
        .expect("a read")
        .is_some();
    // Each entry: its kind, and whether its model message names the job
    // whose record failed.
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
        (true, vec![("eukhe.custom".to_owned(), true)])
    );
    harness.close(cx).await.expect("close");
}
