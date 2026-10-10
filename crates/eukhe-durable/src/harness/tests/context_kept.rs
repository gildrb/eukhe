//! Port of `test/harness-context.test.ts`, continued: task context reads
//! through each conversation's kept range (`countingSetup()` and the tests
//! that use it).

use std::collections::BTreeMap;
use std::fmt::Debug;
use std::future::Future;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use eukhe_chord::context::Context;
use eukhe_chord::json::JsonValue;
use eukhe_types::pi_ai::Message;
use futures::future::BoxFuture;
use futures::FutureExt;
use serde::{Deserialize, Serialize};

use super::support::{
    add_task, assistant, context, create_registry, describe_message, system, tool_result, user,
    AssistantOptions,
};
use super::task_support::{completed, deferred, Deferred};
use crate::errors::StorageError;
use crate::harness::registry::Registry;
use crate::harness::types::{
    Clock, ContextOptions, ContextView, ConversationCreateOptions, HarnessOptions, HarnessSettings,
    HarnessSettingsSource, LiveSettings,
};
use crate::harness::{Conversation, Harness, RootOptions};
use crate::session::{SessionError, SessionResult};
use crate::storage::MemoryStorage;
use crate::tasks::{define_task, AnyTask, NextTaskState, Task, TaskDefinition, TaskRuntime};
use crate::types::{
    AnyTaskRecord, ContextEdit, ContextEditAction, ConversationId, ConversationOwnership,
    ConversationQuery, ConversationRecord, Cursor, DocumentAddress, DocumentId, DocumentPoint,
    DocumentQuery, DocumentRecord, EntryDraft, EntryHead, EntryId, EntryQuery, EntryRecord,
    JoinPolicy, Page, Seq, Storage, StorageWrite, StoredDocument, StoredEntry, SubmissionId,
    SubmissionQuery, SubmissionRecord, TaskId, TaskOptions, TaskOutcome, TaskOwnership, TaskQuery,
};

fn lock<T>(value: &Mutex<T>) -> MutexGuard<'_, T> {
    value.lock().unwrap_or_else(PoisonError::into_inner)
}

fn json(text: &str) -> JsonValue {
    JsonValue::parse(text).expect("valid JSON literal")
}

/// TS `expect(actual).toEqual(expected)` inside a task handler: a mismatch
/// fails the task, whose outcome the test asserts, instead of panicking on
/// the scheduler.
fn expect_eq<T: PartialEq + Debug>(actual: &T, expected: &T, what: &str) -> SessionResult<()> {
    if actual == expected {
        Ok(())
    } else {
        Err(SessionError::error(format!(
            "{what}: {actual:?} != {expected:?}"
        )))
    }
}

fn described(messages: &[Message]) -> Vec<String> {
    messages.iter().map(describe_message).collect()
}

fn message(model: impl Into<Message>) -> EntryDraft {
    EntryDraft {
        model: Some(vec![model.into()]),
        ..EntryDraft::new("message")
    }
}

/// `MemoryStorage` that counts scanned entry rows (TS `countingSetup`'s
/// `Proxy`). When `hold` is set, the next range scan waits for it; bounds
/// probes (one row, on the Session line) do not.
struct Counting {
    inner: MemoryStorage,
    rows: AtomicUsize,
    hold: Mutex<Option<Deferred>>,
}

impl Counting {
    fn rows(&self) -> usize {
        self.rows.load(Ordering::SeqCst)
    }
}

impl Storage for Counting {
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
        let held = if limit > 1 {
            lock(&self.hold).take()
        } else {
            None
        };
        async move {
            if let Some(held) = held {
                held.wait().await;
            }
            let page = self.inner.scan_entries(query, limit, cursor, cx).await?;
            self.rows.fetch_add(page.items.len(), Ordering::SeqCst);
            Ok(page)
        }
        .boxed()
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

/// Options of [`counting_setup`] (TS `{ settings, now }`).
#[derive(Default)]
struct CountingOptions {
    settings: Option<HarnessSettings>,
    now: Option<Clock>,
}

struct CountingSetup {
    harness: Harness,
    registry: Registry,
    root: Conversation,
    first: EntryRecord,
    storage: Arc<Counting>,
}

impl CountingSetup {
    fn add(&self, task: AnyTask) {
        add_task(&self.registry, task, None).expect("install the test task");
    }

    /// `harness.commit((tx) => tx.createTask(task, input, { ownership: { kind: "conversation" }, conversationId: root.id }))`.
    async fn create<S: crate::tasks::TaskValue>(
        &self,
        task: &Task<JsonValue, S, (), ()>,
        input: &str,
    ) -> TaskId {
        let definition = task.as_definition_ref();
        let input = json(input);
        let root = self.root.id();
        self.harness
            .commit(
                move |tx| async move {
                    tx.create_task(
                        definition,
                        input,
                        TaskOptions {
                            ownership: TaskOwnership::Conversation,
                            conversation_id: Some(root),
                            background: None,
                            abandon_on_restart: None,
                        },
                    )
                    .await
                },
                context(),
            )
            .await
            .expect("create the task")
    }

    /// Create a task, wait for it to complete, and wait for the
    /// conversation to be idle.
    async fn run<S: crate::tasks::TaskValue>(
        &self,
        task: &Task<JsonValue, S, (), ()>,
        input: &str,
    ) {
        let id = self.create(task, input).await;
        assert_eq!(
            self.harness
                .wait_for_task(id, context())
                .await
                .unwrap()
                .outcome,
            done()
        );
        self.root.wait_for_idle(context()).await.unwrap();
    }
}

/// A Harness over `MemoryStorage` that counts scanned entry rows, with a
/// 21-entry root transcript.
async fn counting_setup(options: CountingOptions) -> CountingSetup {
    let storage = Arc::new(Counting {
        inner: MemoryStorage::new(),
        rows: AtomicUsize::new(0),
        hold: Mutex::new(None),
    });
    let registry = create_registry();
    let mut harness_options =
        HarnessOptions::new(super::support::create_models(), Arc::new(registry.clone()));
    harness_options.now = options.now;
    harness_options.settings = options
        .settings
        .map(|settings| Arc::new(LiveSettings::new(settings)) as Arc<dyn HarnessSettingsSource>);
    let harness = Harness::open(
        Arc::clone(&storage) as Arc<dyn Storage>,
        harness_options,
        context(),
    )
    .await
    .expect("open the Harness");
    let root = harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    let id = root.id();
    let first = root
        .commit(
            move |tx| async move { tx.append_entry(id, message(user("first"))).await },
            context(),
        )
        .await
        .unwrap();
    for index in 0..20 {
        root.commit(
            move |tx| async move {
                tx.append_entry(
                    id,
                    message(assistant(
                        &format!("old {index}"),
                        AssistantOptions::default(),
                    )),
                )
                .await
            },
            context(),
        )
        .await
        .unwrap();
    }
    CountingSetup {
        harness,
        registry,
        root,
        first,
        storage,
    }
}

/// Checkpoint of a one-phase task.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "camelCase")]
enum Run {
    Run,
}

type RunTask = Task<JsonValue, Run, (), ()>;
type RunRuntime = TaskRuntime<JsonValue, Run, (), ()>;

/// TS `DONE`.
fn done() -> TaskOutcome {
    TaskOutcome::Completed {
        result: JsonValue::Null,
    }
}

/// TS `ABORTED` as a next state.
fn aborted<S, R>() -> NextTaskState<S, R> {
    NextTaskState::Terminal {
        outcome: TaskOutcome::Aborted {
            reason: None,
            result: None,
        },
    }
}

/// Commit `DONE`.
fn complete<I, S, R>(
    runtime: &TaskRuntime<I, S, (), R>,
    cx: &Context,
) -> BoxFuture<'static, SessionResult<()>>
where
    I: crate::tasks::TaskValue,
    S: crate::tasks::TaskValue,
    R: Send + Sync + 'static,
{
    runtime.commit(|_, _| async { Ok(Some(completed(()))) }, cx)
}

/// A one-phase task named `name` whose abort handler commits `ABORTED`.
fn one_run<F, Fut>(name: &str, run: F) -> RunTask
where
    F: Fn(JsonValue, RunRuntime, Context) -> Fut + Send + Sync + 'static,
    Fut: Future<Output = SessionResult<()>> + Send + 'static,
{
    define_task(
        TaskDefinition::new(
            name,
            1,
            |_: &JsonValue| Ok(Run::Run),
            |_, runtime: RunRuntime, cx| async move {
                runtime
                    .commit(|_, _| async { Ok(Some(aborted())) }, &cx)
                    .await
            },
        )
        .phase("run", move |task, runtime, cx| run(task.input, runtime, cx)),
    )
}

/// TS `probeTask(read)`: reads its conversation's context once, named by
/// its input; `read` gets the name and the read to run.
fn probe_task<F, Fut>(read: F) -> RunTask
where
    F: Fn(String, BoxFuture<'static, SessionResult<ContextView>>, Context) -> Fut
        + Send
        + Sync
        + 'static,
    Fut: Future<Output = SessionResult<()>> + Send + 'static,
{
    let read = Arc::new(read);
    one_run("test.context-probe", move |input, runtime, cx| {
        let read = Arc::clone(&read);
        async move {
            let name = input["name"].as_str().unwrap_or_default().to_owned();
            let load = runtime.context(runtime.conversation_id(), &cx, ContextOptions::default());
            read(name, load, cx.clone()).await?;
            complete(&runtime, &cx).await
        }
    })
}

/// Rows per probe name.
type Rows = Arc<Mutex<BTreeMap<String, usize>>>;

fn rows_of(pairs: &[(&str, usize)]) -> BTreeMap<String, usize> {
    pairs
        .iter()
        .map(|(name, rows)| ((*name).to_owned(), *rows))
        .collect()
}

/// A probe that records the rows its read scanned.
fn counting_probe(storage: &Arc<Counting>, rows: &Rows) -> RunTask {
    let (storage, rows) = (Arc::clone(storage), Arc::clone(rows));
    probe_task(move |name, load, _cx| {
        let (storage, rows) = (Arc::clone(&storage), Arc::clone(&rows));
        async move {
            let before = storage.rows();
            load.await?;
            lock(&rows).insert(name, storage.rows() - before);
            Ok(())
        }
    })
}

#[tokio::test]
async fn extends_a_task_s_context_read_with_only_newer_entries() {
    let setup = counting_setup(CountingOptions::default()).await;
    let (root, first, storage) = (
        setup.root.clone(),
        setup.first.id,
        Arc::clone(&setup.storage),
    );
    let reads = one_run("test.context-reads", move |_input, runtime, cx| {
        let (root, storage) = (root.clone(), Arc::clone(&storage));
        async move {
            let id = root.id();
            let write = |draft: EntryDraft| {
                runtime.commit(
                    move |tx, _| async move {
                        tx.append_entry(id, draft).await?;
                        Ok(None)
                    },
                    &cx,
                )
            };
            let read = |at: Option<EntryId>| {
                let (runtime, storage, cx) = (runtime.clone(), Arc::clone(&storage), cx.clone());
                async move {
                    let before = storage.rows();
                    let view = runtime.context(id, &cx, ContextOptions { at }).await?;
                    SessionResult::Ok((view, storage.rows() - before))
                }
            };
            let whole = || root.context(&cx, ContextOptions::default());
            let (initial, _) = read(None).await?;
            expect_eq(&initial, &whole().await?, "initial")?;

            // Three new entries: the bounds probe reads one row, the extension the three new ones.
            write(message(user("new"))).await?;
            write(EntryDraft {
                data: Some(json(r#"{"text":"display only"}"#)),
                ..EntryDraft::new("note")
            })
            .await?;
            write(message(assistant("answer", AssistantOptions::default()))).await?;
            let (extended, rows) = read(None).await?;
            expect_eq(&rows, &4, "extended rows")?;
            expect_eq(&extended, &whole().await?, "extended")?;

            // A newer edit of an older entry applies to the extended range.
            write(EntryDraft {
                edits: Some(vec![ContextEdit {
                    target: first,
                    action: ContextEditAction::Omit,
                }]),
                ..EntryDraft::new("edit")
            })
            .await?;
            let (edited, rows) = read(None).await?;
            expect_eq(&rows, &2, "edited rows")?;
            expect_eq(&edited, &whole().await?, "edited")?;
            expect_eq(
                &described(&edited.messages).contains(&"user:first".to_owned()),
                &false,
                "first omitted",
            )?;

            // An earlier cutoff reuses the range.
            let cutoff = extended.entries.last().expect("entries").id;
            let (cut, rows) = read(Some(cutoff)).await?;
            expect_eq(&rows, &0, "cutoff rows")?;
            expect_eq(&cut, &extended, "cutoff")?;

            // A new head marker changes the range: read it whole.
            write(EntryDraft {
                head: Some(EntryHead::SelfEntry),
                model: Some(vec![user("fresh").into()]),
                ..EntryDraft::new("reset")
            })
            .await?;
            let (reset, _) = read(None).await?;
            expect_eq(&reset, &whole().await?, "reset")?;
            expect_eq(
                &described(&reset.messages),
                &vec!["user:fresh".to_owned()],
                "reset messages",
            )?;

            complete(&runtime, &cx).await
        }
    });
    setup.add(reads.erase());
    let id = setup.create(&reads, "{}").await;
    setup.harness.resume().unwrap();
    let settled = setup.harness.wait_for_task(id, context()).await.unwrap();
    assert_eq!(settled.outcome, done());
    setup.harness.close(context()).await.unwrap();
}

/// Checkpoint of the parent in
/// [`keeps_a_conversation_s_context_read_across_its_tasks_and_for_the_retention_period_once_idle`].
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "camelCase")]
enum ParentPhase {
    Start,
    After,
}

#[tokio::test]
#[expect(clippy::too_many_lines, reason = "one TS case, ported whole")]
async fn keeps_a_conversation_s_context_read_across_its_tasks_and_for_the_retention_period_once_idle(
) {
    let clock = Arc::new(Mutex::new(1_000.0_f64));
    let now: Clock = {
        let clock = Arc::clone(&clock);
        Arc::new(move || *lock(&clock))
    };
    let setup = counting_setup(CountingOptions {
        now: Some(now),
        ..CountingOptions::default()
    })
    .await;
    let rows: Rows = Arc::default();
    // TS `read(name, load, taskContext)`: record the rows and compare with a whole read.
    let read = {
        let (root, storage, rows) = (
            setup.root.clone(),
            Arc::clone(&setup.storage),
            Arc::clone(&rows),
        );
        Arc::new(
            move |name: &str, load: BoxFuture<'static, SessionResult<ContextView>>, cx: Context| {
                let (root, storage, rows, name) = (
                    root.clone(),
                    Arc::clone(&storage),
                    Arc::clone(&rows),
                    name.to_owned(),
                );
                async move {
                    let before = storage.rows();
                    let view = load.await?;
                    lock(&rows).insert(name.clone(), storage.rows() - before);
                    expect_eq(
                        &view,
                        &root.context(&cx, ContextOptions::default()).await?,
                        &name,
                    )
                }
            },
        )
    };
    let root_id = setup.root.id();
    let child = {
        let read = Arc::clone(&read);
        one_run("test.context-child", move |_input, runtime, cx| {
            let read = Arc::clone(&read);
            async move {
                runtime
                    .commit(
                        move |tx, _| async move {
                            tx.append_entry(root_id, message(user("from child")))
                                .await?;
                            Ok(None)
                        },
                        &cx,
                    )
                    .await?;
                read(
                    "child",
                    runtime.context(root_id, &cx, ContextOptions::default()),
                    cx.clone(),
                )
                .await?;
                complete(&runtime, &cx).await
            }
        })
    };
    let spawned = child.clone();
    let start_read = Arc::clone(&read);
    let parent: Task<JsonValue, ParentPhase, (), ()> = define_task(
        TaskDefinition::new(
            "test.context-parent",
            1,
            |_: &JsonValue| Ok(ParentPhase::Start),
            |_, runtime: TaskRuntime<JsonValue, ParentPhase, (), ()>, cx| async move {
                runtime
                    .commit(|_, _| async { Ok(Some(aborted())) }, &cx)
                    .await
            },
        )
        .phase("start", move |task, runtime, cx| {
            let (read, child) = (Arc::clone(&start_read), spawned.clone());
            async move {
                read(
                    "parent",
                    runtime.context(root_id, &cx, ContextOptions::default()),
                    cx.clone(),
                )
                .await?;
                let owner = task.id.erase();
                runtime
                    .commit(
                        move |tx, _| async move {
                            let child = tx
                                .create_task(
                                    child.as_definition_ref(),
                                    json("{}"),
                                    TaskOptions {
                                        ownership: TaskOwnership::Task { task_id: owner },
                                        conversation_id: Some(root_id),
                                        background: None,
                                        abandon_on_restart: None,
                                    },
                                )
                                .await?;
                            Ok(Some(NextTaskState::Waiting {
                                checkpoint: ParentPhase::After,
                                on: vec![child],
                                policy: JoinPolicy::AllSettled,
                            }))
                        },
                        &cx,
                    )
                    .await
            }
        })
        .phase("after", move |_task, runtime, cx| {
            let read = Arc::clone(&read);
            async move {
                read(
                    "after",
                    runtime.context(root_id, &cx, ContextOptions::default()),
                    cx.clone(),
                )
                .await?;
                complete(&runtime, &cx).await
            }
        }),
    );
    let probe = counting_probe(&setup.storage, &rows);
    for task in [child.erase(), parent.erase(), probe.erase()] {
        setup.add(task);
    }
    setup.harness.resume().unwrap();
    setup.run(&parent, "{}").await;
    setup.run(&probe, r#"{"name":"idle"}"#).await;
    *lock(&clock) += 600_000.0;
    setup.run(&probe, r#"{"name":"expired"}"#).await;
    // Bounds probes read one row each. The child scans its own new entry; the waiting parent's later invocation and
    // the probe within the retention period scan nothing new. After it, the probe reads the whole transcript again.
    assert_eq!(
        *lock(&rows),
        rows_of(&[
            ("parent", 22),
            ("child", 2),
            ("after", 1),
            ("idle", 1),
            ("expired", 23),
        ])
    );
    setup.harness.close(context()).await.unwrap();
}

/// Deterministic pseudo-random transcript writer of
/// [`derives_the_same_view_from_extended_reads_as_from_whole_reads`].
struct Steps {
    seed: u32,
    seen: BTreeMap<&'static str, usize>,
    written: Vec<EntryRecord>,
    calls: Vec<String>,
    next: usize,
}

impl Steps {
    /// 32-bit LCG, high bits.
    fn random(&mut self, n: usize) -> usize {
        self.seed = self
            .seed
            .wrapping_mul(1_664_525)
            .wrapping_add(1_013_904_223);
        let scaled = (u64::from(self.seed) * n as u64) >> 32;
        usize::try_from(scaled).expect("below n")
    }

    /// TS `written[random(written.length)]!.id`.
    fn pick_written(&mut self) -> EntryId {
        let index = self.random(self.written.len());
        self.written[index].id
    }

    fn count(&mut self, category: &'static str) {
        *self.seen.entry(category).or_default() += 1;
    }

    fn next(&mut self) -> usize {
        let next = self.next;
        self.next += 1;
        next
    }

    fn user(&mut self) -> EntryDraft {
        self.count("user");
        let text = format!("u{}", self.next());
        message(user(&text))
    }

    fn draft(&mut self) -> EntryDraft {
        let pick = self.random(14);
        if pick < 3 {
            return self.user();
        }
        if pick < 5 {
            let length = self.random(3);
            let ids: Vec<String> = (0..length).map(|_| format!("c{}", self.next())).collect();
            self.calls.extend(ids.iter().cloned());
            let stop_reason = [
                eukhe_types::pi_ai::StopReason::Aborted,
                eukhe_types::pi_ai::StopReason::Error,
                eukhe_types::pi_ai::StopReason::Deferred,
            ]
            .get(self.random(9))
            .copied();
            self.count(match stop_reason {
                Some(eukhe_types::pi_ai::StopReason::Aborted) => "aborted",
                Some(eukhe_types::pi_ai::StopReason::Error) => "error",
                Some(_) => "deferred",
                None => "assistant",
            });
            let refs: Vec<&str> = ids.iter().map(String::as_str).collect();
            let text = format!("a{}", self.next());
            return message(assistant(
                &text,
                AssistantOptions {
                    calls: &refs,
                    stop_reason,
                },
            ));
        }
        if pick < 8 {
            let matched = !self.calls.is_empty() && self.random(5) > 0;
            self.count(if matched { "result" } else { "stray result" });
            let id = if matched {
                let index = self.random(self.calls.len());
                self.calls.remove(index)
            } else {
                format!("stray{}", self.next())
            };
            return message(tool_result(&id, None));
        }
        if pick < 9 {
            self.count("system");
            let value = format!("v{}", self.next());
            let sections = [("s".to_owned(), Some(value))].into_iter().collect();
            return message(system(sections));
        }
        if pick < 10 {
            self.count("note");
            let n = self.next();
            return EntryDraft {
                data: Some(json(&format!(r#"{{"n":{n}}}"#))),
                ..EntryDraft::new("note")
            };
        }
        let index = self.random(self.written.len());
        let target = self.written.get(index).map(|entry| entry.id);
        if let (true, Some(target)) = (pick < 12, target) {
            let omit = self.random(2) == 0;
            self.count(if omit { "omit" } else { "replace" });
            let action = if omit {
                ContextEditAction::Omit
            } else {
                let text = format!("r{}", self.next());
                ContextEditAction::Replace {
                    messages: vec![user(&text).into()],
                }
            };
            return EntryDraft {
                edits: Some(vec![ContextEdit { target, action }]),
                ..EntryDraft::new("edit")
            };
        }
        if let (true, Some(target)) = (pick < 13, target) {
            self.count("head");
            let text = format!("h{}", self.next());
            return EntryDraft {
                head: Some(EntryHead::Entry(target)),
                model: Some(vec![user(&text).into()]),
                ..EntryDraft::new("summary")
            };
        }
        self.user()
    }
}

#[tokio::test]
#[expect(clippy::too_many_lines, reason = "one TS case, ported whole")]
async fn derives_the_same_view_from_extended_reads_as_from_whole_reads() {
    let setup = counting_setup(CountingOptions::default()).await;
    // Deterministic pseudo-random transcript (32-bit LCG, high bits): calls and results in any order, missing and
    // stray results, excluded stop reasons, system entries, notes, edits of earlier entries, and head markers.
    let steps = Arc::new(Mutex::new(Steps {
        seed: 7,
        seen: BTreeMap::new(),
        written: Vec::new(),
        calls: Vec::new(),
        next: 0,
    }));
    let root = setup.root.clone();
    let task_steps = Arc::clone(&steps);
    let task = one_run("test.context-steps", move |_input, runtime, cx| {
        let (root, steps) = (root.clone(), Arc::clone(&task_steps));
        async move {
            let append = |conversation_id: ConversationId| {
                let steps = Arc::clone(&steps);
                runtime.commit(
                    move |tx, _| async move {
                        let added = 1 + lock(&steps).random(3);
                        for _ in 0..added {
                            let draft = lock(&steps).draft();
                            let entry = tx.append_entry(conversation_id, draft).await?;
                            lock(&steps).written.push(entry);
                        }
                        Ok(None)
                    },
                    &cx,
                )
            };
            let whole = ContextOptions::default;
            for step in 0..150 {
                append(root.id()).await?;
                expect_eq(
                    &runtime.context(root.id(), &cx, whole()).await?,
                    &root.context(&cx, whole()).await?,
                    &format!("step {step}"),
                )?;
                if step % 10 == 9 {
                    // Overlapping reads, one with an earlier cutoff, share the kept range.
                    let at = lock(&steps).pick_written();
                    let (whole_view, cut) = futures::join!(
                        runtime.context(root.id(), &cx, whole()),
                        runtime.context(root.id(), &cx, ContextOptions { at: Some(at) }),
                    );
                    expect_eq(&whole_view?, &root.context(&cx, whole()).await?, "whole")?;
                    expect_eq(
                        &cut?,
                        &root.context(&cx, ContextOptions { at: Some(at) }).await?,
                        "cut",
                    )?;
                }
            }
            // A fork sees its parent's entries through the fork point and extends with its own.
            let at = lock(&steps).pick_written();
            let fork = root
                .fork(
                    at,
                    ConversationCreateOptions::new(ConversationOwnership::Ownerless),
                    &cx,
                )
                .await?;
            for step in 0..20 {
                expect_eq(
                    &runtime.context(fork.id(), &cx, whole()).await?,
                    &fork.context(&cx, whole()).await?,
                    &format!("fork step {step}"),
                )?;
                append(fork.id()).await?;
            }
            complete(&runtime, &cx).await
        }
    });
    setup.add(task.erase());
    setup.harness.resume().unwrap();
    let id = setup.create(&task, "{}").await;
    assert_eq!(
        setup
            .harness
            .wait_for_task(id, context())
            .await
            .unwrap()
            .outcome,
        done()
    );
    let seen = lock(&steps).seen.clone();
    for category in [
        "user",
        "assistant",
        "aborted",
        "error",
        "deferred",
        "result",
        "stray result",
        "system",
        "note",
        "omit",
        "replace",
        "head",
    ] {
        assert!(
            seen.get(category).copied().unwrap_or(0) > 0,
            "{category} was not written"
        );
    }
    setup.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn keeps_returned_views_and_kept_ranges_apart() {
    let setup = counting_setup(CountingOptions::default()).await;
    let root = setup.root.clone();
    let task = one_run("test.context-mutate", move |_input, runtime, cx| {
        let root = root.clone();
        async move {
            let mut view = runtime
                .context(root.id(), &cx, ContextOptions::default())
                .await?;
            view.messages.clear();
            view.entries.pop();
            // TS also asserts kept entries are frozen like MemoryStorage records: a returned view is owned in Rust,
            // so no write through it reaches the kept range.
            expect_eq(
                &runtime
                    .context(root.id(), &cx, ContextOptions::default())
                    .await?,
                &root.context(&cx, ContextOptions::default()).await?,
                "kept range",
            )?;
            complete(&runtime, &cx).await
        }
    });
    setup.add(task.erase());
    setup.harness.resume().unwrap();
    let id = setup.create(&task, "{}").await;
    assert_eq!(
        setup
            .harness
            .wait_for_task(id, context())
            .await
            .unwrap()
            .outcome,
        done()
    );
    setup.harness.close(context()).await.unwrap();
}

// "freezes kept entries deeply even when storage freezes them shallowly": no Rust counterpart; Rust values are
// immutable through shared references, so there is no `Object.freeze` depth to test.

#[tokio::test]
async fn does_not_keep_a_read_that_finishes_after_its_task_ended() {
    let setup = counting_setup(CountingOptions {
        settings: Some(HarnessSettings {
            context_retention_ms: Some(0.0),
            ..HarnessSettings::default()
        }),
        ..CountingOptions::default()
    })
    .await;
    let scans: Deferred = deferred();
    let probe_start: Deferred = deferred();
    let late: Arc<Mutex<Option<tokio::task::JoinHandle<SessionResult<ContextView>>>>> =
        Arc::default();
    let late_task = {
        let (storage, scans, late, root_id) = (
            Arc::clone(&setup.storage),
            scans.clone(),
            Arc::clone(&late),
            setup.root.id(),
        );
        one_run("test.context-late", move |_input, runtime, cx| {
            *lock(&storage.hold) = Some(scans.clone());
            // Spawned so the read starts now, as the TS promise does.
            *lock(&late) = Some(tokio::spawn(runtime.context(
                root_id,
                &cx,
                ContextOptions::default(),
            )));
            async move { complete(&runtime, &cx).await }
        })
    };
    let rows: Rows = Arc::default();
    let probe = {
        let (storage, rows, probe_start) = (
            Arc::clone(&setup.storage),
            Arc::clone(&rows),
            probe_start.clone(),
        );
        probe_task(move |name, load, _cx| {
            let (storage, rows, probe_start) =
                (Arc::clone(&storage), Arc::clone(&rows), probe_start.clone());
            async move {
                probe_start.wait().await;
                let before = storage.rows();
                load.await?;
                lock(&rows).insert(name, storage.rows() - before);
                Ok(())
            }
        })
    };
    for task in [late_task.erase(), probe.erase()] {
        setup.add(task);
    }
    setup.harness.resume().unwrap();
    let late_id = setup.create(&late_task, "{}").await;
    assert_eq!(
        setup
            .harness
            .wait_for_task(late_id, context())
            .await
            .unwrap()
            .outcome,
        done()
    );
    // The conversation is busy again when the late read finishes; its range must not be kept.
    let probe_id = setup.create(&probe, r#"{"name":"probe"}"#).await;
    scans.resolve(());
    let handle = lock(&late).take().expect("the late read started");
    // Its result does not matter (TS `.catch((error) => error)`).
    let _ = handle.await.expect("the late read does not panic");
    probe_start.resolve(());
    assert_eq!(
        setup
            .harness
            .wait_for_task(probe_id, context())
            .await
            .unwrap()
            .outcome,
        done()
    );
    assert_eq!(*lock(&rows), rows_of(&[("probe", 22)]));
    setup.harness.close(context()).await.unwrap();
}

#[tokio::test(start_paused = true)]
async fn drops_an_idle_conversation_s_context_read_on_a_timer_when_nothing_else_runs() {
    // Rust: tokio's paused clock stands in for `vi.useFakeTimers()`, and the Harness clock follows it like the faked
    // `Date`. tokio exposes no timer count, so the `vi.getTimerCount()` checks are dropped; the second probe reading
    // the whole transcript shows the timer dropped the kept read.
    let start = tokio::time::Instant::now();
    let now: Clock = Arc::new(move || start.elapsed().as_secs_f64() * 1000.0 + 1.0);
    let setup = counting_setup(CountingOptions {
        settings: Some(HarnessSettings {
            context_retention_ms: Some(1_000.0),
            ..HarnessSettings::default()
        }),
        now: Some(now),
    })
    .await;
    let rows: Rows = Arc::default();
    let probe = counting_probe(&setup.storage, &rows);
    setup.add(probe.erase());
    setup.harness.resume().unwrap();
    setup.run(&probe, r#"{"name":"first"}"#).await;
    tokio::time::advance(std::time::Duration::from_millis(1_000)).await;
    setup.run(&probe, r#"{"name":"second"}"#).await;
    assert_eq!(*lock(&rows), rows_of(&[("first", 22), ("second", 22)]));
    setup.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn drops_a_conversation_s_context_read_once_idle_with_zero_retention() {
    let setup = counting_setup(CountingOptions {
        settings: Some(HarnessSettings {
            context_retention_ms: Some(0.0),
            ..HarnessSettings::default()
        }),
        ..CountingOptions::default()
    })
    .await;
    let rows: Rows = Arc::default();
    let probe = counting_probe(&setup.storage, &rows);
    setup.add(probe.erase());
    setup.harness.resume().unwrap();
    for name in ["first", "second"] {
        setup.run(&probe, &format!(r#"{{"name":"{name}"}}"#)).await;
    }
    assert_eq!(*lock(&rows), rows_of(&[("first", 22), ("second", 22)]));
    setup.harness.close(context()).await.unwrap();
}
