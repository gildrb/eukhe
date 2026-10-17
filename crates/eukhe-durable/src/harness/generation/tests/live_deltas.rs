//! Port of `test/harness-live-deltas.test.ts`. A running tool's progress
//! reaches the live observers and never storage (docs/runtime.md S2), so
//! the tool steps below check the change each publication delivers and
//! that no commit carried it.

use std::collections::{HashMap, VecDeque};
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_text, faux_tool_call, FauxAssistantMessageOptions, FauxTokenSize,
    RegisterFauxProviderOptions,
};
use eukhe_chord::context::Context;
use eukhe_chord::delta::Op;
use eukhe_chord::json::{JsonObject, JsonValue};
use eukhe_types::pi_ai::{AssistantContentBlock, StopReason, Usage};
use futures::future::BoxFuture;
use futures::FutureExt;
use tokio::sync::Notify;

use crate::errors::StorageError;
use crate::harness::define::define_tool;
use crate::harness::events::ToolOutputUpdate;
use crate::harness::live::progress::ProgressChange;
use crate::harness::live::{SlotProgress, LIVE_DOC};
use crate::harness::submissions::SubmissionHandle;
use crate::harness::tests::chat_support::{chat_setup, open_chat, wait_for, OpenChat};
use crate::harness::tests::support::{add_tool, context, empty_object_schema};
use crate::harness::types::{
    InputSubmissionDraft, OutputRetain, ToolDiagnostic, ToolDiagnosticSeverity, ToolExecutionApi,
    ToolExecutionMode, ToolExecutionResult, ToolOutputChunk, ToolRegistration,
};
use crate::harness::{ConversationEntryQuery, Harness, OutputLimits, Truncation};
use crate::session::tests::support::document_changes;
use crate::session::SessionError;
use crate::storage::MemoryStorage;
use crate::types::{
    AnyTaskRecord, CheckpointInfo, CommitChange, ConversationId, ConversationQuery,
    ConversationRecord, Cursor, DocumentAddress, DocumentContent, DocumentId, DocumentPoint,
    DocumentQuery, DocumentRecord, EntryId, EntryQuery, EntryRecord, Page, Seq, Storage,
    StorageWrite, StoredDocument, StoredEntry, SubmissionId, SubmissionQuery, SubmissionRecord,
    TaskId, TaskQuery,
};

const WAIT_MS: u64 = 5000;

type Commits = Arc<Mutex<Vec<Vec<serde_json::Value>>>>;
type Changes = Arc<Mutex<Vec<ProgressChange>>>;
type Action = Box<dyn FnOnce(Arc<dyn ToolExecutionApi>) -> BoxFuture<'static, bool> + Send>;

fn json(text: &str) -> serde_json::Value {
    serde_json::from_str(text).expect("valid JSON literal")
}

fn op_json(op: &Op) -> serde_json::Value {
    serde_json::Value::from(&op.to_json())
}

fn input(text: &str) -> InputSubmissionDraft {
    InputSubmissionDraft::new(text)
}

fn tool_use() -> FauxAssistantMessageOptions {
    FauxAssistantMessageOptions {
        stop_reason: Some(StopReason::ToolUse),
        ..FauxAssistantMessageOptions::default()
    }
}

fn call(name: &str, id: &str) -> AssistantContentBlock {
    faux_tool_call(name, serde_json::Map::new(), Some(id.to_owned()))
}

fn done() -> eukhe_types::pi_ai::AssistantMessage {
    faux_assistant_message(
        vec![faux_text("done")],
        FauxAssistantMessageOptions::default(),
    )
}

fn lock<T>(value: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    value.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Record the operations of every `pi.live` commit that has some.
fn record_commits(harness: &Harness) -> Commits {
    let commits: Commits = Arc::default();
    let sink = Arc::clone(&commits);
    // The listener stays registered for the Harness's lifetime.
    drop(
        harness
            .subscribe_commits(Arc::new(move |publication, _| {
                for change in document_changes(publication) {
                    if change.record.kind == "pi.live" && !change.ops.is_empty() {
                        lock(&sink).push(change.ops.iter().map(op_json).collect());
                    }
                }
            }))
            .unwrap(),
    );
    commits
}

/// vitest `expect.arrayContaining`.
fn contains_all(actual: &[serde_json::Value], expected: &[serde_json::Value]) -> bool {
    expected.iter().all(|item| actual.contains(item))
}

fn assert_contains_all(actual: &[serde_json::Value], expected: &[serde_json::Value]) {
    assert!(
        contains_all(actual, expected),
        "{actual:?} does not contain {expected:?}"
    );
}

async fn live(harness: &Harness, conversation: ConversationId) -> serde_json::Value {
    match harness
        .snapshot(&LIVE_DOC, conversation, context())
        .await
        .unwrap()
    {
        Some(value) => serde_json::Value::from(&JsonValue::Object(value)),
        None => serde_json::Value::Null,
    }
}

/// One tool call driven step by step, capturing the exact Chord operations
/// of every `pi.live` commit and every change its progress publications
/// delivered to the live observers.
struct Drive {
    harness: Harness,
    conversation: ConversationId,
    commits: Commits,
    changes: Changes,
    actions: Arc<Mutex<VecDeque<Action>>>,
    wake: Arc<Notify>,
    submission: SubmissionHandle,
}

impl Drive {
    fn push(&self, action: Action) {
        lock(&self.actions).push_back(action);
        self.wake.notify_one();
    }

    /// Run one action inside the tool, without waiting for what it does.
    fn act<F>(&self, action: F)
    where
        F: FnOnce(Arc<dyn ToolExecutionApi>) -> BoxFuture<'static, ()> + Send + 'static,
    {
        self.push(Box::new(move |api| {
            async move {
                action(api).await;
                true
            }
            .boxed()
        }));
    }

    /// Run one action inside the tool and return the change its
    /// publication delivered; no commit carries it.
    async fn step<F>(&self, action: F) -> ProgressChange
    where
        F: FnOnce(Arc<dyn ToolExecutionApi>) -> BoxFuture<'static, ()> + Send + 'static,
    {
        let (commits, changes) = (lock(&self.commits).len(), lock(&self.changes).len());
        self.act(action);
        wait_for(
            || {
                let grown = lock(&self.changes).len() > changes;
                async move { grown }
            },
            WAIT_MS,
        )
        .await;
        assert_eq!(
            lock(&self.commits).len(),
            commits,
            "progress commits nothing"
        );
        lock(&self.changes).last().cloned().unwrap()
    }

    /// What the call published last, as an observer that attaches now
    /// finds it.
    fn published(&self) -> Option<SlotProgress> {
        let (current, stop) = self
            .harness
            .core()
            .live_progress()
            .watch(self.conversation, Arc::new(|_, _, _| {}));
        stop();
        current.into_values().next()
    }

    /// Let the tool return and the run finish; returns the commits made meanwhile.
    async fn finish(&self) -> Vec<Vec<serde_json::Value>> {
        let before = lock(&self.commits).len();
        self.push(Box::new(|_| async { false }.boxed()));
        self.submission.wait(context()).await.unwrap();
        lock(&self.commits)[before..].to_vec()
    }

    fn commits(&self) -> Vec<Vec<serde_json::Value>> {
        lock(&self.commits).clone()
    }
}

async fn drive(truncation: Truncation) -> Drive {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let actions: Arc<Mutex<VecDeque<Action>>> = Arc::default();
    let wake = Arc::new(Notify::new());
    let (queue, waker) = (Arc::clone(&actions), Arc::clone(&wake));
    let mut tool = ToolRegistration::new(
        "drive",
        "Driven by the test",
        empty_object_schema(),
        move |_, api, cx| {
            let (queue, waker) = (Arc::clone(&queue), Arc::clone(&waker));
            async move {
                let signal = cx.abort_signal().expect("a call signal");
                loop {
                    let action = loop {
                        if let Some(action) = lock(&queue).pop_front() {
                            break action;
                        }
                        tokio::select! {
                            () = waker.notified() => {}
                            reason = signal.cancelled() => return Err(SessionError::Aborted(reason)),
                        }
                    };
                    if !action(Arc::clone(&api)).await {
                        return Ok(ToolExecutionResult::default());
                    }
                }
            }
        },
    );
    tool.truncation = truncation;
    add_tool(&setup.registry, define_tool(tool), None).unwrap();
    setup.faux.set_responses(vec![
        faux_assistant_message(vec![call("drive", "c1")], tool_use()).into(),
        done().into(),
    ]);
    let OpenChat { harness, root } = open_chat(Arc::new(MemoryStorage::new()), &setup, None)
        .await
        .unwrap();
    let commits = record_commits(&harness);
    let changes: Changes = Arc::default();
    let sink = Arc::clone(&changes);
    // The watch stays registered for the Harness's lifetime.
    let (_, _watch) = harness.core().live_progress().watch(
        root.id(),
        Arc::new(move |_, _, change| lock(&sink).push(change.clone())),
    );
    let submission = root.submit(input("go"), context()).await.unwrap();
    let conversation = root.id();
    wait_for(
        || async { live(&harness, conversation).await["tools"][0]["status"] == "running" },
        WAIT_MS,
    )
    .await;
    Drive {
        harness,
        conversation,
        commits,
        changes,
        actions,
        wake,
        submission,
    }
}

fn limits(max_lines: usize, retain: OutputRetain) -> Truncation {
    Truncation::On(OutputLimits {
        max_lines,
        retain,
        ..OutputLimits::default()
    })
}

fn output_change(output: ToolOutputUpdate) -> ProgressChange {
    ProgressChange {
        output: Some(output),
        details: None,
        diagnostics: None,
    }
}

fn set(text: &str) -> ProgressChange {
    output_change(ToolOutputUpdate::Set {
        set: text.to_owned(),
    })
}

fn window(trim_start: Option<usize>, append: &str) -> ProgressChange {
    output_change(ToolOutputUpdate::Window {
        trim_start,
        append: Some(append.to_owned()),
    })
}

fn print(
    text: &'static str,
) -> impl FnOnce(Arc<dyn ToolExecutionApi>) -> BoxFuture<'static, ()> + Send {
    move |api| {
        api.output(ToolOutputChunk::Text(text), None).unwrap();
        async {}.boxed()
    }
}

fn print_owned(
    text: String,
) -> impl FnOnce(Arc<dyn ToolExecutionApi>) -> BoxFuture<'static, ()> + Send {
    move |api| {
        api.output(ToolOutputChunk::Text(&text), None).unwrap();
        async {}.boxed()
    }
}

fn details(value: &str) -> impl FnOnce(Arc<dyn ToolExecutionApi>) -> BoxFuture<'static, ()> + Send {
    let value = JsonValue::parse(value).expect("valid JSON literal");
    move |api| async move { api.details(value, context()).await.unwrap() }.boxed()
}

fn diagnostic(
    diagnostic: ToolDiagnostic,
) -> impl FnOnce(Arc<dyn ToolExecutionApi>) -> BoxFuture<'static, ()> + Send {
    move |api| {
        api.diagnostic(diagnostic).unwrap();
        async {}.boxed()
    }
}

fn noop(name: &str) -> Arc<ToolRegistration> {
    define_tool(ToolRegistration::new(
        name,
        name,
        empty_object_schema(),
        |_, _, _| async {
            Ok(ToolExecutionResult {
                output: Some(Vec::new()),
                ..ToolExecutionResult::default()
            })
        },
    ))
}

#[tokio::test(flavor = "multi_thread")]
async fn hands_a_generation_over_to_its_tool_round_and_starts_a_tool_with_one_field_write_each() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_tool(&setup.registry, noop("noop"), None).unwrap();
    setup.faux.set_responses(vec![
        faux_assistant_message(vec![call("noop", "c1")], tool_use()).into(),
        done().into(),
    ]);
    let OpenChat { harness, root } = open_chat(Arc::new(MemoryStorage::new()), &setup, None)
        .await
        .unwrap();
    let commits = record_commits(&harness);
    let submission = root.submit(input("go"), context()).await.unwrap();
    submission.wait(context()).await.unwrap();
    let root_id = root.id();
    let tasks = harness
        .commit(
            move |tx| async move {
                tx.scan_tasks(
                    TaskQuery {
                        conversation_id: Some(root_id),
                        ..TaskQuery::default()
                    },
                    20,
                    None,
                )
                .await
            },
            context(),
        )
        .await
        .unwrap();
    let id = |kind: &str| -> Vec<u64> {
        let mut ids: Vec<u64> = tasks
            .items
            .iter()
            .filter(|task| task.kind == kind)
            .map(|task| task.id.get())
            .collect();
        ids.sort_unstable();
        ids
    };
    let (generations, tool) = (id("pi.generation"), id("pi.tool")[0]);
    let (first_generation, second_generation) = (generations[0], generations[1]);
    let entries = root
        .entries(ConversationEntryQuery::default(), 10, None, context())
        .await
        .unwrap();
    let result = entries
        .items
        .iter()
        .find(|entry| entry.kind == "pi.tool-result")
        .unwrap()
        .id
        .get();
    let commits = lock(&commits).clone();
    assert_eq!(commits.len(), 8, "{commits:?}");
    // submission
    assert_eq!(
        commits[0],
        [
            serde_json::json!(["s", ["run"], { "taskId": first_generation, "inputs": [submission.id().get()] }])
        ]
    );
    // request
    assert_eq!(commits[1], [json(r#"["s",["generation"],{"attempt":1}]"#)]);
    // the generation starts its tool round and keeps the run
    assert_contains_all(
        &commits[2],
        &[
            json(r#"["d",["generation"]]"#),
            serde_json::json!(["s", ["tools"], [{ "callId": "c1", "name": "noop", "taskId": tool, "status": "pending" }]]),
        ],
    );
    // intent
    assert_eq!(
        commits[3],
        [json(r#"["s",["tools",0,"status"],"running"]"#)]
    );
    // result
    assert_contains_all(
        &commits[4],
        &[
            json(r#"["s",["tools",0,"status"],"done"]"#),
            serde_json::json!(["s", ["tools", 0, "entry"], result]),
        ],
    );
    // the generation's tools phase hands the run to the next generation
    assert_contains_all(
        &commits[5],
        &[
            json(r#"["d",["tools"]]"#),
            serde_json::json!(["s", ["run", "taskId"], second_generation]),
        ],
    );
    assert_eq!(commits[6], [json(r#"["s",["generation"],{"attempt":1}]"#)]);
    // the answer ends the run
    assert_contains_all(
        &commits[7],
        &[json(r#"["d",["run"]]"#), json(r#"["d",["generation"]]"#)],
    );
    assert_eq!(commits[2].len(), 2);
    assert_eq!(commits[4].len(), 2);
    assert_eq!(commits[5].len(), 2);
    harness.close(context()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn publishes_head_output_and_then_only_the_dropped_counts_once_the_window_is_full() {
    let run = drive(limits(2, OutputRetain::Head)).await;
    let started = run.commits().len();
    assert_eq!(run.step(print("one\n")).await, set("one\n"));
    assert_eq!(run.step(print("two\n")).await, window(None, "two\n"));
    // The window is full: the retained text stays, so no change reaches the
    // observers; only the counts a late observer finds grow.
    run.act(print("three\n"));
    run.act(print("four\n"));
    let full = SlotProgress {
        output: Some("one\ntwo\n".to_owned()),
        dropped_bytes: Some(11),
        dropped_lines: Some(2),
        ..SlotProgress::default()
    };
    wait_for(
        || {
            let published = run.published() == Some(full.clone());
            async move { published }
        },
        WAIT_MS,
    )
    .await;
    assert_eq!(
        (lock(&run.changes).len(), run.commits().len()),
        (2, started)
    );
    run.finish().await;
    run.harness.close(context()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn slides_a_tail_window_as_a_front_trim_plus_an_append() {
    let run = drive(limits(3, OutputRetain::Tail)).await;
    assert_eq!(
        run.step(print("line 1\nline 2\nline 3\n")).await,
        set("line 1\nline 2\nline 3\n")
    );
    assert_eq!(
        run.step(print("line 4\n")).await,
        window(Some(7), "line 4\n")
    );
    // The buffer keeps only the window, and later slides stay minimal and exact.
    assert_eq!(
        run.step(print("line 5\nline 6\n")).await,
        window(Some(14), "line 5\nline 6\n")
    );
    assert_eq!(
        run.published(),
        Some(SlotProgress {
            output: Some("line 4\nline 5\nline 6\n".to_owned()),
            dropped_bytes: Some(21),
            dropped_lines: Some(3),
            ..SlotProgress::default()
        })
    );
    run.finish().await;
    run.harness.close(context()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn sends_the_whole_window_when_the_overlap_search_cannot_find_the_shared_part() {
    // A retained window beyond the 64 KiB overlap scan.
    let wide = drive(Truncation::On(OutputLimits {
        max_bytes: 100 * 1024,
        max_lines: 1_000_000,
        retain: OutputRetain::Tail,
    }))
    .await;
    let line = |index: usize| format!("{index:010} {}\n", "x".repeat(989));
    let text: String = (0..100).map(line).collect();
    wide.step(print_owned(text)).await;
    let slid = wide.step(print_owned((100..104).map(line).collect())).await;
    assert!(
        matches!(slid.output, Some(ToolOutputUpdate::Set { .. })),
        "{slid:?}"
    );
    wide.finish().await;
    wide.harness.close(context()).await.unwrap();

    // Repetitive output still finds an overlap here; the bounded candidate search can give up on other inputs and
    // then sends one window.
    let repetitive = drive(limits(50, OutputRetain::Tail)).await;
    repetitive.step(print_owned("y\n".repeat(50))).await;
    assert_eq!(repetitive.step(print("z\n")).await, window(Some(2), "z\n"));
    repetitive.finish().await;
    repetitive.harness.close(context()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn publishes_details_and_diagnostics_and_settles_them_with_one_commit() {
    let run = drive(Truncation::default()).await;
    let details_change = |value: &str| ProgressChange {
        output: None,
        details: Some(JsonValue::parse(value).expect("valid JSON literal")),
        diagnostics: None,
    };
    assert_eq!(
        run.step(details(r#"{"step":1,"log":"a"}"#)).await,
        details_change(r#"{"step":1,"log":"a"}"#)
    );
    assert_eq!(
        run.step(details(r#"{"step":2}"#)).await,
        details_change(r#"{"step":2}"#)
    );
    let first = ToolDiagnostic {
        omitted: None,
        artifact: None,
        lines: None,
        severity: ToolDiagnosticSeverity::Info,
        code: None,
        message: "first".to_owned(),
    };
    let next = ToolDiagnostic {
        severity: ToolDiagnosticSeverity::Warn,
        message: "second".to_owned(),
        ..first.clone()
    };
    assert_eq!(
        run.step(diagnostic(first.clone())).await,
        ProgressChange {
            output: None,
            details: None,
            diagnostics: Some(vec![first.clone()]),
        }
    );
    assert_eq!(
        run.step(diagnostic(next.clone())).await,
        ProgressChange {
            output: None,
            details: None,
            diagnostics: Some(vec![first, next]),
        }
    );
    // The slot never held them, so the settle commit only marks it done.
    let settled = run.finish().await;
    assert_eq!(
        settled[0]
            .iter()
            .filter(|op| op[1][0] == "tools")
            .map(|op| (op[0].clone(), op[1].clone()))
            .collect::<Vec<_>>(),
        [
            (json(r#""s""#), json(r#"["tools",0,"status"]"#)),
            (json(r#""s""#), json(r#"["tools",0,"entry"]"#)),
        ]
    );
    run.harness.close(context()).await.unwrap();
}

/// The journal of a long streaming call: its start (the `running` slot,
/// before the steps) and its settle; none of its many publications
/// reaches storage (docs/runtime.md S2).
#[tokio::test(flavor = "multi_thread")]
async fn a_long_streaming_call_commits_nothing_between_its_start_and_its_settle() {
    let run = drive(Truncation::default()).await;
    for index in 0..40 {
        run.step(print_owned(format!("line {index}\n"))).await;
    }
    let settled = run.finish().await;
    // Ops inside the call's slot; the round's own cleanup replaces `tools` whole.
    let touches_slot = |ops: &Vec<serde_json::Value>| {
        ops.iter().any(|op| {
            op[1]
                .as_array()
                .is_some_and(|path| path.len() > 2 && path[..2] == [json(r#""tools""#), json("0")])
        })
    };
    assert_eq!(
        (
            lock(&run.changes).len(),
            settled.iter().filter(|ops| touches_slot(ops)).count()
        ),
        (40, 1)
    );
    run.harness.close(context()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn streams_partial_text_as_appends() {
    let setup = chat_setup(RegisterFauxProviderOptions {
        tokens_per_second: Some(400.0),
        token_size: Some(FauxTokenSize {
            min: Some(4),
            max: Some(4),
        }),
        ..RegisterFauxProviderOptions::default()
    });
    setup.faux.set_responses(vec![faux_assistant_message(
        vec![faux_text("word ".repeat(250))],
        FauxAssistantMessageOptions::default(),
    )
    .into()]);
    let OpenChat { harness, root } = open_chat(Arc::new(MemoryStorage::new()), &setup, None)
        .await
        .unwrap();
    let commits = record_commits(&harness);
    root.submit(input("go"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    let commits = lock(&commits).clone();
    let partials = &commits[2..commits.len() - 1];
    assert!(partials.len() > 2);
    assert_eq!(partials[0].len(), 1);
    assert_eq!(partials[0][0][0], "s");
    assert_eq!(partials[0][0][1], json(r#"["generation","message"]"#));
    assert!(partials[0][0][2].is_object());
    for ops in &partials[1..] {
        assert_eq!(ops.len(), 1, "{ops:?}");
        assert_eq!(ops[0][0], "a");
        assert_eq!(
            ops[0][1],
            json(r#"["generation","message","content",0,"text"]"#)
        );
        assert!(ops[0][2].is_string());
    }
    harness.close(context()).await.unwrap();
}

/// Memory storage that remembers whether each commit wrote `pi.live` as a base or a delta.
struct RecordingStorage {
    inner: MemoryStorage,
    live_id: Arc<Mutex<Option<DocumentId>>>,
    written: Arc<Mutex<Vec<(Seq, &'static str)>>>,
}

impl Storage for RecordingStorage {
    fn commit<'a>(
        &'a self,
        writes: &'a [StorageWrite],
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Seq, StorageError>> {
        async move {
            let live_id = *lock(&self.live_id);
            let mut kind = None;
            for write in writes {
                if let StorageWrite::DocumentChange { id, content } = write {
                    if Some(*id) == live_id {
                        kind = Some(match content {
                            DocumentContent::Base(_) => "base",
                            DocumentContent::Delta(_) => "delta",
                        });
                    }
                }
            }
            let seq = self.inner.commit(writes, cx).await?;
            if let Some(kind) = kind {
                lock(&self.written).push((seq, kind));
            }
            Ok(seq)
        }
        .boxed()
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

fn nothing_runs(value: &serde_json::Value) -> bool {
    value.get("generation").is_none()
        && !value
            .get("tools")
            .and_then(serde_json::Value::as_array)
            .is_some_and(|slots| slots.iter().any(|slot| slot["status"] == "running"))
}

#[tokio::test(flavor = "multi_thread")]
async fn stores_a_complete_base_exactly_in_the_commits_where_nothing_runs() {
    let live_id: Arc<Mutex<Option<DocumentId>>> = Arc::default();
    let written: Arc<Mutex<Vec<(Seq, &'static str)>>> = Arc::default();
    let storage = RecordingStorage {
        inner: MemoryStorage::new(),
        live_id: Arc::clone(&live_id),
        written: Arc::clone(&written),
    };
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    for name in ["first", "second"] {
        let tool = ToolRegistration::new(
            name,
            name,
            empty_object_schema(),
            move |_, api, _| async move {
                api.output(ToolOutputChunk::Text(&format!("{name} output\n")), None)?;
                tokio::time::sleep(Duration::from_millis(150)).await;
                api.output(ToolOutputChunk::Text(&format!("{name} more\n")), None)?;
                Ok(ToolExecutionResult::default())
            },
        );
        add_tool(&setup.registry, define_tool(tool), None).unwrap();
    }
    setup.faux.set_responses(vec![
        faux_assistant_message(vec![call("first", "a"), call("second", "b")], tool_use()).into(),
        done().into(),
    ]);
    setup
        .settings
        .update(|settings| settings.tool_execution = Some(ToolExecutionMode::Sequential));
    let OpenChat { harness, root } = open_chat(Arc::new(storage), &setup, None).await.unwrap();
    let values: Arc<Mutex<HashMap<Seq, serde_json::Value>>> = Arc::default();
    let sink = Arc::clone(&values);
    drop(
        harness
            .subscribe_commits(Arc::new(move |publication, _| {
                for change in document_changes(publication) {
                    if change.record.kind != "pi.live" {
                        continue;
                    }
                    *lock(&live_id) = Some(change.record.id);
                    if let Some(value) = change.value {
                        lock(&sink).insert(
                            publication.seq,
                            serde_json::Value::from(&JsonValue::Object(value)),
                        );
                    }
                }
            }))
            .unwrap(),
    );
    root.submit(input("go"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    // Publications follow their commits; wait until every recorded commit's value arrived.
    wait_for(
        || {
            let published = {
                let values = lock(&values);
                lock(&written)
                    .iter()
                    .all(|(seq, _)| values.contains_key(seq))
            };
            async move { published }
        },
        WAIT_MS,
    )
    .await;
    let values = lock(&values).clone();
    let kinds: Vec<&str> = lock(&written)
        .iter()
        .map(|(seq, kind)| {
            assert_eq!(
                *kind == "base",
                nothing_runs(&values[seq]),
                "commit {seq:?}"
            );
            *kind
        })
        .collect();
    // Bases at the handover, after each sequential tool, after the round, and when the run ends.
    assert!(
        kinds.iter().filter(|kind| **kind == "base").count() >= 5,
        "{kinds:?}"
    );
    assert!(kinds.contains(&"delta"));
    harness.close(context()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn starts_calls_the_request_did_not_offer_as_done_and_marks_a_faulted_tools_slot_done_without_an_entry(
) {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    // TS returns details holding a function, which is not strict JSON. Rust
    // `JsonValue` cannot hold one; usage beyond `Number.MAX_SAFE_INTEGER` is
    // the closest value whose result commit throws the same way.
    let bad = ToolRegistration::new("bad", "bad", empty_object_schema(), |_, _, _| async {
        Ok(ToolExecutionResult {
            output: Some(Vec::new()),
            usage: Some(Usage {
                input: u64::MAX,
                ..Usage::default()
            }),
            ..ToolExecutionResult::default()
        })
    });
    add_tool(&setup.registry, define_tool(bad), None).unwrap();
    setup.faux.set_responses(vec![
        faux_assistant_message(vec![call("ghost", "g"), call("bad", "b")], tool_use()).into(),
        done().into(),
    ]);
    let OpenChat { harness, root } = open_chat(Arc::new(MemoryStorage::new()), &setup, None)
        .await
        .unwrap();
    let commits = record_commits(&harness);
    root.submit(input("go"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    let entries = root
        .entries(ConversationEntryQuery::default(), 10, None, context())
        .await
        .unwrap();
    let ghost_result = entries
        .items
        .iter()
        .find(|entry| entry.kind == "pi.tool-result")
        .unwrap()
        .id
        .get();
    let commits = lock(&commits).clone();
    let handover = commits
        .iter()
        .find(|ops| ops.iter().any(|op| op[0] == "s" && op[1][0] == "tools"))
        .unwrap();
    let tools = handover
        .iter()
        .find(|op| op[0] == "s" && op[1] == json(r#"["tools"]"#))
        .expect("the handover sets the tool round");
    assert!(tools[2][1]["taskId"].is_u64());
    let bad_task = tools[2][1]["taskId"].clone();
    assert_eq!(
        *tools,
        serde_json::json!([
            "s",
            ["tools"],
            [
                { "callId": "g", "name": "ghost", "status": "done", "entry": ghost_result },
                { "callId": "b", "name": "bad", "taskId": bad_task, "status": "pending" },
            ],
        ])
    );
    // The fault cleanup writes only the status.
    assert!(
        commits.contains(&vec![json(r#"["s",["tools",1,"status"],"done"]"#)]),
        "{commits:?}"
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn commits_the_tool_calling_answer_its_tool_tasks_the_generations_wait_and_the_tool_round_in_one_commit(
) {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_tool(&setup.registry, noop("noop"), None).unwrap();
    setup.faux.set_responses(vec![
        faux_assistant_message(vec![call("noop", "a"), call("noop", "b")], tool_use()).into(),
        done().into(),
    ]);
    let OpenChat { harness, root } = open_chat(Arc::new(MemoryStorage::new()), &setup, None)
        .await
        .unwrap();
    let handover: Arc<Mutex<Option<Vec<CommitChange>>>> = Arc::default();
    let sink = Arc::clone(&handover);
    drop(
        harness
            .subscribe_commits(Arc::new(move |publication, _| {
                for change in document_changes(publication) {
                    let two = change.record.kind == "pi.live"
                        && change
                            .value
                            .as_ref()
                            .and_then(|value| value.get("tools"))
                            .and_then(JsonValue::as_array)
                            .is_some_and(|tools| tools.len() == 2);
                    if two {
                        lock(&sink).get_or_insert_with(|| publication.changes.clone());
                    }
                }
            }))
            .unwrap(),
    );
    root.submit(input("go"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    let changes = lock(&handover).clone().unwrap();
    let mut kinds: Vec<String> = changes
        .iter()
        .filter_map(|change| match change {
            CommitChange::Entry(entry) => Some(entry.kind.clone()),
            CommitChange::Task(task) => Some(task.kind.clone()),
            CommitChange::Conversation(_)
            | CommitChange::Submission(_)
            | CommitChange::Document(_) => None,
        })
        .collect();
    kinds.sort();
    assert_eq!(
        kinds,
        ["pi.assistant", "pi.generation", "pi.tool", "pi.tool"]
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn settles_an_aborted_tools_slot_with_its_status_and_entry_only() {
    let run = drive(Truncation::default()).await;
    run.step(print("partial\n")).await;
    run.step(details(r#"{"n":1}"#)).await;
    let task_id = live(&run.harness, run.conversation).await["tools"][0]["taskId"]
        .as_u64()
        .unwrap();
    let before = run.commits().len();
    run.harness
        .abort_task(TaskId::from_number(task_id), context())
        .await
        .unwrap();
    let status = json(r#"["tools",0,"status"]"#);
    let is_abort_commit =
        |ops: &Vec<serde_json::Value>| ops.iter().any(|op| op[0] == "s" && op[1] == status);
    wait_for(
        || {
            let found = run.commits()[before..].iter().any(is_abort_commit);
            async move { found }
        },
        WAIT_MS,
    )
    .await;
    let abort_commit = run.commits()[before..]
        .iter()
        .find(|ops| is_abort_commit(ops))
        .cloned()
        .unwrap();
    // The slot never held the progress: the abort marks it done and names
    // its entry, which carries the output and the details.
    assert_eq!(abort_commit.len(), 2, "{abort_commit:?}");
    assert_contains_all(
        &abort_commit,
        &[json(r#"["s",["tools",0,"status"],"done"]"#)],
    );
    assert!(abort_commit
        .iter()
        .any(|op| op[0] == "s" && op[1] == json(r#"["tools",0,"entry"]"#) && op[2].is_u64()));
    run.harness.close(context()).await.unwrap();
}

#[test]
fn keeps_a_complete_base_exactly_while_nothing_runs() {
    let base = |value: &str| {
        let value = JsonValue::parse(value).expect("valid JSON literal");
        let object: &JsonObject = value.as_object().expect("an object");
        let when = LIVE_DOC
            .definition()
            .checkpoint_when
            .expect("pi.live selects bases");
        when(
            object,
            &[],
            CheckpointInfo {
                deltas_since_base: 1000,
            },
        )
    };
    let run = r#""run":{"taskId":1,"inputs":[]}"#;
    let slot = |status: &str| format!(r#"{{"callId":"c","name":"n","status":"{status}"}}"#);
    assert!(base("{}"));
    assert!(!base(&format!(r#"{{{run},"generation":{{"attempt":1}}}}"#)));
    assert!(base(&format!(
        r#"{{{run},"tools":[{},{}]}}"#,
        slot("pending"),
        slot("done")
    )));
    assert!(!base(&format!(
        r#"{{{run},"tools":[{},{}]}}"#,
        slot("done"),
        slot("running")
    )));
    assert!(base(&format!("{{{run}}}")));
}
