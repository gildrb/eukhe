//! Port of `test/harness-inbox.test.ts`.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::delta::Op;
use eukhe_chord::json::{from_json, to_json, JsonValue};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_text, faux_tool_call, FauxAssistantMessageOptions,
    FauxResponseStep, FauxTokenSize, RegisterFauxProviderOptions,
};
use eukhe_types::pi_ai::{
    AssistantMessage, IndexMap, JsonObject as PiJsonObject, Message, StopReason, Usage, UsageCost,
};
use futures::FutureExt;

use super::chat_support::{
    all_entries, chat_setup, open_chat, text_of, wait_for, ChatSetup, OpenChat,
};
use super::support::{
    add_hooks, add_tool, context, empty_object_schema, generation_task, tool_task,
};
use super::task_support::{deferred, flush, Deferred};
use crate::documents::{DocDefinition, SessionDoc};
use crate::entries::RESET_ENTRY;
use crate::harness::define::define_tool;
use crate::harness::inbox::{InboxItem, InboxState, INBOX_DOC};
use crate::harness::live::{LiveState, ToolSlotStatus, LIVE_DOC};
use crate::harness::types::{
    ConversationCreateOptions, GenerationHooks, InputSubmissionDraft, PartialRetryPolicy,
    QueueMode, ToolControl, ToolExecutionResult, ToolHooks, ToolRegistration, WhenBusy,
    WriteSubmissionDraft, YieldContinuation,
};
use crate::harness::usage::{record_usage, UsageBucket, UsageState, USAGE_DOC};
use crate::harness::{Conversation, Harness, SubmissionHandle};
use crate::session::tests::support::{document_changes, ControlledStorage};
use crate::storage::sqlite::{open_native_sqlite_storage, NativeSqliteStorageOptions};
use crate::storage::MemoryStorage;
use crate::types::{
    CheckpointInfo, CommitChange, ConversationOwnership, DocumentContent, EntryDraft, EntryHead,
    EntryId, EntryRecord, InputSubmission, Storage, StorageWrite, SubmissionId, SubmissionRecord,
    SubmissionState, SubmissionStatus,
};

fn memory() -> Arc<dyn Storage> {
    Arc::new(MemoryStorage::new())
}

async fn sqlite(path: &std::path::Path) -> Arc<dyn Storage> {
    Arc::new(
        open_native_sqlite_storage(path, NativeSqliteStorageOptions::default())
            .await
            .unwrap(),
    )
}

fn json(text: &str) -> JsonValue {
    JsonValue::parse(text).expect("valid JSON literal")
}

fn ops_json(ops: &[Op]) -> JsonValue {
    ops.iter().map(Op::to_json).collect()
}

fn answer(text: &str) -> AssistantMessage {
    faux_assistant_message(
        vec![faux_text(text)],
        FauxAssistantMessageOptions::default(),
    )
}

fn failure(message: &str) -> AssistantMessage {
    faux_assistant_message(
        Vec::new(),
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::Error),
            error_message: Some(message.to_owned()),
            ..FauxAssistantMessageOptions::default()
        },
    )
}

/// A faux response held until `release` or cancellation; `reached` resolves when the request is sent.
struct Gated {
    step: FauxResponseStep,
    reached: Deferred,
    gate: Deferred,
}

impl Gated {
    fn release(&self) {
        self.gate.resolve(());
    }

    async fn reached(&self) {
        self.reached.wait().await;
    }
}

fn gated(message: AssistantMessage) -> Gated {
    let reached = deferred();
    let gate = deferred();
    let (reach, release) = (reached.clone(), gate.clone());
    let step = FauxResponseStep::Factory(Arc::new(move |_, options, _, _| {
        reach.resolve(());
        let signal = options.and_then(|options| options.stream.request.signal.clone());
        let (release, message) = (release.clone(), message.clone());
        async move {
            if let Some(signal) = signal {
                tokio::select! {
                    () = release.wait() => Ok(message),
                    reason = signal.cancelled() => Err(reason),
                }
            } else {
                release.wait().await;
                Ok(message)
            }
        }
        .boxed()
    }));
    Gated {
        step,
        reached,
        gate,
    }
}

fn gated_tool(
    name: &str,
    description: &str,
    gate: &Deferred,
    result: ToolExecutionResult,
) -> Arc<ToolRegistration> {
    let gate = gate.clone();
    define_tool(ToolRegistration::new(
        name,
        description,
        empty_object_schema(),
        move |_, _, _| {
            let (gate, result) = (gate.clone(), result.clone());
            async move {
                gate.wait().await;
                Ok(result)
            }
        },
    ))
}

fn empty_result() -> ToolExecutionResult {
    ToolExecutionResult {
        content: Some(Vec::new()),
        ..ToolExecutionResult::default()
    }
}

fn control_result(control: ToolControl) -> ToolExecutionResult {
    ToolExecutionResult {
        control: Some(control),
        ..empty_result()
    }
}

/// Register a `hold` tool whose calls wait for `gate` and then return `result`.
fn hold_tool(setup: &ChatSetup, gate: &Deferred, result: ToolExecutionResult) {
    add_tool(
        &setup.registry,
        gated_tool("hold", "Waits for the test", gate, result),
        None,
    )
    .unwrap();
}

/// TS `HOLD`: one call of the `hold` tool.
fn hold() -> AssistantMessage {
    faux_assistant_message(
        vec![faux_tool_call(
            "hold",
            PiJsonObject::new(),
            Some("c1".to_owned()),
        )],
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )
}

fn input(text: &str) -> InputSubmissionDraft {
    InputSubmissionDraft::new(text)
}

fn input_when(text: &str, when_busy: WhenBusy) -> InputSubmissionDraft {
    InputSubmissionDraft {
        when_busy: Some(when_busy),
        ..InputSubmissionDraft::new(text)
    }
}

fn write(entry: EntryDraft) -> WriteSubmissionDraft {
    WriteSubmissionDraft {
        request_id: None,
        entry,
    }
}

fn head(kind: &str, target: EntryId) -> EntryDraft {
    let mut draft = EntryDraft::new(kind);
    draft.head = Some(EntryHead::Entry(target));
    draft
}

async fn note(conversation: &Conversation) -> EntryRecord {
    let id = conversation.id();
    conversation
        .commit(
            move |tx| async move { tx.append_entry(id, EntryDraft::new("note")).await },
            context(),
        )
        .await
        .unwrap()
}

async fn submit(
    conversation: &Conversation,
    draft: impl Into<crate::harness::types::SubmissionDraft>,
) -> SubmissionHandle {
    conversation.submit(draft, context()).await.unwrap()
}

async fn status(submission: &SubmissionHandle) -> SubmissionRecord {
    submission.status(context()).await.unwrap()
}

async fn settle(submission: &SubmissionHandle) -> SubmissionRecord {
    submission.wait(context()).await.unwrap().into_record()
}

/// `toMatchObject({ status, answer? })`.
fn assert_done(record: &SubmissionRecord, answer: Option<EntryId>) {
    assert_eq!(record.state.status(), SubmissionStatus::Done, "{record:?}");
    if answer.is_some() {
        assert_eq!(record.state.answer(), answer, "{record:?}");
    }
}

/// `toMatchObject({ status: "unanswered", reason })`.
fn assert_unanswered(record: &SubmissionRecord, reason: &str) {
    assert_eq!(
        record.state.status(),
        SubmissionStatus::Unanswered,
        "{record:?}"
    );
    assert_eq!(record.state.reason(), Some(reason), "{record:?}");
}

/// `{ ...settled, id: actual.id, entry: expect.any(Number) }`.
fn like_settled(settled: &SubmissionRecord, actual: &SubmissionRecord) -> SubmissionRecord {
    let mut expected = settled.clone();
    expected.id = actual.id;
    if let (SubmissionState::Input(InputSubmission::Done { entry, .. }), Some(actual_entry)) =
        (&mut expected.state, actual.state.entry())
    {
        *entry = actual_entry;
    }
    expected
}

/// Kind and text of each entry, skipping system entries.
fn transcript(entries: &[EntryRecord]) -> Vec<String> {
    entries
        .iter()
        .filter(|entry| entry.kind != "pi.system")
        .map(|entry| {
            let message = entry.model.as_ref().and_then(|model| model.first());
            let text = match message {
                Some(Message::ToolResult(_)) => None,
                other => text_of(other),
            };
            match text {
                None => entry.kind.clone(),
                Some(text) => format!("{}:{text}", entry.kind),
            }
        })
        .collect()
}

fn last(entries: &[String], count: usize) -> Vec<String> {
    entries[entries.len() - count..].to_vec()
}

fn assistant_entries(entries: &[EntryRecord]) -> Vec<&EntryRecord> {
    entries
        .iter()
        .filter(|entry| entry.kind == "pi.assistant")
        .collect()
}

fn assistant_messages(entries: &[EntryRecord]) -> Vec<AssistantMessage> {
    entries
        .iter()
        .filter(|entry| entry.kind == "pi.assistant")
        .map(|entry| match &entry.model.as_ref().unwrap()[0] {
            Message::Assistant(message) => message.clone(),
            other => panic!("not an assistant message: {other:?}"),
        })
        .collect()
}

async fn inbox(harness: &Harness, root: &Conversation) -> Vec<(SubmissionId, &'static str)> {
    let value = harness
        .snapshot(&INBOX_DOC, root.id(), context())
        .await
        .unwrap()
        .unwrap();
    let state: InboxState = from_json(&JsonValue::Object(value)).unwrap();
    state
        .items
        .iter()
        .map(|item| {
            let mode = match item {
                InboxItem::Steer { .. } => "steer",
                InboxItem::FollowUp { .. } => "followUp",
                InboxItem::Write { .. } => "write",
            };
            (item.id(), mode)
        })
        .collect()
}

async fn live(harness: &Harness, root: &Conversation) -> Option<LiveState> {
    harness
        .snapshot(&LIVE_DOC, root.id(), context())
        .await
        .unwrap()
        .map(|value| from_json(&JsonValue::Object(value)).unwrap())
}

async fn usage_of(harness: &Harness, conversation: &Conversation) -> Option<UsageState> {
    harness
        .snapshot(&USAGE_DOC, conversation.id(), context())
        .await
        .unwrap()
        .map(|value| from_json(&JsonValue::Object(value)).unwrap())
}

async fn tool_status(
    harness: &Harness,
    root: &Conversation,
    index: usize,
) -> Option<ToolSlotStatus> {
    live(harness, root)
        .await
        .and_then(|live| live.tools)
        .and_then(|tools| tools.get(index).map(|slot| slot.status))
}

async fn tool_running(harness: &Harness, root: &Conversation) {
    wait_for(
        || async { tool_status(harness, root, 0).await == Some(ToolSlotStatus::Running) },
        5000,
    )
    .await;
}

async fn generation_streaming(harness: &Harness, root: &Conversation) {
    wait_for(
        || async {
            live(harness, root)
                .await
                .and_then(|live| live.generation)
                .is_some_and(|generation| generation.message.is_some())
        },
        5000,
    )
    .await;
}

fn yield_hooks(continue_first: bool, always: bool) -> GenerationHooks {
    let yields = Arc::new(AtomicUsize::new(0));
    GenerationHooks {
        on_yield: Some(Arc::new(move |_, _, _| {
            let first = yields.fetch_add(1, Ordering::SeqCst) == 0;
            let decision = (always || (continue_first && first)).then(|| YieldContinuation {
                r#continue: "more".into(),
            });
            futures::future::ready(Ok(decision)).boxed()
        })),
        ..GenerationHooks::default()
    }
}

/// Collects the non-empty `pi.inbox` operations of every commit.
fn inbox_ops(harness: &Harness) -> Arc<Mutex<Vec<JsonValue>>> {
    let ops: Arc<Mutex<Vec<JsonValue>>> = Arc::default();
    let sink = Arc::clone(&ops);
    let subscription = harness
        .subscribe_commits(Arc::new(move |publication, _| {
            for change in document_changes(publication) {
                if change.record.kind == "pi.inbox" && !change.ops.is_empty() {
                    sink.lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .push(ops_json(&change.ops));
                }
            }
        }))
        .unwrap();
    drop(subscription);
    ops
}

fn taken(ops: &Arc<Mutex<Vec<JsonValue>>>) -> Vec<JsonValue> {
    ops.lock().unwrap_or_else(PoisonError::into_inner).clone()
}

fn spent_usage(
    input: u64,
    output: u64,
    cache_read: u64,
    cache_write: u64,
    total_tokens: u64,
    cost: UsageCost,
) -> Usage {
    Usage {
        input,
        output,
        cache_read,
        cache_write,
        cache_write_1h: None,
        reasoning: None,
        total_tokens,
        cost,
    }
}

/// TS `describe("inbox")`.
mod queue {
    use super::*;

    #[tokio::test]
    async fn queues_busy_submissions_and_places_writes_before_user_items_at_the_final_boundary_one_follow_up_per_run(
    ) {
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let first = gated(answer("first"));
        setup.faux.set_responses(vec![
            first.step.clone(),
            answer("second").into(),
            answer("third").into(),
        ]);
        let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
        let input_submission = submit(&root, input("a")).await;
        first.reached().await;
        let f1 = submit(&root, input("f1")).await;
        let mut note_w = EntryDraft::new("note");
        note_w.data = Some(json(r#""w""#));
        let write_submission = submit(&root, write(note_w)).await;
        let f2 = submit(&root, input_when("f2", WhenBusy::FollowUp)).await;
        for submission in [&f1, &write_submission, &f2] {
            assert_eq!(
                status(submission).await.state.status(),
                SubmissionStatus::Queued
            );
        }
        assert_eq!(
            inbox(&harness, &root).await,
            vec![
                (f1.id(), "followUp"),
                (write_submission.id(), "write"),
                (f2.id(), "followUp")
            ]
        );
        assert_eq!(
            transcript(&all_entries(&root, context()).await.unwrap()),
            ["pi.user:a"]
        );

        first.release();
        settle(&f2).await;
        assert_eq!(
            transcript(&all_entries(&root, context()).await.unwrap()),
            [
                "pi.user:a",
                "pi.assistant:first",
                "note",
                "pi.user:f1",
                "pi.assistant:second",
                "pi.user:f2",
                "pi.assistant:third",
            ]
        );
        let entries = all_entries(&root, context()).await.unwrap();
        let answers = assistant_entries(&entries);
        assert_done(&status(&input_submission).await, Some(answers[0].id));
        assert_done(&status(&write_submission).await, None);
        assert_done(&status(&f1).await, Some(answers[1].id));
        assert_done(&status(&f2).await, Some(answers[2].id));
        assert_eq!(inbox(&harness, &root).await, vec![]);
        assert_eq!(live(&harness, &root).await, Some(LiveState::default()));
        harness.close(context()).await.unwrap();
    }

    #[tokio::test]
    async fn places_every_follow_up_in_one_successor_run_with_follow_up_mode_all() {
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let first = gated(answer("first"));
        setup
            .faux
            .set_responses(vec![first.step.clone(), answer("both").into()]);
        let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
        setup
            .settings
            .update(|settings| settings.follow_up_mode = Some(QueueMode::All));
        submit(&root, input("a")).await;
        first.reached().await;
        let f1 = submit(&root, input("f1")).await;
        let f2 = submit(&root, input("f2")).await;
        first.release();
        let settled = settle(&f2).await;
        let actual = status(&f1).await;
        assert_eq!(actual, like_settled(&settled, &actual));
        assert_eq!(
            transcript(&all_entries(&root, context()).await.unwrap()),
            [
                "pi.user:a",
                "pi.assistant:first",
                "pi.user:f1",
                "pi.user:f2",
                "pi.assistant:both"
            ]
        );
        assert_eq!(setup.faux.state().call_count, 2);
        harness.close(context()).await.unwrap();
    }

    #[derive(Default, serde::Serialize, serde::Deserialize)]
    struct Marker {
        n: u64,
    }

    static MARKER: SessionDoc<Marker> = match SessionDoc::define(DocDefinition {
        kind: "test.marker",
        version: 1,
        initial: Marker::default,
        migrate: None,
        checkpoint_when: None,
    }) {
        Ok(token) => token,
        Err(_) => panic!("invalid test.marker definition"),
    };

    #[tokio::test]
    async fn reads_queue_modes_when_the_final_boundary_s_commit_runs_on_the_session_line() {
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let first = gated(answer("first"));
        setup
            .faux
            .set_responses(vec![first.step.clone(), answer("both").into()]);
        let yielded = deferred();
        let signal = yielded.clone();
        add_hooks(
            &setup.registry,
            generation_task(),
            GenerationHooks {
                on_yield: Some(Arc::new(move |_, _, _| {
                    signal.resolve(());
                    futures::future::ready(Ok(None)).boxed()
                })),
                ..GenerationHooks::default()
            },
            None,
        )
        .unwrap();
        let storage = ControlledStorage::new();
        let OpenChat { harness, root } =
            open_chat(Arc::clone(&storage) as Arc<dyn Storage>, &setup, None)
                .await
                .unwrap();
        submit(&root, input("a")).await;
        first.reached().await;
        let f1 = submit(&root, input("f1")).await;
        let f2 = submit(&root, input("f2")).await;
        // Occupy the line, let the answer queue its boundary commit behind it, then change the mode.
        let held = storage.hold_commits();
        let occupying = tokio::spawn(root.commit(
            |tx| async move {
                let marker = tx.doc(&MARKER, ()).await?;
                // `n` starts at 0; `n++` makes it 1.
                marker.set("n", 1)?;
                Ok(())
            },
            context(),
        ));
        held.entered().await;
        first.release();
        yielded.wait().await;
        flush().await;
        setup
            .settings
            .update(|settings| settings.follow_up_mode = Some(QueueMode::All));
        held.release();
        occupying.await.unwrap().unwrap();
        let settled = settle(&f2).await;
        let actual = status(&f1).await;
        assert_eq!(actual, like_settled(&settled, &actual));
        assert_eq!(setup.faux.state().call_count, 2);
        harness.close(context()).await.unwrap();
    }

    #[tokio::test]
    async fn adds_steers_to_the_run_at_the_post_tools_boundary_and_holds_follow_ups_for_the_final_boundary(
    ) {
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let gate = deferred();
        hold_tool(&setup, &gate, empty_result());
        setup.faux.set_responses(vec![
            hold().into(),
            answer("after tools").into(),
            answer("follow-up").into(),
        ]);
        let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
        let input_submission = submit(&root, input("a")).await;
        tool_running(&harness, &root).await;
        let steer = submit(&root, input_when("s", WhenBusy::Steer)).await;
        let follow_up = submit(&root, input("f")).await;
        gate.resolve(());
        settle(&follow_up).await;
        assert_eq!(
            transcript(&all_entries(&root, context()).await.unwrap()),
            [
                "pi.user:a",
                "pi.assistant",
                "pi.tool-result",
                "pi.user:s",
                "pi.assistant:after tools",
                "pi.user:f",
                "pi.assistant:follow-up",
            ]
        );
        let entries = all_entries(&root, context()).await.unwrap();
        let answers = assistant_entries(&entries);
        assert_done(&status(&input_submission).await, Some(answers[1].id));
        assert_done(&status(&steer).await, Some(answers[1].id));
        assert_done(&status(&follow_up).await, Some(answers[2].id));
        harness.close(context()).await.unwrap();
    }

    #[tokio::test]
    async fn ends_the_run_at_a_queued_reset_after_tools_and_runs_earlier_follow_ups_in_the_new_context(
    ) {
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let gate = deferred();
        hold_tool(&setup, &gate, empty_result());
        let requests: Arc<Mutex<Vec<Vec<String>>>> = Arc::default();
        let sink = Arc::clone(&requests);
        let record = FauxResponseStep::factory(move |request, _, _, _| {
            sink.lock().unwrap_or_else(PoisonError::into_inner).push(
                request
                    .messages()
                    .iter()
                    .map(|message| {
                        format!(
                            "{}:{}",
                            message.role(),
                            text_of(Some(message)).unwrap_or_default()
                        )
                    })
                    .collect(),
            );
            Ok(answer("fresh"))
        });
        setup.faux.set_responses(vec![hold().into(), record]);
        let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
        let input_submission = submit(&root, input("a")).await;
        tool_running(&harness, &root).await;
        let follow_up = submit(&root, input("f")).await;
        root.reset(None, context()).await.unwrap();
        gate.resolve(());
        settle(&follow_up).await;
        assert_unanswered(&status(&input_submission).await, "reset");
        let entries = all_entries(&root, context()).await.unwrap();
        assert_eq!(
            transcript(&entries),
            [
                "pi.user:a",
                "pi.assistant",
                "pi.tool-result",
                "pi.reset",
                "pi.user:f",
                "pi.assistant:fresh"
            ]
        );
        let reset = entries
            .iter()
            .find(|entry| RESET_ENTRY.is(Some(entry)))
            .unwrap();
        assert_eq!(reset.head, Some(reset.id));
        // The follow-up's request starts at the reset: the follow-up, then the complete system baseline after the cut.
        assert_eq!(
            *requests.lock().unwrap_or_else(PoisonError::into_inner),
            vec![vec!["user:f".to_owned(), "system:".to_owned()]]
        );
        assert_eq!(setup.faux.state().call_count, 2);
        harness.close(context()).await.unwrap();
    }

    #[tokio::test]
    async fn places_a_queued_reset_after_the_answer_at_the_final_boundary() {
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let first = gated(answer("first"));
        setup.faux.set_responses(vec![first.step.clone()]);
        let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
        let input_submission = submit(&root, input("a")).await;
        first.reached().await;
        root.reset(Some("handoff".to_owned()), context())
            .await
            .unwrap();
        first.release();
        settle(&input_submission).await;
        harness.wait_for_idle(context()).await.unwrap();
        assert_done(&status(&input_submission).await, None);
        assert_eq!(
            transcript(&all_entries(&root, context()).await.unwrap()),
            ["pi.user:a", "pi.assistant:first", "pi.reset:handoff"]
        );
        let messages = to_json(&root.context(context()).await.unwrap().messages).unwrap();
        let timestamp = &messages[0]["timestamp"];
        assert!(matches!(timestamp, JsonValue::Number(_)), "{messages}");
        assert_eq!(
            messages,
            json(&format!(
                r#"[{{"role":"user","content":"handoff","timestamp":{timestamp}}}]"#
            ))
        );
        harness.close(context()).await.unwrap();
    }

    #[tokio::test]
    async fn resets_an_idle_conversation_at_once_with_or_without_handoff_text() {
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        setup.set_now(|| 7.0);
        let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
        note(&root).await;
        root.reset(None, context()).await.unwrap();
        let view = root.context(context()).await.unwrap();
        assert_eq!(
            view.head.as_ref().map(|head| head.kind.as_str()),
            Some("pi.reset")
        );
        assert_eq!(view.head.as_ref().and_then(|head| head.model.clone()), None);
        assert_eq!(view.messages, vec![]);
        root.reset(Some("carry on".to_owned()), context())
            .await
            .unwrap();
        let view = root.context(context()).await.unwrap();
        let reset = view.head.as_ref().unwrap();
        assert_eq!(reset.head, Some(reset.id));
        assert_eq!(
            to_json(&view.messages).unwrap(),
            json(r#"[{"role":"user","content":"carry on","timestamp":7}]"#)
        );
        harness.close(context()).await.unwrap();
    }

    #[tokio::test]
    async fn makes_a_queued_head_write_stale_when_it_targets_an_entry_before_the_active_range() {
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let first = gated(answer("first"));
        setup
            .faux
            .set_responses(vec![first.step.clone(), answer("second").into()]);
        let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
        let old = note(&root).await;
        root.reset(None, context()).await.unwrap();
        let reset = root.context(context()).await.unwrap().head.unwrap();
        let input_submission = submit(&root, input("a")).await;
        first.reached().await;
        let stale = submit(&root, write(head("summary", old.id))).await;
        let fresh = submit(&root, write(head("summary", reset.id))).await;
        first.release();
        settle(&input_submission).await;
        assert_unanswered(&status(&stale).await, "stale");
        assert_done(&status(&fresh).await, None);
        assert_eq!(inbox(&harness, &root).await, vec![]);

        // The fresh summary's marker starts the range at the reset: a target inside the range is not stale, even when
        // it is older than the marker itself. A reset placed earlier in the same boundary makes it stale.
        let inside = all_entries(&root, context())
            .await
            .unwrap()
            .into_iter()
            .find(|entry| entry.kind == "pi.user")
            .unwrap();
        let second = submit(&root, input("b")).await;
        let kept = submit(&root, write(head("summary", inside.id))).await;
        settle(&second).await;
        assert_done(&status(&kept).await, None);
        harness.close(context()).await.unwrap();
    }

    #[tokio::test]
    async fn makes_a_head_write_stale_behind_a_reset_placed_earlier_in_the_same_boundary() {
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let first = gated(answer("first"));
        setup.faux.set_responses(vec![first.step.clone()]);
        let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
        let input_submission = submit(&root, input("a")).await;
        first.reached().await;
        let target = all_entries(&root, context()).await.unwrap().remove(0);
        root.reset(None, context()).await.unwrap();
        let summary = submit(&root, write(head("summary", target.id))).await;
        first.release();
        settle(&input_submission).await;
        assert_unanswered(&status(&summary).await, "stale");
        harness.close(context()).await.unwrap();
    }

    #[tokio::test]
    async fn ends_the_run_with_a_pi_reset_entry_when_a_tool_requests_a_handoff() {
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let gate = deferred();
        gate.resolve(());
        hold_tool(
            &setup,
            &gate,
            control_result(ToolControl {
                handoff: Some("continue here".to_owned()),
                ..ToolControl::default()
            }),
        );
        setup.faux.set_responses(vec![hold().into()]);
        let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
        let settled = settle(&submit(&root, input("a")).await).await;
        let entries = all_entries(&root, context()).await.unwrap();
        let calling = entries
            .iter()
            .find(|entry| entry.kind == "pi.assistant")
            .unwrap();
        assert_done(&settled, Some(calling.id));
        assert_eq!(
            transcript(&entries),
            [
                "pi.user:a",
                "pi.assistant",
                "pi.tool-result",
                "pi.reset:continue here"
            ]
        );
        let tail = entries.last().unwrap();
        assert_eq!(tail.head, Some(tail.id));
        assert_eq!(setup.faux.state().call_count, 1);
        assert_eq!(live(&harness, &root).await, Some(LiveState::default()));
        harness.close(context()).await.unwrap();
    }

    #[tokio::test]
    async fn drops_an_on_yield_continuation_when_the_final_boundary_selects_a_follow_up() {
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let first = gated(answer("first"));
        setup
            .faux
            .set_responses(vec![first.step.clone(), answer("second").into()]);
        add_hooks(
            &setup.registry,
            generation_task(),
            yield_hooks(true, false),
            None,
        )
        .unwrap();
        let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
        let input_submission = submit(&root, input("a")).await;
        first.reached().await;
        let follow_up = submit(&root, input("f")).await;
        first.release();
        settle(&follow_up).await;
        assert_done(&status(&input_submission).await, None);
        assert_eq!(
            transcript(&all_entries(&root, context()).await.unwrap()),
            [
                "pi.user:a",
                "pi.assistant:first",
                "pi.user:f",
                "pi.assistant:second"
            ]
        );
        harness.close(context()).await.unwrap();
    }

    #[tokio::test]
    async fn withdraws_a_queued_submission_and_removes_its_item() {
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let first = gated(answer("first"));
        setup.faux.set_responses(vec![first.step.clone()]);
        let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
        let input_submission = submit(&root, input("a")).await;
        first.reached().await;
        let kept = submit(&root, write(EntryDraft::new("note"))).await;
        let withdrawn = submit(&root, input("f")).await;
        assert_eq!(
            withdrawn.abort(context()).await.unwrap().as_str(),
            "aborted"
        );
        assert_unanswered(&settle(&withdrawn).await, "aborted");
        assert_eq!(inbox(&harness, &root).await, vec![(kept.id(), "write")]);
        first.release();
        settle(&input_submission).await;
        assert_done(&status(&kept).await, None);
        assert_eq!(setup.faux.state().call_count, 1);
        harness.close(context()).await.unwrap();
    }

    #[tokio::test]
    async fn leaves_queued_items_after_a_failed_run_until_the_next_submission_places_them_in_order()
    {
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let failing = gated(failure("invalid request"));
        setup.faux.set_responses(vec![
            failing.step.clone(),
            answer("for f").into(),
            answer("for g").into(),
        ]);
        let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
        let input_submission = submit(&root, input("a")).await;
        failing.reached().await;
        let f = submit(&root, input("f")).await;
        failing.release();
        assert_unanswered(&settle(&input_submission).await, "model_error");
        harness.wait_for_idle(context()).await.unwrap();
        assert_eq!(status(&f).await.state.status(), SubmissionStatus::Queued);
        assert_eq!(inbox(&harness, &root).await, vec![(f.id(), "followUp")]);

        // Idle with a queued item: the new input queues behind it, and a final boundary places the older one first.
        let g = submit(&root, input_when("g", WhenBusy::Reject)).await;
        settle(&g).await;
        assert_done(&status(&f).await, None);
        assert_eq!(
            last(
                &transcript(&all_entries(&root, context()).await.unwrap()),
                4
            ),
            [
                "pi.user:f",
                "pi.assistant:for f",
                "pi.user:g",
                "pi.assistant:for g"
            ]
        );
        harness.close(context()).await.unwrap();
    }

    #[tokio::test]
    async fn keeps_queued_submissions_across_reopen_and_settles_them_afterwards() {
        let directory = tempfile::Builder::new()
            .prefix("pi-durable-inbox-")
            .tempdir()
            .unwrap();
        let path = directory.path().join("session.sqlite");
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let first = gated(answer("first"));
        setup.faux.set_responses(vec![
            first.step.clone(),
            answer("first again").into(),
            answer("f").into(),
        ]);
        let opened = open_chat(sqlite(&path).await, &setup, None).await.unwrap();
        submit(&opened.root, input("a")).await;
        first.reached().await;
        let f = submit(&opened.root, input("f")).await.id();
        opened.harness.close(context()).await.unwrap();

        let opened = open_chat(sqlite(&path).await, &setup, None).await.unwrap();
        let settled = opened
            .harness
            .submission(f, context())
            .await
            .unwrap()
            .unwrap()
            .wait(context())
            .await
            .unwrap();
        assert_done(&settled, None);
        assert_eq!(
            last(
                &transcript(&all_entries(&opened.root, context()).await.unwrap()),
                2
            ),
            ["pi.user:f", "pi.assistant:f"]
        );
        opened.harness.close(context()).await.unwrap();
    }

    #[tokio::test]
    async fn commits_inbox_changes_as_positional_chord_operations_and_a_base_when_empty() {
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let first = gated(answer("first"));
        setup
            .faux
            .set_responses(vec![first.step.clone(), answer("second").into()]);
        let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
        let ops = inbox_ops(&harness);
        let input_submission = submit(&root, input("a")).await;
        first.reached().await;
        let w1 = submit(&root, write(EntryDraft::new("note"))).await;
        let f1 = submit(&root, input("f1")).await;
        let w2 = submit(&root, write(EntryDraft::new("note"))).await;
        let f2 = submit(&root, input("f2")).await;
        let w3 = submit(&root, write(EntryDraft::new("note"))).await;
        let write_item = |index: usize, id: SubmissionId| {
            json(&format!(
                r#"[["p",["items"],{index},0,[{{"id":{id},"mode":"write","entry":{{"kind":"note"}}}}]]]"#
            ))
        };
        let follow_up_item = |index: usize, id: SubmissionId, content: &str| {
            json(&format!(
                r#"[["p",["items"],{index},0,[{{"id":{id},"mode":"followUp","content":"{content}"}}]]]"#
            ))
        };
        assert_eq!(
            taken(&ops),
            vec![
                write_item(0, w1.id()),
                follow_up_item(1, f1.id(), "f1"),
                write_item(2, w2.id()),
                follow_up_item(3, f2.id(), "f2"),
                write_item(4, w3.id()),
            ]
        );
        first.release();
        settle(&input_submission).await;
        // Every write and the first follow-up leave; only f2 at index 3 remains. No retained value is carried.
        let sixth = taken(&ops)[5].clone();
        let sixth_ops = sixth.as_array().unwrap();
        assert!(
            sixth_ops.iter().all(|op| op[0] == json(r#""p""#)
                && op[4].as_array().is_some_and(<[JsonValue]>::is_empty)),
            "{sixth}"
        );
        assert!(
            sixth_ops.contains(&json(r#"["p",["items"],4,1,[]]"#)),
            "{sixth}"
        );
        assert!(!sixth.to_string().contains("f2"), "{sixth}");
        settle(&f2).await;
        harness.close(context()).await.unwrap();
    }

    #[tokio::test]
    async fn settles_a_stale_write_at_once_while_idle_and_a_queued_one_behind_waiting_items() {
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let failing = gated(failure("invalid request"));
        setup
            .faux
            .set_responses(vec![failing.step.clone(), answer("for f").into()]);
        let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
        let old = note(&root).await;
        root.reset(None, context()).await.unwrap();
        let before = all_entries(&root, context()).await.unwrap().len();
        let idle = submit(&root, write(head("summary", old.id))).await;
        assert_unanswered(&settle(&idle).await, "stale");
        assert_eq!(all_entries(&root, context()).await.unwrap().len(), before);

        // After a failed run, a follow-up waits; a stale write queues behind it and the boundary rejects it.
        let input_submission = submit(&root, input("a")).await;
        failing.reached().await;
        let f = submit(&root, input("f")).await;
        failing.release();
        settle(&input_submission).await;
        harness.wait_for_idle(context()).await.unwrap();
        let queued = submit(&root, write(head("summary", old.id))).await;
        assert_unanswered(&settle(&queued).await, "stale");
        assert_done(&settle(&f).await, None);
        harness.close(context()).await.unwrap();
    }

    #[tokio::test]
    async fn keeps_an_on_yield_continuation_across_a_queued_plain_write_with_the_run_s_original_input(
    ) {
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let first = gated(answer("first"));
        setup
            .faux
            .set_responses(vec![first.step.clone(), answer("second").into()]);
        add_hooks(
            &setup.registry,
            generation_task(),
            yield_hooks(true, false),
            None,
        )
        .unwrap();
        let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
        let input_submission = submit(&root, input("a")).await;
        first.reached().await;
        let write_submission = submit(&root, write(EntryDraft::new("note"))).await;
        first.release();
        settle(&input_submission).await;
        let entries = all_entries(&root, context()).await.unwrap();
        assert_eq!(
            transcript(&entries),
            [
                "pi.user:a",
                "pi.assistant:first",
                "note",
                "pi.user:more",
                "pi.assistant:second"
            ]
        );
        assert_done(
            &status(&input_submission).await,
            Some(entries.last().unwrap().id),
        );
        assert_done(&status(&write_submission).await, None);
        harness.close(context()).await.unwrap();
    }

    #[tokio::test]
    async fn drops_an_on_yield_continuation_for_a_queued_reset() {
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let first = gated(answer("first"));
        setup.faux.set_responses(vec![first.step.clone()]);
        add_hooks(
            &setup.registry,
            generation_task(),
            yield_hooks(false, true),
            None,
        )
        .unwrap();
        let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
        let input_submission = submit(&root, input("a")).await;
        first.reached().await;
        root.reset(None, context()).await.unwrap();
        first.release();
        settle(&input_submission).await;
        harness.wait_for_idle(context()).await.unwrap();
        assert_done(&status(&input_submission).await, None);
        assert_eq!(
            transcript(&all_entries(&root, context()).await.unwrap()),
            ["pi.user:a", "pi.assistant:first", "pi.reset"]
        );
        assert_eq!(setup.faux.state().call_count, 1);
        harness.close(context()).await.unwrap();
    }

    #[tokio::test]
    async fn adds_every_steer_to_the_run_at_the_post_tools_boundary_with_steering_mode_all() {
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let gate = deferred();
        hold_tool(&setup, &gate, empty_result());
        setup.faux.set_responses(vec![
            hold().into(),
            answer("after tools").into(),
            answer("follow-up").into(),
        ]);
        let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
        setup
            .settings
            .update(|settings| settings.steering_mode = Some(QueueMode::All));
        let input_submission = submit(&root, input("a")).await;
        tool_running(&harness, &root).await;
        let s1 = submit(&root, input_when("s1", WhenBusy::Steer)).await;
        let f = submit(&root, input("f")).await;
        let s2 = submit(&root, input_when("s2", WhenBusy::Steer)).await;
        gate.resolve(());
        settle(&f).await;
        let entries = all_entries(&root, context()).await.unwrap();
        assert_eq!(
            transcript(&entries),
            [
                "pi.user:a",
                "pi.assistant",
                "pi.tool-result",
                "pi.user:s1",
                "pi.user:s2",
                "pi.assistant:after tools",
                "pi.user:f",
                "pi.assistant:follow-up",
            ]
        );
        let answers = assistant_entries(&entries);
        for submission in [&input_submission, &s1, &s2] {
            assert_done(&status(submission).await, Some(answers[1].id));
        }
        harness.close(context()).await.unwrap();
    }

    #[tokio::test]
    async fn queues_an_idle_steer_behind_waiting_items_and_places_it_with_the_first_follow_up_in_id_order(
    ) {
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let failing = gated(failure("invalid request"));
        setup
            .faux
            .set_responses(vec![failing.step.clone(), answer("both").into()]);
        let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
        let input_submission = submit(&root, input("a")).await;
        failing.reached().await;
        let f = submit(&root, input("f")).await;
        failing.release();
        settle(&input_submission).await;
        harness.wait_for_idle(context()).await.unwrap();
        let steer = submit(&root, input_when("s", WhenBusy::Steer)).await;
        let settled = settle(&steer).await;
        assert_eq!(settled.state.status(), SubmissionStatus::Done);
        let f_record = status(&f).await;
        assert_eq!(f_record.state.status(), SubmissionStatus::Done);
        assert_eq!(f_record.state.answer(), settled.state.answer());
        assert_eq!(
            last(
                &transcript(&all_entries(&root, context()).await.unwrap()),
                3
            ),
            ["pi.user:f", "pi.user:s", "pi.assistant:both"]
        );
        harness.close(context()).await.unwrap();
    }

    #[tokio::test]
    async fn starts_a_queued_follow_up_after_a_terminating_round() {
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let gate = deferred();
        hold_tool(
            &setup,
            &gate,
            control_result(ToolControl {
                terminate: true,
                ..ToolControl::default()
            }),
        );
        setup
            .faux
            .set_responses(vec![hold().into(), answer("follow-up").into()]);
        let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
        let input_submission = submit(&root, input("a")).await;
        tool_running(&harness, &root).await;
        let f = submit(&root, input("f")).await;
        gate.resolve(());
        settle(&f).await;
        let entries = all_entries(&root, context()).await.unwrap();
        let calling = entries
            .iter()
            .find(|entry| entry.kind == "pi.assistant")
            .unwrap();
        assert_done(&status(&input_submission).await, Some(calling.id));
        assert_eq!(
            transcript(&entries),
            [
                "pi.user:a",
                "pi.assistant",
                "pi.tool-result",
                "pi.user:f",
                "pi.assistant:follow-up"
            ]
        );
        harness.close(context()).await.unwrap();
    }

    #[tokio::test]
    async fn writes_the_last_handoff_in_call_order_and_then_runs_queued_follow_ups_in_the_new_context(
    ) {
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let first_gate = deferred();
        let second_gate = deferred();
        hold_tool(
            &setup,
            &first_gate,
            control_result(ToolControl {
                handoff: Some("one".to_owned()),
                ..ToolControl::default()
            }),
        );
        add_tool(
            &setup.registry,
            gated_tool(
                "later",
                "Finishes first",
                &second_gate,
                control_result(ToolControl {
                    handoff: Some("two".to_owned()),
                    ..ToolControl::default()
                }),
            ),
            None,
        )
        .unwrap();
        let round = faux_assistant_message(
            vec![
                faux_tool_call("hold", PiJsonObject::new(), Some("c1".to_owned())),
                faux_tool_call("later", PiJsonObject::new(), Some("c2".to_owned())),
            ],
            FauxAssistantMessageOptions {
                stop_reason: Some(StopReason::ToolUse),
                ..FauxAssistantMessageOptions::default()
            },
        );
        setup
            .faux
            .set_responses(vec![round.into(), answer("follow-up").into()]);
        let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
        let input_submission = submit(&root, input("a")).await;
        tool_running(&harness, &root).await;
        let f = submit(&root, input("f")).await;
        second_gate.resolve(());
        wait_for(
            || async { tool_status(&harness, &root, 1).await == Some(ToolSlotStatus::Done) },
            5000,
        )
        .await;
        first_gate.resolve(());
        settle(&f).await;
        assert_done(&status(&input_submission).await, None);
        assert_eq!(
            last(
                &transcript(&all_entries(&root, context()).await.unwrap()),
                4
            ),
            [
                "pi.tool-result",
                "pi.reset:two",
                "pi.user:f",
                "pi.assistant:follow-up"
            ]
        );
        harness.close(context()).await.unwrap();
    }

    #[tokio::test]
    async fn leaves_the_inbox_alone_when_the_run_s_task_is_aborted() {
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let first = gated(answer("never"));
        setup.faux.set_responses(vec![first.step.clone()]);
        let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
        let input_submission = submit(&root, input("a")).await;
        first.reached().await;
        let f = submit(&root, input("f")).await;
        let task_id = live(&harness, &root).await.unwrap().run.unwrap().task_id;
        harness.abort_task(task_id, context()).await.unwrap();
        assert_unanswered(&settle(&input_submission).await, "aborted");
        harness.wait_for_idle(context()).await.unwrap();
        assert_eq!(status(&f).await.state.status(), SubmissionStatus::Queued);
        assert_eq!(inbox(&harness, &root).await, vec![(f.id(), "followUp")]);
        harness.close(context()).await.unwrap();
    }

    #[tokio::test]
    async fn returns_a_queued_submission_for_its_repeated_request_id_without_a_second_item() {
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let first = gated(answer("first"));
        setup.faux.set_responses(vec![first.step.clone()]);
        let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
        submit(&root, input("a")).await;
        first.reached().await;
        let requested = || InputSubmissionDraft {
            request_id: Some("r".to_owned()),
            ..InputSubmissionDraft::new("f")
        };
        let queued = submit(&root, requested()).await;
        let again = submit(&root, requested()).await;
        assert_eq!(again.id(), queued.id());
        assert_eq!(
            inbox(&harness, &root).await,
            vec![(queued.id(), "followUp")]
        );
        harness.close(context()).await.unwrap();
    }

    #[tokio::test]
    async fn withdraws_a_middle_item_with_one_positional_removal() {
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let first = gated(answer("first"));
        setup.faux.set_responses(vec![first.step.clone()]);
        let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
        submit(&root, input("a")).await;
        first.reached().await;
        let mut items = Vec::new();
        for text in ["x", "y", "z"] {
            items.push(submit(&root, input(text)).await);
        }
        let ops = inbox_ops(&harness);
        items[1].abort(context()).await.unwrap();
        assert_eq!(taken(&ops), vec![json(r#"[["p",["items"],1,1,[]]]"#)]);
        assert_eq!(
            inbox(&harness, &root).await,
            vec![(items[0].id(), "followUp"), (items[2].id(), "followUp")]
        );
        harness.close(context()).await.unwrap();
    }

    /// TS overrides `MemoryStorage.commit` to record the inbox writes once its
    /// ID is known; `ControlledStorage` records every batch, so the test reads
    /// the batches committed after the one whose publication revealed the ID.
    #[tokio::test]
    async fn stores_the_inbox_as_a_base_exactly_when_it_becomes_empty() {
        let storage = ControlledStorage::new();
        let learned: Arc<Mutex<Option<(crate::types::DocumentId, usize)>>> = Arc::default();
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let first = gated(answer("first"));
        setup
            .faux
            .set_responses(vec![first.step.clone(), answer("second").into()]);
        let OpenChat { harness, root } =
            open_chat(Arc::clone(&storage) as Arc<dyn Storage>, &setup, None)
                .await
                .unwrap();
        let (sink, counter) = (Arc::clone(&learned), Arc::clone(&storage));
        let subscription = harness
            .subscribe_commits(Arc::new(move |publication, _| {
                for change in document_changes(publication) {
                    if change.record.kind == "pi.inbox" {
                        let mut learned = sink.lock().unwrap_or_else(PoisonError::into_inner);
                        if learned.is_none() {
                            *learned = Some((change.record.id, counter.commit_count()));
                        }
                    }
                }
            }))
            .unwrap();
        drop(subscription);
        let input_submission = submit(&root, input("a")).await;
        first.reached().await;
        submit(&root, input("f1")).await;
        let f2 = submit(&root, input("f2")).await;
        first.release();
        settle(&input_submission).await;
        settle(&f2).await;
        let (inbox_id, from) = learned
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .expect("the inbox ID was learned");
        let written: Vec<(&str, bool)> = storage.commits()[from..]
            .iter()
            .flatten()
            .filter_map(|write| match write {
                StorageWrite::DocumentChange { id, content } if *id == inbox_id => {
                    Some(match content {
                        DocumentContent::Base(base) => (
                            "base",
                            base.value
                                .get("items")
                                .and_then(JsonValue::as_array)
                                .is_some_and(<[JsonValue]>::is_empty),
                        ),
                        DocumentContent::Delta(_) => ("delta", false),
                    })
                }
                _ => None,
            })
            .collect();
        // The inbox ID is learned from the f1 push; later writes: the f2 push, removing f1, and emptying the inbox.
        assert_eq!(
            written,
            vec![("delta", false), ("delta", false), ("base", true)]
        );
        harness.close(context()).await.unwrap();
    }

    #[test]
    fn keeps_a_complete_inbox_base_exactly_while_it_is_empty_and_a_usage_base_on_every_change() {
        let info = CheckpointInfo {
            deltas_since_base: 1000,
        };
        let object = |text: &str| match json(text) {
            JsonValue::Object(object) => object,
            other => panic!("not an object: {other}"),
        };
        let inbox_when = INBOX_DOC.definition().checkpoint_when.unwrap();
        assert!(inbox_when(&object(r#"{"items":[]}"#), &[], info));
        assert!(!inbox_when(
            &object(r#"{"items":[{"id":1,"mode":"followUp","content":"x"}]}"#),
            &[],
            info
        ));
        let usage_when = USAGE_DOC.definition().checkpoint_when.unwrap();
        assert!(usage_when(
            &object(r#"{"models":{},"tools":{}}"#),
            &[],
            info
        ));
    }
}

/// TS `describe("usage")`.
mod ledger {
    use super::*;

    #[tokio::test]
    async fn totals_assistant_usage_per_model_and_tool_usage_per_tool_and_sums_the_session() {
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let spent = spent_usage(
            1,
            2,
            3,
            4,
            10,
            UsageCost {
                input: 0.1,
                output: 0.2,
                cache_read: 0.3,
                cache_write: 0.4,
                total: 1.0,
            },
        );
        let gate = deferred();
        gate.resolve(());
        hold_tool(
            &setup,
            &gate,
            ToolExecutionResult {
                usage: Some(spent),
                ..empty_result()
            },
        );
        setup.faux.set_responses(vec![
            hold().into(),
            answer("done").into(),
            answer("other").into(),
        ]);
        let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
        settle(&submit(&root, input("a")).await).await;
        let entries = all_entries(&root, context()).await.unwrap();
        let assistants = assistant_messages(&entries);
        let (input_sum, output_sum, total_sum) =
            assistants.iter().fold((0, 0, 0), |sum, message| {
                (
                    sum.0 + message.usage.input,
                    sum.1 + message.usage.output,
                    sum.2 + message.usage.total_tokens,
                )
            });
        let usage = usage_of(&harness, &root).await.unwrap();
        let model = usage.models["faux/faux-1"];
        assert_eq!(
            (model.input, model.output, model.total_tokens),
            (input_sum, output_sum, total_sum)
        );
        let expected_tools: IndexMap<String, Usage> =
            [("hold".to_owned(), spent)].into_iter().collect();
        assert_eq!(usage.tools, expected_tools);
        let result = entries
            .iter()
            .find(|entry| entry.kind == "pi.tool-result")
            .unwrap();
        let Message::ToolResult(result) = &result.model.as_ref().unwrap()[0] else {
            panic!("not a tool result");
        };
        assert_eq!(result.usage, Some(spent));

        // A fork starts at zero; the Session total adds every conversation once.
        let fork = root
            .fork(
                entries.last().unwrap().id,
                ConversationCreateOptions::new(ConversationOwnership::Ownerless),
                context(),
            )
            .await
            .unwrap();
        assert_eq!(usage_of(&harness, &fork).await, Some(UsageState::default()));
        settle(&submit(&fork, input("b")).await).await;
        let fork_usage = usage_of(&harness, &fork).await.unwrap().models["faux/faux-1"];
        let total = harness.usage(context()).await.unwrap();
        assert_eq!(
            total.models["faux/faux-1"].output,
            output_sum + fork_usage.output
        );
        assert_eq!(total.tools, expected_tools);
        harness.close(context()).await.unwrap();
    }

    #[tokio::test]
    async fn counts_failed_attempts_converted_partials_and_tool_usage_replaced_by_after_tool() {
        let setup = chat_setup(RegisterFauxProviderOptions {
            tokens_per_second: Some(200.0),
            token_size: Some(FauxTokenSize {
                min: Some(1),
                max: Some(1),
            }),
            ..RegisterFauxProviderOptions::default()
        });
        let spent = spent_usage(5, 0, 0, 0, 5, UsageCost::default());
        let gate = deferred();
        gate.resolve(());
        hold_tool(&setup, &gate, empty_result());
        add_hooks(
            &setup.registry,
            tool_task(),
            ToolHooks {
                after_tool: Some(Arc::new(move |_, result, _, _| {
                    let replaced = ToolExecutionResult {
                        usage: Some(spent),
                        ..result.clone()
                    };
                    futures::future::ready(Ok(Some(replaced))).boxed()
                })),
                ..ToolHooks::default()
            },
            None,
        )
        .unwrap();
        let retryable = failure("503 Service Unavailable");
        setup.faux.set_responses(vec![
            retryable.into(),
            hold().into(),
            answer("done").into(),
            answer(&"x".repeat(400)).into(),
        ]);
        let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
        setup.settings.update(|settings| {
            settings.retry = Some(PartialRetryPolicy {
                enabled: Some(true),
                max_retries: Some(1),
                base_delay_ms: Some(1.0),
                ..PartialRetryPolicy::default()
            });
        });
        settle(&submit(&root, input("a")).await).await;
        let expected_tools: IndexMap<String, Usage> =
            [("hold".to_owned(), spent)].into_iter().collect();
        assert_eq!(
            usage_of(&harness, &root).await.unwrap().tools,
            expected_tools
        );

        // A partial committed while streaming becomes an aborted entry on abort; its usage counts too.
        let input_submission = submit(&root, input("b")).await;
        generation_streaming(&harness, &root).await;
        let task_id = live(&harness, &root).await.unwrap().run.unwrap().task_id;
        harness.abort_task(task_id, context()).await.unwrap();
        settle(&input_submission).await;
        let assistants = assistant_messages(&all_entries(&root, context()).await.unwrap());
        assert_eq!(
            assistants
                .iter()
                .map(|message| message.stop_reason)
                .collect::<Vec<_>>(),
            [
                StopReason::Error,
                StopReason::ToolUse,
                StopReason::Stop,
                StopReason::Aborted
            ]
        );
        let output: u64 = assistants.iter().map(|message| message.usage.output).sum();
        assert_eq!(
            usage_of(&harness, &root).await.unwrap().models["faux/faux-1"].output,
            output
        );
        harness.close(context()).await.unwrap();
    }

    #[tokio::test]
    async fn keeps_tools_named_like_object_prototype_keys_in_the_ledger_and_the_session_total() {
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
        let usage = spent_usage(1, 1, 0, 0, 2, UsageCost::default());
        let names = ["constructor", "__proto__", "toString"];
        let id = root.id();
        for name in names {
            for _ in 0..2 {
                root.commit(
                    move |tx| async move {
                        record_usage(&tx, id, UsageBucket::Tools, name, &usage).await
                    },
                    context(),
                )
                .await
                .unwrap();
            }
        }
        let total = harness.usage(context()).await.unwrap();
        assert_eq!(
            total.tools.keys().map(String::as_str).collect::<Vec<_>>(),
            names
        );
        for name in names {
            assert_eq!(total.tools[name].output, 2);
        }
        harness.close(context()).await.unwrap();
    }

    #[tokio::test]
    async fn keeps_usage_totals_exact_across_reopen_counting_a_partial_converted_after_reopen_once()
    {
        let directory = tempfile::Builder::new()
            .prefix("pi-durable-usage-")
            .tempdir()
            .unwrap();
        let path = directory.path().join("session.sqlite");
        let setup = chat_setup(RegisterFauxProviderOptions {
            tokens_per_second: Some(200.0),
            token_size: Some(FauxTokenSize {
                min: Some(1),
                max: Some(1),
            }),
            ..RegisterFauxProviderOptions::default()
        });
        setup.faux.set_responses(vec![
            answer("first").into(),
            answer(&"x".repeat(400)).into(),
            answer("again").into(),
        ]);
        let opened = open_chat(sqlite(&path).await, &setup, None).await.unwrap();
        settle(&submit(&opened.root, input("a")).await).await;
        submit(&opened.root, input("b")).await;
        generation_streaming(&opened.harness, &opened.root).await;
        // Closing mid-stream keeps the committed partial; the reopened request converts it into an aborted entry.
        opened.harness.close(context()).await.unwrap();
        let opened = open_chat(sqlite(&path).await, &setup, None).await.unwrap();
        opened.harness.resume().unwrap();
        opened.harness.wait_for_idle(context()).await.unwrap();
        let assistants = assistant_messages(&all_entries(&opened.root, context()).await.unwrap());
        assert_eq!(
            assistants
                .iter()
                .map(|message| message.stop_reason)
                .collect::<Vec<_>>(),
            [StopReason::Stop, StopReason::Aborted, StopReason::Stop]
        );
        let total = opened.harness.usage(context()).await.unwrap().models["faux/faux-1"];
        let sum = |field: fn(&Usage) -> u64| {
            assistants
                .iter()
                .map(|message| field(&message.usage))
                .sum::<u64>()
        };
        assert_eq!(
            [total.input, total.output, total.total_tokens],
            [
                sum(|usage| usage.input),
                sum(|usage| usage.output),
                sum(|usage| usage.total_tokens)
            ]
        );
        opened.harness.close(context()).await.unwrap();
    }

    #[tokio::test]
    async fn records_usage_as_numeric_sets_on_the_ledger_in_the_entry_s_commit() {
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        setup
            .faux
            .set_responses(vec![answer("one").into(), answer("two").into()]);
        let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
        let commits: Arc<Mutex<Vec<(usize, JsonValue)>>> = Arc::default();
        let sink = Arc::clone(&commits);
        let subscription = harness
            .subscribe_commits(Arc::new(move |publication, _| {
                for change in document_changes(publication) {
                    if change.record.kind != "pi.usage" {
                        continue;
                    }
                    let entries = publication
                        .changes
                        .iter()
                        .filter(|other| matches!(other, CommitChange::Entry(_)))
                        .count();
                    sink.lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .push((entries, ops_json(&change.ops)));
                }
            }))
            .unwrap();
        drop(subscription);
        settle(&submit(&root, input("a")).await).await;
        settle(&submit(&root, input("b")).await).await;
        let commits = commits
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone();
        assert_eq!(commits.len(), 2);
        let first = commits[0].1.as_array().unwrap();
        assert_eq!(first.len(), 1, "{}", commits[0].1);
        assert_eq!(first[0][0], json(r#""s""#));
        assert_eq!(first[0][1], json(r#"["models","faux/faux-1"]"#));
        assert!(first[0][2].as_object().is_some(), "{}", commits[0].1);
        assert!(
            commits[1]
                .1
                .as_array()
                .unwrap()
                .iter()
                .all(|op| op[0] == json(r#""s""#) && op[1][1] == json(r#""faux/faux-1""#)),
            "{}",
            commits[1].1
        );
        assert!(commits.iter().all(|(entries, _)| *entries >= 1));
        harness.close(context()).await.unwrap();
    }
}
