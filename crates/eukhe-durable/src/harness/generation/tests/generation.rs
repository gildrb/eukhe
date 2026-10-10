//! Port of `test/harness-generation.test.ts`.

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use eukhe_chord::json::{from_json, to_json, JsonValue};
use eukhe_pi_ai::api::StreamSimpleFn;
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_text, FauxAssistantMessageOptions, FauxContentBlock,
    FauxDeferredOptions, FauxResponseStep, FauxTokenSize, RegisterFauxProviderOptions,
};
use eukhe_pi_ai::types::{DeferredRequest, SimpleStreamOptions};
use eukhe_pi_ai::utils::diagnostics::ErrorObject;
use eukhe_pi_ai::utils::event_stream::AssistantMessageEventStream;
use eukhe_types::pi_ai::{
    AssistantMessage, AssistantMessageEvent, DeferredHandle, IndexMap, Message, ModelThinkingLevel,
    StopReason, SystemContent, SystemMessage, ThinkingLevel, TranscriptContext, UserContent,
    UserMessage,
};
use futures::FutureExt;

use crate::documents::{ConversationDoc, DocDefinition};
use crate::entries::USER_ENTRY;
use crate::harness::agent::resolve_settings;
use crate::harness::define::{define_extension, wrap_section};
use crate::harness::live::{LiveRun, LIVE_DOC};
use crate::harness::provider::PROVIDER_DOC;
use crate::harness::tests::chat_support::{
    all_entries, chat_setup, open_chat, text_of, unanswered, wait_for, ChatSetup, OpenChat,
};
use crate::harness::tests::support::{
    add_section, builtins, context, create_registry, generation_task,
};
use crate::harness::types::{
    AgentChange, CompactionPolicy, ConversationCreateOptions, ConversationRetryPolicy,
    ConversationStreamOptions, Extension, FieldChange, HarnessOptions, HarnessSettings,
    HarnessSettingsSource, InputSubmissionDraft, ModelRef, PartialCompactionPolicy,
    PartialProgressPolicy, PartialRetryPolicy, ProgressPolicy, QueueMode, ToolExecutionMode,
    WhenBusy,
};
use crate::harness::{Conversation, Harness, RootOptions, TaskAbortResult};
use crate::session::tests::support::ControlledStorage;
use crate::session::{SessionError, SessionResult, TaskDefinitionRef};
use crate::storage::MemoryStorage;
use crate::types::{
    CommitChange, ConversationOwnership, DocumentCommitChange, DocumentContent, EntryRecord,
    InputSubmission, LatestFork, Storage, StorageWrite, SubmissionCreate, SubmissionSettlement,
    SubmissionState, TaskId, TaskOptions, TaskOutcome, TaskOwnership, TaskQuery, TypedEntryDraft,
};

type Values = Arc<Mutex<Vec<JsonValue>>>;

fn storage() -> Arc<dyn Storage> {
    Arc::new(MemoryStorage::new())
}

fn json(text: &str) -> JsonValue {
    JsonValue::parse(text).expect("valid JSON literal")
}

fn input(text: &str) -> InputSubmissionDraft {
    InputSubmissionDraft::new(text)
}

fn text_message(text: &str) -> AssistantMessage {
    faux_assistant_message(
        vec![faux_text(text)],
        FauxAssistantMessageOptions::default(),
    )
}

fn error_message(text: &str) -> AssistantMessage {
    faux_assistant_message(
        Vec::<FauxContentBlock>::new(),
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::Error),
            error_message: Some(text.to_owned()),
            ..FauxAssistantMessageOptions::default()
        },
    )
}

/// TS `ERROR_503`.
fn error_503() -> AssistantMessage {
    error_message("503 Service Unavailable")
}

fn faux_model() -> ModelRef {
    ModelRef {
        provider: "faux".to_owned(),
        model_id: "faux-1".to_owned(),
    }
}

fn with_model(model: ModelRef) -> AgentChange {
    AgentChange {
        model: FieldChange::Set(model),
        ..AgentChange::default()
    }
}

fn ownerless_with_faux() -> ConversationCreateOptions {
    ConversationCreateOptions {
        agent: Some(with_model(faux_model())),
        ..ConversationCreateOptions::new(ConversationOwnership::Ownerless)
    }
}

/// The committed `pi.live` value; `null` when absent.
async fn live(harness: &Harness, conversation: &Conversation) -> JsonValue {
    harness
        .snapshot(&LIVE_DOC, conversation.id(), context())
        .await
        .unwrap()
        .map_or(JsonValue::Null, JsonValue::Object)
}

fn run_task_of(live: &JsonValue) -> Option<TaskId> {
    live.get("run")
        .and_then(|run| run.get("taskId"))
        .map(|id| from_json(id).unwrap())
}

async fn run_task(harness: &Harness, conversation: &Conversation) -> TaskId {
    wait_for(
        || async move { run_task_of(&live(harness, conversation).await).is_some() },
        5000,
    )
    .await;
    run_task_of(&live(harness, conversation).await).unwrap()
}

/// The committed partial of a `pi.live` value.
fn live_message(live: &JsonValue) -> Option<Message> {
    live.get("generation")
        .and_then(|generation| generation.get("message"))
        .map(|message| Message::Assistant(from_json(message).unwrap()))
}

fn live_text(live: &JsonValue) -> Option<String> {
    text_of(live_message(live).as_ref())
}

/// Committed `pi.live` values of every commit that has one.
fn live_publications(harness: &Harness) -> Values {
    let values: Values = Arc::default();
    let sink = Arc::clone(&values);
    let subscription = harness
        .subscribe_commits(Arc::new(move |publication, _| {
            for change in &publication.changes {
                if let CommitChange::Document(DocumentCommitChange::Document {
                    record,
                    value: Some(value),
                    ..
                }) = change
                {
                    if record.kind == "pi.live" {
                        sink.lock()
                            .unwrap_or_else(PoisonError::into_inner)
                            .push(JsonValue::Object(Arc::clone(value)));
                    }
                }
            }
        }))
        .unwrap();
    drop(subscription);
    values
}

fn values_of(values: &Values) -> Vec<JsonValue> {
    values
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
}

/// TS `toMatchObject`: objects match by `expected`'s keys, recursively;
/// arrays element-wise with equal length; other values are equal.
fn matches_object(actual: &JsonValue, expected: &JsonValue) -> bool {
    match (actual, expected) {
        (JsonValue::Object(actual), JsonValue::Object(expected)) => {
            expected.iter().all(|(key, expected)| {
                actual
                    .get(key)
                    .is_some_and(|actual| matches_object(actual, expected))
            })
        }
        (JsonValue::Array(actual), JsonValue::Array(expected)) => {
            actual.len() == expected.len()
                && actual
                    .iter()
                    .zip(expected.iter())
                    .all(|(actual, expected)| matches_object(actual, expected))
        }
        _ => actual == expected,
    }
}

#[track_caller]
fn assert_matches<T: serde::Serialize>(actual: &T, expected: &str) {
    let actual = to_json(actual).unwrap();
    assert!(
        matches_object(&actual, &json(expected)),
        "{actual:?} does not match {expected}"
    );
}

fn kinds(entries: &[EntryRecord]) -> Vec<&str> {
    entries.iter().map(|entry| entry.kind.as_str()).collect()
}

fn first_model(entry: &EntryRecord) -> &Message {
    &entry.model.as_ref().expect("entry has model messages")[0]
}

fn assistant_of(message: &Message) -> &AssistantMessage {
    let Message::Assistant(message) = message else {
        panic!("not an assistant message: {message:?}");
    };
    message
}

async fn first_task_state(harness: &Harness, conversation: &Conversation) -> JsonValue {
    let id = conversation.id();
    let page = harness
        .commit(
            move |tx| async move {
                tx.scan_tasks(
                    TaskQuery {
                        conversation_id: Some(id),
                        ..TaskQuery::default()
                    },
                    10,
                    None,
                )
                .await
            },
            context(),
        )
        .await
        .unwrap();
    to_json(&page.items[0].state).unwrap()
}

fn has_report(setup: &ChatSetup, message: &str) -> bool {
    setup
        .reports()
        .iter()
        .any(|report| report.to_string() == message)
}

/// `setup.models` with the faux provider's `stream_simple` replaced (TS
/// `withStream`, a `Proxy` over `models`).
fn with_stream(setup: &ChatSetup, stream_simple: StreamSimpleFn) {
    let mut provider = setup.faux.provider.clone();
    provider.stream_simple = stream_simple;
    setup.models.set_provider(provider);
}

/// A stream that starts with `partial` and ends with `last` 300 ms later
/// (TS async generator with a `setTimeout`).
fn delayed_stream(partial: AssistantMessage, last: AssistantMessage) -> StreamSimpleFn {
    Arc::new(move |_, _, _| {
        let stream = AssistantMessageEventStream::new();
        stream.push(AssistantMessageEvent::Start {
            partial: partial.clone(),
        });
        let (target, last) = (stream.clone(), last.clone());
        tokio::spawn(async move {
            tokio::time::sleep(Duration::from_millis(300)).await;
            target.end(Some(last));
        });
        stream
    })
}

fn pending(content: Vec<FauxContentBlock>) -> AssistantMessage {
    faux_assistant_message(
        content,
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::Pending),
            ..FauxAssistantMessageOptions::default()
        },
    )
}

#[tokio::test]
async fn answers_an_input_and_settles_its_submission() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_section(
        &setup.registry,
        "preamble",
        |_, _| async { Ok(Some("You are helpful.".to_owned())) }.boxed(),
        Some(false),
        None,
    )
    .unwrap();
    setup
        .faux
        .set_responses(vec![text_message("Hello there").into()]);
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    harness.resume().unwrap();
    let submission = root.submit(input("hi"), context()).await.unwrap();
    let settled = submission.wait(context()).await.unwrap();
    let SubmissionState::Input(InputSubmission::Done { entry, answer }) = settled.state else {
        panic!("Unexpected {:?}", settled.state);
    };

    let answer_entry = root
        .commit(move |tx| async move { tx.entry(answer).await }, context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(
        text_of(Some(first_model(&answer_entry))),
        Some("Hello there".to_owned())
    );
    let entries = all_entries(&root, context()).await.unwrap();
    assert_eq!(kinds(&entries), ["pi.user", "pi.system", "pi.assistant"]);
    assert_eq!(entries[0].id, entry);
    let Message::System(system) = first_model(&entries[1]) else {
        panic!("not a system message");
    };
    let mut sections = IndexMap::new();
    sections.insert("preamble".to_owned(), Some("You are helpful.".to_owned()));
    assert_eq!(
        entries[1].model,
        Some(vec![Message::System(SystemMessage {
            content: SystemContent::from(""),
            sections: Some(sections),
            tools_added: None,
            tools_removed: None,
            timestamp: system.timestamp,
        })])
    );
    assert_eq!(live(&harness, &root).await, json("{}"));
    let id = root.id();
    let page = harness
        .commit(
            move |tx| async move {
                tx.scan_tasks(
                    TaskQuery {
                        conversation_id: Some(id),
                        ..TaskQuery::default()
                    },
                    10,
                    None,
                )
                .await
            },
            context(),
        )
        .await
        .unwrap();
    let task = &page.items[0];
    assert_eq!(task.kind, "pi.generation");
    // Entries written by the generation are attributed to it; the admitted user entry is not task work.
    assert_eq!(
        entries
            .iter()
            .map(|entry| entry.by_task_id)
            .collect::<Vec<_>>(),
        [None, Some(task.id), Some(task.id)]
    );
    assert_eq!(
        to_json(&task.state).unwrap(),
        json(&format!(
            r#"{{"status":"terminal","outcome":{{"status":"completed","result":{{"entryId":{answer}}}}}}}"#
        ))
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn stores_partials_as_deltas_and_a_complete_base_once_nothing_is_in_flight() {
    let setup = chat_setup(RegisterFauxProviderOptions {
        tokens_per_second: Some(200.0),
        token_size: Some(FauxTokenSize {
            min: Some(1),
            max: Some(1),
        }),
        ..RegisterFauxProviderOptions::default()
    });
    setup
        .faux
        .set_responses(vec![text_message(&"w".repeat(200)).into()]);
    let storage = ControlledStorage::new();
    let OpenChat { harness, root } =
        open_chat(Arc::clone(&storage) as Arc<dyn Storage>, &setup, None)
            .await
            .unwrap();
    // TS `storage.findDocument({ kind: "pi.live", scope: root }, "current")`:
    // the root is the only conversation, so its creation holds the record.
    let record = storage
        .commits()
        .iter()
        .flatten()
        .find_map(|write| match write {
            StorageWrite::DocumentCreate { record, .. } if record.kind == "pi.live" => {
                Some(record.id)
            }
            _ => None,
        })
        .expect("pi.live exists");
    harness.resume().unwrap();
    root.submit(input("hi"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    let contents: Vec<&str> = storage
        .commits()
        .iter()
        .flatten()
        .filter_map(|write| match write {
            StorageWrite::DocumentChange { id, content } if *id == record => Some(match content {
                DocumentContent::Base(_) => "base",
                DocumentContent::Delta(_) => "delta",
            }),
            _ => None,
        })
        .collect();
    // Streaming writes deltas; the commit that settles the answer clears generation and writes a base.
    assert!(contents.contains(&"delta"));
    assert_eq!(contents.last(), Some(&"base"));
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn still_ends_a_run_whose_input_something_else_already_settled() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let busy = unanswered();
    setup.faux.set_responses(vec![busy.step.clone()]);
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let submission = root.submit(input("hi"), context()).await.unwrap();
    busy.reached().await;
    let submission_id = submission.id();
    root.commit(
        move |tx| async move {
            tx.settle_submission(
                submission_id,
                SubmissionSettlement::Unanswered {
                    reason: "withdrawn".to_owned(),
                    detail: None,
                },
            )
        },
        context(),
    )
    .await
    .unwrap();
    let task_id = run_task(&harness, &root).await;
    harness.abort_task(task_id, context()).await.unwrap();
    assert_eq!(
        harness
            .wait_for_task(task_id, context())
            .await
            .unwrap()
            .outcome,
        TaskOutcome::Aborted {
            reason: None,
            result: None
        }
    );
    // The earlier settlement stays; the run's own settlement leaves it unchanged.
    assert_matches(
        &submission.status(context()).await.unwrap(),
        r#"{"status":"unanswered","reason":"withdrawn"}"#,
    );
    assert_eq!(live(&harness, &root).await, json("{}"));
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn fails_with_no_model_when_no_model_is_configured_or_the_model_is_unknown() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let plain = harness
        .create_conversation(
            ConversationCreateOptions::new(ConversationOwnership::Ownerless),
            context(),
        )
        .await
        .unwrap();
    harness.resume().unwrap();
    let unset = plain
        .submit(input("hi"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    assert_matches(
        unset.record(),
        r#"{"status":"unanswered","reason":"no_model"}"#,
    );

    root.configure(
        with_model(ModelRef {
            provider: "faux".to_owned(),
            model_id: "missing".to_owned(),
        }),
        context(),
    )
    .await
    .unwrap();
    let unknown = root
        .submit(input("hi"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    assert_matches(
        unknown.record(),
        r#"{"status":"unanswered","reason":"no_model"}"#,
    );
    assert!(to_json(unknown.record())
        .unwrap()
        .get("entry")
        .and_then(JsonValue::as_f64)
        .is_some());
    assert_eq!(
        kinds(&all_entries(&root, context()).await.unwrap()),
        ["pi.user"]
    );
    assert_eq!(
        first_task_state(&harness, &root).await,
        json(
            r#"{"status":"terminal","outcome":{"status":"failed","error":{"message":"Model faux/missing is not available","detail":{"reason":"no_model"}}}}"#
        )
    );
    assert_eq!(live(&harness, &root).await, json("{}"));
    assert_eq!(live(&harness, &plain).await, json("{}"));
    harness.close(context()).await.unwrap();
}

fn retry(enabled: bool, max_retries: Option<u32>) -> PartialRetryPolicy {
    PartialRetryPolicy {
        enabled: Some(enabled),
        max_retries,
        base_delay_ms: Some(1.0),
        ..PartialRetryPolicy::default()
    }
}

#[tokio::test]
async fn retries_a_retryable_error_after_a_durable_backoff_and_then_answers() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_section(
        &setup.registry,
        "preamble",
        |_, _| async { Ok(Some("p".to_owned())) }.boxed(),
        Some(false),
        None,
    )
    .unwrap();
    setup
        .faux
        .set_responses(vec![error_503().into(), text_message("recovered").into()]);
    setup
        .settings
        .update(|settings| settings.retry = Some(retry(true, Some(3))));
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let values = live_publications(&harness);
    harness.resume().unwrap();
    let settled = root
        .submit(input("hi"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    assert_matches(settled.record(), r#"{"status":"done"}"#);
    let entries = all_entries(&root, context()).await.unwrap();
    assert_eq!(
        kinds(&entries),
        ["pi.user", "pi.system", "pi.assistant", "pi.assistant"]
    );
    assert_eq!(
        assistant_of(first_model(&entries[2])).stop_reason,
        StopReason::Error
    );
    let values = values_of(&values);
    assert!(values.iter().any(|value| {
        value
            .get("generation")
            .and_then(|generation| generation.get("retry"))
            .and_then(|retry| retry.get("error"))
            .and_then(JsonValue::as_str)
            == Some("503 Service Unavailable")
    }));
    assert!(values.iter().any(|value| {
        value
            .get("generation")
            .and_then(|generation| generation.get("attempt"))
            .and_then(JsonValue::as_f64)
            == Some(2.0)
    }));
    assert_eq!(live(&harness, &root).await, json("{}"));
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn fails_with_model_error_once_retries_are_exhausted() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    setup.faux.set_responses(vec![
        error_503().into(),
        error_503().into(),
        text_message("never").into(),
    ]);
    setup
        .settings
        .update(|settings| settings.retry = Some(retry(true, Some(1))));
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    harness.resume().unwrap();
    let settled = root
        .submit(input("hi"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    assert_matches(
        settled.record(),
        r#"{"status":"unanswered","reason":"model_error","detail":"503 Service Unavailable"}"#,
    );
    assert_eq!(
        kinds(&all_entries(&root, context()).await.unwrap()),
        ["pi.user", "pi.assistant", "pi.assistant"]
    );
    assert_eq!(setup.faux.get_pending_response_count(), 1);
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn fails_a_retryable_error_without_retrying_when_the_retry_policy_is_disabled() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    setup
        .faux
        .set_responses(vec![error_503().into(), text_message("never").into()]);
    setup.settings.update(|settings| {
        settings.retry = Some(PartialRetryPolicy {
            enabled: Some(false),
            ..PartialRetryPolicy::default()
        });
    });
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    harness.resume().unwrap();
    let settled = root
        .submit(input("hi"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    assert_matches(
        settled.record(),
        r#"{"status":"unanswered","reason":"model_error"}"#,
    );
    assert_eq!(setup.faux.state().call_count, 1);
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn reports_section_wrapper_failures_while_preparing() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_section(
        &setup.registry,
        "cwd",
        |_, _| async { Ok(Some("/repo".to_owned())) }.boxed(),
        None,
        None,
    )
    .unwrap();
    setup
        .registry
        .install(define_extension(Extension {
            wraps: vec![wrap_section("cwd", |_| {
                Err(SessionError::error("wrapper failed"))
            })],
            ..Extension::named("broken")
        }))
        .unwrap();
    setup.faux.set_responses(vec![text_message("ok").into()]);
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    harness.resume().unwrap();
    let settled = root
        .submit(input("hi"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    assert_matches(settled.record(), r#"{"status":"done"}"#);
    assert!(
        has_report(&setup, "wrapper failed"),
        "{:?}",
        setup.reports()
    );
    // The failed section is absent, so nothing was rendered.
    assert_eq!(
        kinds(&all_entries(&root, context()).await.unwrap()),
        ["pi.user", "pi.assistant"]
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn fails_a_non_retryable_error_without_retrying() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    setup.faux.set_responses(vec![
        error_message("Invalid request").into(),
        text_message("never").into(),
    ]);
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    harness.resume().unwrap();
    let settled = root
        .submit(input("hi"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    assert_matches(
        settled.record(),
        r#"{"status":"unanswered","reason":"model_error","detail":"Invalid request"}"#,
    );
    let state = first_task_state(&harness, &root).await;
    assert!(matches_object(
        &state,
        &json(
            r#"{"outcome":{"status":"failed","error":{"message":"Invalid request","detail":{"reason":"model_error"}}}}"#
        )
    ));
    harness.close(context()).await.unwrap();
}

fn deferred_setup(pending_fetches: f64, poll_after_ms: f64) -> ChatSetup {
    chat_setup(RegisterFauxProviderOptions {
        deferred: Some(FauxDeferredOptions {
            pending_fetches: Some(pending_fetches),
            poll_after_ms: Some(poll_after_ms),
        }),
        ..RegisterFauxProviderOptions::default()
    })
}

fn stream_deferred(setup: &ChatSetup) {
    setup.settings.update(|settings| {
        settings.stream = Some(ConversationStreamOptions {
            deferred: Some(DeferredRequest::Flag(true)),
            ..ConversationStreamOptions::default()
        });
    });
}

fn has_deferred(live: &JsonValue) -> bool {
    live.get("generation")
        .and_then(|generation| generation.get("deferred"))
        .is_some()
}

#[tokio::test]
async fn polls_a_deferred_response_until_it_is_ready() {
    let setup = deferred_setup(1.0, 1.0);
    setup
        .faux
        .set_responses(vec![text_message("deferred answer").into()]);
    stream_deferred(&setup);
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let values = live_publications(&harness);
    harness.resume().unwrap();
    let settled = root
        .submit(input("hi"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    let SubmissionState::Input(InputSubmission::Done { answer, .. }) = settled.state else {
        panic!("Unexpected {:?}", settled.state);
    };
    assert_eq!(setup.faux.state().deferred_fetch_count, 2);
    let poll_times: Vec<f64> = values_of(&values)
        .iter()
        .filter_map(|value| {
            value
                .get("generation")
                .and_then(|generation| generation.get("deferred"))
                .map(|deferred| deferred.get("pollAt").and_then(JsonValue::as_f64).unwrap())
        })
        .collect();
    assert_eq!(poll_times.len(), 2);
    assert!(poll_times[1] > poll_times[0]);
    let answer_entry = root
        .commit(move |tx| async move { tx.entry(answer).await }, context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(
        text_of(Some(first_model(&answer_entry))),
        Some("deferred answer".to_owned())
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn converts_the_committed_partial_when_aborted_during_streaming() {
    let setup = chat_setup(RegisterFauxProviderOptions {
        tokens_per_second: Some(20.0),
        token_size: Some(FauxTokenSize {
            min: Some(1),
            max: Some(1),
        }),
        ..RegisterFauxProviderOptions::default()
    });
    setup
        .faux
        .set_responses(vec![text_message(&"x".repeat(400)).into()]);
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    harness.resume().unwrap();
    let submission = root.submit(input("hi"), context()).await.unwrap();
    let task_id = run_task(&harness, &root).await;
    let (h, r) = (&harness, &root);
    wait_for(
        || async move { live_text(&live(h, r).await).is_some() },
        5000,
    )
    .await;
    let partial = live_text(&live(&harness, &root).await).unwrap();
    assert_eq!(
        harness.abort_task(task_id, context()).await.unwrap(),
        TaskAbortResult::Marked
    );
    assert_matches(
        submission.wait(context()).await.unwrap().record(),
        r#"{"status":"unanswered","reason":"aborted"}"#,
    );
    let entries = all_entries(&root, context()).await.unwrap();
    assert_eq!(kinds(&entries), ["pi.user", "pi.assistant"]);
    let converted = first_model(&entries[1]);
    assert_eq!(assistant_of(converted).stop_reason, StopReason::Aborted);
    assert!(text_of(Some(converted)).unwrap().starts_with(&partial));
    assert_eq!(live(&harness, &root).await, json("{}"));
    assert_eq!(
        harness
            .wait_for_task(task_id, context())
            .await
            .unwrap()
            .outcome,
        TaskOutcome::Aborted {
            reason: None,
            result: None
        }
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn cancels_a_deferred_response_when_aborted_during_polling() {
    let setup = deferred_setup(100.0, 60_000.0);
    setup.faux.set_responses(vec![text_message("never").into()]);
    stream_deferred(&setup);
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    harness.resume().unwrap();
    let submission = root.submit(input("hi"), context()).await.unwrap();
    let task_id = run_task(&harness, &root).await;
    let (h, r) = (&harness, &root);
    wait_for(|| async move { has_deferred(&live(h, r).await) }, 5000).await;
    harness.abort_task(task_id, context()).await.unwrap();
    assert_matches(
        submission.wait(context()).await.unwrap().record(),
        r#"{"status":"unanswered","reason":"aborted"}"#,
    );
    assert_eq!(setup.faux.state().cancelled_deferred.len(), 1);
    assert_eq!(live(&harness, &root).await, json("{}"));
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn reports_a_failed_deferred_cancellation_and_still_ends_the_run_aborted() {
    let setup = deferred_setup(100.0, 60_000.0);
    setup.faux.set_responses(vec![text_message("never").into()]);
    // TS: a `Proxy` over `models` whose `cancelDeferred` rejects.
    let mut provider = setup.faux.provider.clone();
    provider.cancel_deferred = Some(Arc::new(|_, _, _| {
        async { Err(ErrorObject::new("cancel failed").thrown()) }.boxed()
    }));
    setup.models.set_provider(provider);
    stream_deferred(&setup);
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    harness.resume().unwrap();
    let submission = root.submit(input("hi"), context()).await.unwrap();
    let task_id = run_task(&harness, &root).await;
    let (h, r) = (&harness, &root);
    wait_for(|| async move { has_deferred(&live(h, r).await) }, 5000).await;
    harness.abort_task(task_id, context()).await.unwrap();
    assert_matches(
        submission.wait(context()).await.unwrap().record(),
        r#"{"status":"unanswered","reason":"aborted"}"#,
    );
    assert!(has_report(&setup, "cancel failed"), "{:?}", setup.reports());
    assert_eq!(live(&harness, &root).await, json("{}"));
    harness.close(context()).await.unwrap();
}

async fn provider_session_id(harness: &Harness, conversation: &Conversation) -> Option<String> {
    harness
        .snapshot(&PROVIDER_DOC, conversation.id(), context())
        .await
        .unwrap()
        .and_then(|state| {
            state
                .get("sessionId")
                .and_then(JsonValue::as_str)
                .map(str::to_owned)
        })
}

#[tokio::test]
async fn forwards_stream_options_and_the_thinking_level() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let seen: Arc<Mutex<Vec<Option<SimpleStreamOptions>>>> = Arc::default();
    let step = |text: &'static str| {
        let seen = Arc::clone(&seen);
        FauxResponseStep::factory(move |_, options, _, _| {
            seen.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(options.cloned());
            Ok(text_message(text))
        })
    };
    setup.faux.set_responses(vec![step("a"), step("b")]);
    let mut headers = IndexMap::new();
    headers.insert("x-test".to_owned(), "1".to_owned());
    setup.settings.update(|settings| {
        settings.stream = Some(ConversationStreamOptions {
            timeout_ms: Some(1234.0),
            headers: Some(headers),
            ..ConversationStreamOptions::default()
        });
    });
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    root.configure(
        AgentChange {
            thinking_level: FieldChange::Set(ModelThinkingLevel::High),
            ..AgentChange::default()
        },
        context(),
    )
    .await
    .unwrap();
    harness.resume().unwrap();
    root.submit(input("one"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    // Both are read at the next preparation: the thinking level from pi.agent, the stream options live from settings.
    root.configure(
        AgentChange {
            thinking_level: FieldChange::Clear,
            ..AgentChange::default()
        },
        context(),
    )
    .await
    .unwrap();
    setup.settings.update(|settings| {
        settings.stream = Some(ConversationStreamOptions {
            timeout_ms: Some(99.0),
            ..ConversationStreamOptions::default()
        });
    });
    root.submit(input("two"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    let session_id = provider_session_id(&harness, &root).await.unwrap();
    let seen = seen.lock().unwrap_or_else(PoisonError::into_inner).clone();
    let first = seen[0].as_ref().unwrap();
    assert_eq!(first.stream.request.timeout_ms, Some(1234.0));
    let mut expected_headers = IndexMap::new();
    expected_headers.insert("x-test".to_owned(), Some("1".to_owned()));
    assert_eq!(first.stream.request.headers, Some(expected_headers));
    assert_eq!(first.reasoning, Some(ThinkingLevel::High));
    assert_eq!(
        first.stream.session_id.as_deref(),
        Some(session_id.as_str())
    );
    assert!(first.stream.request.signal.is_some());
    let second = seen[1].as_ref().unwrap();
    assert_eq!(second.reasoning, None);
    assert_eq!(second.stream.request.timeout_ms, Some(99.0));
    assert_eq!(
        second.stream.session_id.as_deref(),
        Some(session_id.as_str())
    );
    assert_eq!(second.stream.request.headers, None);
    harness.close(context()).await.unwrap();
}

fn last_user_text(request: &TranscriptContext) -> String {
    request
        .messages()
        .iter()
        .rev()
        .find_map(|message| match message {
            Message::User(UserMessage {
                content: UserContent::Text(text),
                ..
            }) => Some(text.clone()),
            Message::User(_) => Some(String::new()),
            _ => None,
        })
        .unwrap_or_default()
}

// Regression coverage for #10424.
#[tokio::test]
async fn keeps_provider_session_ids_request_local_across_concurrent_conversations() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let seen: Arc<Mutex<HashMap<String, Vec<String>>>> = Arc::default();
    let capture = {
        let seen = Arc::clone(&seen);
        FauxResponseStep::factory(move |request, options, _, _| {
            let text = last_user_text(request);
            seen.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .entry(text.clone())
                .or_default()
                .push(
                    options
                        .and_then(|options| options.stream.session_id.clone())
                        .unwrap_or_default(),
                );
            Ok(text_message(&format!("answer:{text}")))
        })
    };
    setup.faux.set_responses(vec![
        capture.clone(),
        capture.clone(),
        capture.clone(),
        capture,
    ]);
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let child = harness
        .create_conversation(ownerless_with_faux(), context())
        .await
        .unwrap();
    harness.resume().unwrap();
    for round in ["first", "second"] {
        futures::future::join_all([&root, &child].into_iter().enumerate().map(
            |(index, conversation)| async move {
                conversation
                    .submit(input(&format!("{round}-{index}")), context())
                    .await
                    .unwrap()
                    .wait(context())
                    .await
                    .unwrap();
            },
        ))
        .await;
    }
    let root_id = provider_session_id(&harness, &root).await.unwrap();
    let child_id = provider_session_id(&harness, &child).await.unwrap();
    assert_ne!(root_id, child_id);
    let seen = seen.lock().unwrap_or_else(PoisonError::into_inner).clone();
    assert_eq!(seen.get("first-0"), Some(&vec![root_id.clone()]));
    assert_eq!(seen.get("second-0"), Some(&vec![root_id]));
    assert_eq!(seen.get("first-1"), Some(&vec![child_id.clone()]));
    assert_eq!(seen.get("second-1"), Some(&vec![child_id]));
    harness.close(context()).await.unwrap();
}

/// TS `/^[0-9a-f]{8}-[0-9a-f]{4}-7[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/u`.
fn is_uuid_v7(text: &str) -> bool {
    let groups: Vec<&str> = text.split('-').collect();
    let hex = |group: &str| group.chars().all(|c| matches!(c, '0'..='9' | 'a'..='f'));
    groups.len() == 5
        && groups
            .iter()
            .zip([8, 4, 4, 4, 12])
            .all(|(group, len)| group.len() == len && hex(group))
        && groups[2].starts_with('7')
        && groups[3].starts_with(['8', '9', 'a', 'b'])
}

// Regression coverage for #10424.
#[tokio::test]
async fn creates_and_persists_provider_state_before_a_legacy_conversations_request() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let sent: Arc<Mutex<Option<String>>> = Arc::default();
    let sink = Arc::clone(&sent);
    setup
        .faux
        .set_responses(vec![FauxResponseStep::factory(move |_, options, _, _| {
            *sink.lock().unwrap_or_else(PoisonError::into_inner) =
                options.and_then(|options| options.stream.session_id.clone());
            Ok(text_message("ok"))
        })]);
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let id = root.id();
    root.commit(
        move |tx| async move { tx.retire_doc(&PROVIDER_DOC, id).await },
        context(),
    )
    .await
    .unwrap();
    assert_eq!(
        harness
            .snapshot(&PROVIDER_DOC, id, context())
            .await
            .unwrap(),
        None
    );
    harness.resume().unwrap();
    root.submit(input("legacy"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    let stored = provider_session_id(&harness, &root).await.unwrap();
    assert!(is_uuid_v7(&stored), "{stored}");
    assert_eq!(
        sent.lock().unwrap_or_else(PoisonError::into_inner).clone(),
        Some(stored)
    );
    harness.close(context()).await.unwrap();
}

/// TS settings object with a `stream` getter over a mutable `timeoutMs`.
struct GetterSettings {
    timeout_ms: Arc<AtomicU64>,
}

impl HarnessSettingsSource for GetterSettings {
    fn current(&self) -> Arc<HarnessSettings> {
        Arc::new(HarnessSettings {
            stream: Some(ConversationStreamOptions {
                timeout_ms: Some(f64::from_bits(self.timeout_ms.load(Ordering::SeqCst))),
                ..ConversationStreamOptions::default()
            }),
            retry: Some(PartialRetryPolicy {
                base_delay_ms: Some(1.0),
                ..PartialRetryPolicy::default()
            }),
            ..HarnessSettings::default()
        })
    }
}

#[tokio::test]
async fn reads_settings_through_getters_at_every_decision() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let timeout_ms = Arc::new(AtomicU64::new(111.0_f64.to_bits()));
    let seen: Arc<Mutex<Vec<Option<f64>>>> = Arc::default();
    let first = {
        let (seen, timeout_ms) = (Arc::clone(&seen), Arc::clone(&timeout_ms));
        FauxResponseStep::factory(move |_, options, _, _| {
            seen.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(options.and_then(|options| options.stream.request.timeout_ms));
            // The user changes the setting while the first attempt runs.
            timeout_ms.store(222.0_f64.to_bits(), Ordering::SeqCst);
            Ok(error_503())
        })
    };
    let second = {
        let seen = Arc::clone(&seen);
        FauxResponseStep::factory(move |_, options, _, _| {
            seen.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(options.and_then(|options| options.stream.request.timeout_ms));
            Ok(text_message("ok"))
        })
    };
    setup.faux.set_responses(vec![first, second]);
    let mut options = HarnessOptions::new(setup.models.clone(), Arc::new(setup.registry.clone()));
    options.settings = Some(Arc::new(GetterSettings { timeout_ms }));
    let harness = Harness::open(storage(), options, context()).await.unwrap();
    let root = harness
        .root(
            RootOptions {
                agent: Some(with_model(faux_model())),
                ..RootOptions::default()
            },
            context(),
        )
        .await
        .unwrap();
    harness.resume().unwrap();
    let settled = root
        .submit(input("hi"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    assert_matches(settled.record(), r#"{"status":"done"}"#);
    // The retry prepares again, so it resolves the settings again and sends the new timeout.
    assert_eq!(
        *seen.lock().unwrap_or_else(PoisonError::into_inner),
        [Some(111.0), Some(222.0)]
    );
    harness.close(context()).await.unwrap();
}

#[test]
fn resolves_settings_over_the_built_in_defaults() {
    let defaults = resolve_settings(None);
    assert!(defaults.extensions.is_none());
    assert_eq!(defaults.stream, ConversationStreamOptions::default());
    assert_eq!(
        defaults.retry,
        ConversationRetryPolicy {
            enabled: true,
            max_retries: 3,
            base_delay_ms: 2000.0,
            max_agent_delay_ms: Some(60000.0),
        }
    );
    assert_eq!(
        defaults.compaction,
        CompactionPolicy {
            enabled: true,
            reserve_tokens: 16384.0,
            keep_recent_tokens: 20000.0,
            background_tokens: 32768.0,
        }
    );
    assert_eq!(
        defaults.progress,
        ProgressPolicy {
            partial_interval_ms: 100.0,
            output_interval_ms: 100.0,
        }
    );
    assert_eq!(defaults.tool_execution, ToolExecutionMode::Parallel);
    assert_eq!(defaults.steering_mode, QueueMode::OneAtATime);
    assert_eq!(defaults.follow_up_mode, QueueMode::OneAtATime);

    let partial = resolve_settings(Some(&HarnessSettings {
        retry: Some(PartialRetryPolicy {
            enabled: Some(false),
            ..PartialRetryPolicy::default()
        }),
        compaction: Some(PartialCompactionPolicy {
            background_tokens: Some(0.0),
            ..PartialCompactionPolicy::default()
        }),
        ..HarnessSettings::default()
    }));
    assert_eq!(
        partial.retry,
        ConversationRetryPolicy {
            enabled: false,
            ..defaults.retry
        }
    );
    assert_eq!(
        partial.compaction,
        CompactionPolicy {
            background_tokens: 0.0,
            ..defaults.compaction
        }
    );

    let progress = resolve_settings(Some(&HarnessSettings {
        progress: Some(PartialProgressPolicy {
            output_interval_ms: Some(500.0),
            ..PartialProgressPolicy::default()
        }),
        ..HarnessSettings::default()
    }));
    assert_eq!(
        progress.progress,
        ProgressPolicy {
            partial_interval_ms: 100.0,
            output_interval_ms: 500.0,
        }
    );
}

/// Whether a run over a stream whose partial is followed 300 ms later by the
/// final message publishes that partial under `settings`.
async fn published_partial(settings: HarnessSettings) -> bool {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    setup.settings.set(settings);
    with_stream(
        &setup,
        delayed_stream(pending(vec![faux_text("partial")]), text_message("final")),
    );
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let values = live_publications(&harness);
    harness.resume().unwrap();
    let submission = root.submit(input("hi"), context()).await.unwrap();
    assert_matches(
        submission.wait(context()).await.unwrap().record(),
        r#"{"status":"done"}"#,
    );
    harness.close(context()).await.unwrap();
    values_of(&values)
        .iter()
        .any(|value| live_text(value).as_deref() == Some("partial"))
}

#[tokio::test(start_paused = true)]
async fn commits_partials_no_more_often_than_progress_partial_interval_ms() {
    // 300 ms is longer than the default 100 ms, shorter than the configured interval.
    assert!(published_partial(HarnessSettings::default()).await);
    assert!(
        !published_partial(HarnessSettings {
            progress: Some(PartialProgressPolicy {
                partial_interval_ms: Some(5000.0),
                ..PartialProgressPolicy::default()
            }),
            ..HarnessSettings::default()
        })
        .await
    );
}

/// The first `pi.system` message of a conversation.
async fn system_of(conversation: &Conversation) -> SystemMessage {
    let entry = all_entries(conversation, context())
        .await
        .unwrap()
        .into_iter()
        .find(|entry| entry.kind == "pi.system")
        .expect("a system entry");
    let Message::System(message) = first_model(&entry).clone() else {
        panic!("not a system message");
    };
    message
}

static TEST_AGENT_DOC: ConversationDoc<JsonValue> = match ConversationDoc::define(
    DocDefinition {
        kind: "test.agent",
        version: 1,
        initial: || JsonValue::parse(r#"{"cwd":"/","kind":"main"}"#).expect("valid JSON literal"),
        migrate: None,
        checkpoint_when: None,
    },
    LatestFork::Current,
) {
    Ok(token) => token,
    Err(_) => panic!("valid definition"),
};

/// `input.read.snapshot(Agent, input.conversationId)?.[key]`.
fn agent_field(
    input: &crate::harness::types::PromptInput,
    cx: &eukhe_chord::context::Context,
    key: &'static str,
) -> futures::future::BoxFuture<'static, SessionResult<Option<String>>> {
    use crate::types::DocumentReaderExt;
    let read = input
        .read
        .snapshot(&TEST_AGENT_DOC, input.conversation_id, cx);
    async move {
        Ok(read.await?.and_then(|agent| {
            agent
                .get(key)
                .and_then(JsonValue::as_str)
                .map(str::to_owned)
        }))
    }
    .boxed()
}

#[tokio::test]
async fn renders_sections_that_read_conversation_documents_through_input_read() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_section(
        &setup.registry,
        "cwd",
        |input, cx| agent_field(input, cx, "cwd"),
        None,
        None,
    )
    .unwrap();
    add_section(
        &setup.registry,
        "agents",
        |input, cx| {
            let kind = agent_field(input, cx, "kind");
            async move {
                Ok(if kind.await?.as_deref() == Some("sub") {
                    None
                } else {
                    Some("Read AGENTS.md".to_owned())
                })
            }
            .boxed()
        },
        None,
        None,
    )
    .unwrap();
    setup
        .faux
        .set_responses(vec![text_message("a").into(), text_message("b").into()]);
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let id = root.id();
    root.commit(
        move |tx| async move {
            tx.doc(&TEST_AGENT_DOC, id)
                .await?
                .set("cwd", JsonValue::from("/repo"))?;
            Ok(())
        },
        context(),
    )
    .await
    .unwrap();
    let sub = harness
        .create_conversation(
            ConversationCreateOptions {
                init: Some(Box::new(|tx, id| {
                    async move {
                        let agent = tx.doc(&TEST_AGENT_DOC, id).await?;
                        agent.set("kind", JsonValue::from("sub"))?;
                        agent.set("cwd", JsonValue::from("/sub"))?;
                        Ok(())
                    }
                    .boxed()
                })),
                ..ownerless_with_faux()
            },
            context(),
        )
        .await
        .unwrap();
    harness.resume().unwrap();
    root.submit(input("one"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    sub.submit(input("two"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    let root_system = system_of(&root).await;
    let root_sections = root_system.sections.as_ref().unwrap();
    assert_eq!(
        root_sections.get("cwd"),
        Some(&Some("<cwd>\n/repo\n</cwd>".to_owned()))
    );
    assert_eq!(
        root_sections.get("agents"),
        Some(&Some("<agents>\nRead AGENTS.md\n</agents>".to_owned()))
    );
    let sub_system = system_of(&sub).await;
    let mut expected = IndexMap::new();
    expected.insert("cwd".to_owned(), Some("<cwd>\n/sub\n</cwd>".to_owned()));
    assert_eq!(
        sub_system,
        SystemMessage {
            content: SystemContent::from(""),
            sections: Some(expected),
            tools_added: None,
            tools_removed: None,
            timestamp: sub_system.timestamp,
        }
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test(start_paused = true)]
async fn commits_no_partial_for_a_response_that_turns_deferred_after_an_empty_start_event() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let handle = DeferredHandle {
        provider: "faux".to_owned(),
        model_id: "faux-1".to_owned(),
        api: "faux".to_owned(),
        id: "handle-1".to_owned(),
        expires_at: None,
        poll_after_ms: Some(60_000.0),
        data: None,
    };
    let last = faux_assistant_message(
        Vec::<FauxContentBlock>::new(),
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::Deferred),
            deferred: Some(handle),
            ..FauxAssistantMessageOptions::default()
        },
    );
    // 300 ms is longer than the partial throttle: an empty partial would be committed then.
    with_stream(&setup, delayed_stream(pending(Vec::new()), last));
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let values = live_publications(&harness);
    let submission = root.submit(input("hi"), context()).await.unwrap();
    let (h, r) = (&harness, &root);
    wait_for(|| async move { has_deferred(&live(h, r).await) }, 5000).await;
    assert!(!values_of(&values).iter().any(|value| {
        value
            .get("generation")
            .and_then(|generation| generation.get("message"))
            .is_some()
    }));
    let task_id = run_task_of(&live(&harness, &root).await).unwrap();
    harness.abort_task(task_id, context()).await.unwrap();
    assert_matches(
        submission.wait(context()).await.unwrap().record(),
        r#"{"status":"unanswered","reason":"aborted"}"#,
    );
    assert_eq!(
        kinds(&all_entries(&root, context()).await.unwrap()),
        ["pi.user"]
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test(start_paused = true)]
async fn faults_a_run_task_settling_its_inputs_and_converting_the_committed_partial() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    // TS gives the final message a function property, which is not strict
    // JSON; Rust messages are typed, so the closest equivalent is a count
    // beyond `Number.MAX_SAFE_INTEGER`, which is not exact JSON.
    let mut last = text_message("final");
    last.usage.input = u64::MAX;
    with_stream(
        &setup,
        delayed_stream(pending(vec![faux_text("partial")]), last),
    );
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let values = live_publications(&harness);
    harness.resume().unwrap();
    let submission = root.submit(input("hi"), context()).await.unwrap();
    let settled = submission.wait(context()).await.unwrap();
    assert_matches(
        settled.record(),
        r#"{"status":"unanswered","reason":"faulted"}"#,
    );
    let detail = to_json(settled.record()).unwrap();
    let detail = detail
        .get("detail")
        .and_then(JsonValue::as_str)
        .unwrap_or_default();
    assert!(detail.contains("not exact JSON"), "{detail}");
    assert!(values_of(&values)
        .iter()
        .any(|value| live_text(value).as_deref() == Some("partial")));
    let entries = all_entries(&root, context()).await.unwrap();
    assert_eq!(kinds(&entries), ["pi.user", "pi.assistant"]);
    assert_eq!(
        assistant_of(first_model(&entries[1])).stop_reason,
        StopReason::Aborted
    );
    assert_eq!(
        text_of(Some(first_model(&entries[1]))),
        Some("partial".to_owned())
    );
    assert_eq!(live(&harness, &root).await, json("{}"));
    assert!(matches_object(
        &first_task_state(&harness, &root).await,
        &json(r#"{"status":"terminal","outcome":{"status":"faulted"}}"#)
    ));
    harness.close(context()).await.unwrap();
}

/// TS `{ ...GenerationTask.definition, version: 2 }`.
struct GenerationV2;

impl TaskDefinitionRef for GenerationV2 {
    fn name(&self) -> &'static str {
        "pi.generation"
    }

    fn version(&self) -> u64 {
        2
    }

    fn initial(&self, input: &JsonValue) -> SessionResult<JsonValue> {
        generation_task().erase().as_definition_ref().initial(input)
    }
}

#[tokio::test]
async fn orphans_a_blocked_run_task_with_full_run_cleanup() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let id = root.id();
    // A run whose task was stored by a newer generation definition this process cannot run.
    let (task_id, submission_id) = harness
        .commit(
            move |tx| async move {
                let entry = tx
                    .append_typed_entry(
                        &USER_ENTRY,
                        id,
                        TypedEntryDraft {
                            model: Some(vec![Message::User(UserMessage {
                                content: UserContent::Text("hi".to_owned()),
                                timestamp: 1,
                            })]),
                            ..TypedEntryDraft::default()
                        },
                    )
                    .await?;
                let submission = tx
                    .create_submission(SubmissionCreate {
                        conversation_id: id,
                        request_id: None,
                        state: SubmissionState::Input(InputSubmission::Placed {
                            entry: entry.entry().id,
                        }),
                    })
                    .await?;
                let task_id = tx
                    .create_task(
                        Arc::new(GenerationV2),
                        JsonValue::object(),
                        TaskOptions {
                            ownership: TaskOwnership::Conversation,
                            conversation_id: Some(id),
                            background: None,
                            abandon_on_restart: None,
                        },
                    )
                    .await?;
                tx.doc(&LIVE_DOC, id).await?.set(
                    "run",
                    to_json(&LiveRun {
                        task_id,
                        inputs: vec![submission.id],
                    })?,
                )?;
                Ok((task_id, submission.id))
            },
            context(),
        )
        .await
        .unwrap();
    harness.resume().unwrap();
    let busy = root
        .submit(
            InputSubmissionDraft {
                when_busy: Some(WhenBusy::Reject),
                ..input("busy")
            },
            context(),
        )
        .await;
    let Err(error) = busy else {
        panic!("a busy conversation admitted the input");
    };
    assert!(error.to_string().contains("is busy"), "{error}");
    assert_eq!(
        harness.abort_task(task_id, context()).await.unwrap(),
        TaskAbortResult::Marked
    );
    assert_eq!(
        harness
            .wait_for_task(task_id, context())
            .await
            .unwrap()
            .outcome,
        TaskOutcome::Orphaned {
            reason: "task_too_old".to_owned()
        }
    );
    assert_matches(
        &harness
            .submission(submission_id, context())
            .await
            .unwrap()
            .unwrap()
            .status(context())
            .await
            .unwrap(),
        r#"{"status":"unanswered","reason":"task_too_old"}"#,
    );
    assert_eq!(live(&harness, &root).await, json("{}"));
    harness.close(context()).await.unwrap();
}

/// TS builds a `RegistrySnapshot` without `pi.generation` and expects
/// `Harness.open` to reject it. In Rust `RegistrySnapshot` is a concrete
/// type that only `create_registry()` builds, always with the built-in
/// tasks, so a snapshot without them cannot be constructed; the closest
/// observable equivalent checks that even an empty registry's snapshot
/// resolves every built-in task by name.
#[test]
fn rejects_a_registry_without_the_built_in_tasks() {
    use crate::harness::types::RegistryReader;
    let snapshot = create_registry().snapshot();
    let expected = builtins();
    for name in ["pi.generation", "pi.tool", "pi.compaction"] {
        assert!(snapshot.task(name).is_some(), "{name} is missing");
    }
    assert_eq!(
        snapshot
            .task("pi.generation")
            .map(crate::tasks::AnyTask::name),
        Some(expected.generation.name())
    );
}
