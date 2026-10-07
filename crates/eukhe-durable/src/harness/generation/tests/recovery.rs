//! Port of `test/harness-generation-recovery.test.ts`.

use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::json::{JsonObject, JsonValue};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, FauxAssistantMessageOptions, FauxDeferredOptions, FauxResponseStep,
    FauxTokenSize, RegisterFauxProviderOptions,
};
use eukhe_pi_ai::types::DeferredRequest;
use eukhe_types::pi_ai::{AssistantContentBlock, AssistantMessage, Message, StopReason};
use futures::FutureExt;

use crate::harness::live::LIVE_DOC;
use crate::harness::tests::chat_support::{
    all_entries, chat_setup, open_chat, text_of, unanswered, wait_for, ChatSetup, OpenChat,
};
use crate::harness::tests::support::{add_section, context, create_models};
use crate::harness::tests::task_support::{aborted, deferred, Deferred};
use crate::harness::types::{ConversationStreamOptions, InputSubmissionDraft, PartialRetryPolicy};
use crate::harness::Harness;
use crate::storage::sqlite::{open_native_sqlite_storage, NativeSqliteStorageOptions};
use crate::types::{SubmissionStatus, TaskId};

const WAIT_MS: u64 = 5000;

fn sqlite_path(directory: &tempfile::TempDir) -> PathBuf {
    directory.path().join("session.sqlite")
}

fn temp() -> tempfile::TempDir {
    tempfile::Builder::new()
        .prefix("pi-durable-generation-")
        .tempdir()
        .unwrap()
}

async fn open(path: &PathBuf, setup: &ChatSetup) -> OpenChat {
    let storage = open_native_sqlite_storage(path, NativeSqliteStorageOptions::default())
        .await
        .unwrap();
    open_chat(Arc::new(storage), setup, None).await.unwrap()
}

fn input(text: &str) -> InputSubmissionDraft {
    InputSubmissionDraft::new(text)
}

fn json(text: &str) -> serde_json::Value {
    serde_json::from_str(text).expect("valid JSON literal")
}

fn plain(value: &JsonObject) -> serde_json::Value {
    serde_json::Value::from(&JsonValue::Object(Arc::new(value.clone())))
}

/// vitest `toMatchObject`: objects match by subset, arrays element-wise with equal length.
fn matches_object(actual: &serde_json::Value, expected: &serde_json::Value) -> bool {
    match (actual, expected) {
        (serde_json::Value::Object(actual), serde_json::Value::Object(expected)) => {
            expected.iter().all(|(key, value)| {
                actual
                    .get(key)
                    .is_some_and(|actual| matches_object(actual, value))
            })
        }
        (serde_json::Value::Array(actual), serde_json::Value::Array(expected)) => {
            actual.len() == expected.len()
                && actual
                    .iter()
                    .zip(expected)
                    .all(|(actual, expected)| matches_object(actual, expected))
        }
        _ => actual == expected,
    }
}

fn assert_match(actual: &serde_json::Value, expected: &serde_json::Value) {
    assert!(
        matches_object(actual, expected),
        "{actual} does not match {expected}"
    );
}

async fn live(harness: &Harness, chat: &OpenChat) -> serde_json::Value {
    let value = harness
        .snapshot(&LIVE_DOC, chat.root.id(), context())
        .await
        .unwrap()
        .expect("pi.live exists");
    plain(&value)
}

async fn run_task_id(chat: &OpenChat) -> TaskId {
    let value = live(&chat.harness, chat).await;
    TaskId::from_number(value["run"]["taskId"].as_u64().expect("a run"))
}

async fn checkpoint(harness: &Harness, id: TaskId) -> Option<serde_json::Value> {
    let record = harness.get_task(id, context()).await.unwrap()?;
    record.state.checkpoint().map(serde_json::Value::from)
}

fn kinds(entries: &[crate::types::EntryRecord]) -> Vec<&str> {
    entries.iter().map(|entry| entry.kind.as_str()).collect()
}

fn generation_text(value: &serde_json::Value) -> Option<String> {
    let message: AssistantMessage =
        serde_json::from_value(value.get("generation")?.get("message")?.clone()).ok()?;
    text_of(Some(&Message::Assistant(message)))
}

fn signal_of(
    options: Option<&eukhe_pi_ai::types::SimpleStreamOptions>,
) -> eukhe_chord::context::AbortSignal {
    options
        .and_then(|options| options.stream.request.signal.clone())
        .expect("a request signal")
}

fn deferred_setup() -> ChatSetup {
    chat_setup(RegisterFauxProviderOptions {
        deferred: Some(FauxDeferredOptions {
            poll_after_ms: Some(60_000.0),
            ..FauxDeferredOptions::default()
        }),
        ..RegisterFauxProviderOptions::default()
    })
}

fn manual_clock(setup: &ChatSetup, start: f64) -> Arc<AtomicU64> {
    let now = Arc::new(AtomicU64::new(start.to_bits()));
    let clock = Arc::clone(&now);
    setup.set_now(move || f64::from_bits(clock.load(Ordering::SeqCst)));
    now
}

fn deferred_stream(setup: &ChatSetup) {
    setup.settings.update(|settings| {
        settings.stream = Some(ConversationStreamOptions {
            deferred: Some(DeferredRequest::Flag(true)),
            ..ConversationStreamOptions::default()
        });
    });
}

async fn wait_deferred(chat: &OpenChat) {
    wait_for(
        || async {
            live(&chat.harness, chat).await["generation"]
                .get("deferred")
                .is_some()
        },
        WAIT_MS,
    )
    .await;
}

#[tokio::test(flavor = "multi_thread")]
async fn reruns_preparation_interrupted_before_its_commit() {
    let directory = temp();
    let path = sqlite_path(&directory);
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let reached: Deferred = deferred();
    let block = Arc::new(AtomicBool::new(true));
    let reach = reached.clone();
    add_section(
        &setup.registry,
        "preamble",
        move |_, cx| {
            let first = block.swap(false, Ordering::SeqCst);
            let reach = reach.clone();
            let signal = cx.abort_signal();
            async move {
                if first {
                    reach.resolve(());
                    return Err(aborted(&signal.expect("a section signal")).await);
                }
                Ok(Some("p".to_owned()))
            }
            .boxed()
        },
        None,
        None,
    )
    .unwrap();
    setup.faux.set_responses(vec![faux_assistant_message(
        "answer",
        FauxAssistantMessageOptions::default(),
    )
    .into()]);
    let mut opened = open(&path, &setup).await;
    opened.harness.resume().unwrap();
    let id = opened
        .root
        .submit(input("hi"), context())
        .await
        .unwrap()
        .id();
    reached.wait().await;
    let task_id = run_task_id(&opened).await;
    opened.harness.close(context()).await.unwrap();

    opened = open(&path, &setup).await;
    assert_eq!(
        checkpoint(&opened.harness, task_id).await,
        Some(json(r#"{"phase":"prepare","attempt":1}"#))
    );
    opened.harness.resume().unwrap();
    let handle = opened
        .harness
        .submission(id, context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(
        handle.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Done
    );
    assert_eq!(
        kinds(&all_entries(&opened.root, context()).await.unwrap()),
        ["pi.user", "pi.system", "pi.assistant"]
    );
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn resends_a_request_interrupted_before_any_partial_without_repeating_preparation() {
    let directory = temp();
    let path = sqlite_path(&directory);
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_section(
        &setup.registry,
        "preamble",
        |_, _| async { Ok(Some("p".to_owned())) }.boxed(),
        Some(false),
        None,
    )
    .unwrap();
    let reached: Deferred = deferred();
    let sent: Arc<Mutex<Vec<Vec<&'static str>>>> = Arc::default();
    let timeouts: Arc<Mutex<Vec<Option<f64>>>> = Arc::default();
    let reach = reached.clone();
    let (sent_sink, timeout_sink) = (Arc::clone(&sent), Arc::clone(&timeouts));
    setup.faux.set_responses(vec![
        FauxResponseStep::Factory(Arc::new(move |_, options, _, _| {
            reach.resolve(());
            let signal = signal_of(options);
            async move { Err(signal.cancelled().await) }.boxed()
        })),
        FauxResponseStep::factory(move |request, options, _, _| {
            sent_sink
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(request.messages().iter().map(Message::role).collect());
            timeout_sink
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(options.and_then(|options| options.stream.request.timeout_ms));
            Ok(faux_assistant_message(
                "answer",
                FauxAssistantMessageOptions::default(),
            ))
        }),
    ]);
    let timeout = |ms: f64| {
        move |settings: &mut crate::harness::types::HarnessSettings| {
            settings.stream = Some(ConversationStreamOptions {
                timeout_ms: Some(ms),
                ..ConversationStreamOptions::default()
            });
        }
    };
    let mut opened = open(&path, &setup).await;
    setup.settings.update(timeout(1234.0));
    opened.harness.resume().unwrap();
    let id = opened
        .root
        .submit(input("hi"), context())
        .await
        .unwrap()
        .id();
    reached.wait().await;
    let task_id = run_task_id(&opened).await;
    opened.harness.close(context()).await.unwrap();

    opened = open(&path, &setup).await;
    assert_match(
        &checkpoint(&opened.harness, task_id).await.unwrap(),
        &json(
            r#"{"phase":"request","attempt":1,"thinkingLevel":"off","streamOptions":{"timeoutMs":1234}}"#,
        ),
    );
    // The resend uses the pinned request, not options changed after preparation.
    setup.settings.update(timeout(999.0));
    assert_match(
        &live(&opened.harness, &opened).await,
        &json(r#"{"generation":{"attempt":1}}"#),
    );
    opened.harness.resume().unwrap();
    let handle = opened
        .harness
        .submission(id, context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(
        handle.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Done
    );
    assert_eq!(
        *sent.lock().unwrap_or_else(PoisonError::into_inner),
        [["user", "system"]]
    );
    assert_eq!(
        *timeouts.lock().unwrap_or_else(PoisonError::into_inner),
        [Some(1234.0)]
    );
    assert_eq!(
        kinds(&all_entries(&opened.root, context()).await.unwrap()),
        ["pi.user", "pi.system", "pi.assistant"]
    );
    opened.harness.close(context()).await.unwrap();
}

/// Stream a slow answer until an observer saw a partial, then close: the
/// crash. Returns the submission and the last observed partial text.
async fn crash_with_partial(path: &PathBuf) -> (crate::types::SubmissionId, String) {
    let slow = chat_setup(RegisterFauxProviderOptions {
        tokens_per_second: Some(20.0),
        token_size: Some(FauxTokenSize {
            min: Some(1),
            max: Some(1),
        }),
        ..RegisterFauxProviderOptions::default()
    });
    slow.faux.set_responses(vec![faux_assistant_message(
        "z".repeat(400),
        FauxAssistantMessageOptions::default(),
    )
    .into()]);
    let opened = open(path, &slow).await;
    opened.harness.resume().unwrap();
    let watch = opened
        .harness
        .watch_doc(&LIVE_DOC, opened.root.id(), context())
        .await
        .unwrap()
        .unwrap();
    let watched: Arc<Mutex<Option<String>>> = Arc::default();
    let sink = Arc::clone(&watched);
    watch
        .start(Arc::new(move |value, _, _| {
            if let Some(text) = value
                .as_deref()
                .and_then(|value| generation_text(&plain(value)))
            {
                *sink.lock().unwrap_or_else(PoisonError::into_inner) = Some(text);
            }
            async { Ok(()) }.boxed()
        }))
        .unwrap();
    let id = opened
        .root
        .submit(input("hi"), context())
        .await
        .unwrap()
        .id();
    wait_for(
        || {
            let seen = watched
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .is_some();
            async move { seen }
        },
        WAIT_MS,
    )
    .await;
    opened.harness.close(context()).await.unwrap();
    let watched = watched
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .unwrap();
    (id, watched)
}

#[tokio::test(flavor = "multi_thread")]
async fn converts_a_committed_partial_into_an_aborted_entry_and_resends_the_same_messages() {
    let directory = temp();
    let path = sqlite_path(&directory);
    let (id, watched) = crash_with_partial(&path).await;

    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let sent: Arc<Mutex<Vec<Vec<&'static str>>>> = Arc::default();
    let sent_sink = Arc::clone(&sent);
    setup
        .faux
        .set_responses(vec![FauxResponseStep::factory(move |request, _, _, _| {
            sent_sink
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(request.messages().iter().map(Message::role).collect());
            Ok(faux_assistant_message(
                "answer",
                FauxAssistantMessageOptions::default(),
            ))
        })]);
    let opened = open(&path, &setup).await;
    let partial = generation_text(&live(&opened.harness, &opened).await).unwrap();
    // Everything observers saw before the crash is durable.
    assert!(partial.starts_with(&watched));
    opened.harness.resume().unwrap();
    let handle = opened
        .harness
        .submission(id, context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(
        handle.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Done
    );
    assert_eq!(
        *sent.lock().unwrap_or_else(PoisonError::into_inner),
        [["user"]]
    );
    let entries = all_entries(&opened.root, context()).await.unwrap();
    assert_eq!(kinds(&entries), ["pi.user", "pi.assistant", "pi.assistant"]);
    let Some(Message::Assistant(converted)) =
        entries[1].model.as_ref().and_then(|model| model.first())
    else {
        panic!("the converted entry holds an assistant message");
    };
    assert_eq!(converted.stop_reason, StopReason::Aborted);
    assert_eq!(
        text_of(Some(&Message::Assistant(converted.clone()))),
        Some(partial)
    );
    assert_eq!(live(&opened.harness, &opened).await, json("{}"));
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn resumes_a_retry_backoff_after_reopen() {
    let directory = temp();
    let path = sqlite_path(&directory);
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let now = manual_clock(&setup, 1_000.0);
    setup.faux.set_responses(vec![
        faux_assistant_message(
            Vec::<AssistantContentBlock>::new(),
            FauxAssistantMessageOptions {
                stop_reason: Some(StopReason::Error),
                error_message: Some("503 Service Unavailable".to_owned()),
                ..FauxAssistantMessageOptions::default()
            },
        )
        .into(),
        faux_assistant_message("recovered", FauxAssistantMessageOptions::default()).into(),
    ]);
    let mut opened = open(&path, &setup).await;
    opened.harness.resume().unwrap();
    setup.settings.update(|settings| {
        settings.retry = Some(PartialRetryPolicy {
            enabled: Some(true),
            max_retries: Some(2),
            base_delay_ms: Some(60_000.0),
            ..PartialRetryPolicy::default()
        });
    });
    let id = opened
        .root
        .submit(input("hi"), context())
        .await
        .unwrap()
        .id();
    wait_for(
        || async {
            live(&opened.harness, &opened).await["generation"]
                .get("retry")
                .is_some()
        },
        WAIT_MS,
    )
    .await;
    let task_id = run_task_id(&opened).await;
    opened.harness.close(context()).await.unwrap();

    opened = open(&path, &setup).await;
    assert_eq!(
        checkpoint(&opened.harness, task_id).await,
        Some(json(r#"{"phase":"retry","attempt":1,"until":61000}"#))
    );
    assert_eq!(
        live(&opened.harness, &opened).await,
        serde_json::json!({
            "run": { "taskId": task_id.get(), "inputs": [id.get()] },
            "generation": { "attempt": 1, "retry": { "at": 61_000, "error": "503 Service Unavailable" } },
        })
    );
    now.store(61_000.0_f64.to_bits(), Ordering::SeqCst);
    opened.harness.resume().unwrap();
    let handle = opened
        .harness
        .submission(id, context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(
        handle.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Done
    );
    assert_eq!(
        kinds(&all_entries(&opened.root, context()).await.unwrap()),
        ["pi.user", "pi.assistant", "pi.assistant"]
    );
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn resumes_polling_a_deferred_response_after_reopen() {
    let directory = temp();
    let path = sqlite_path(&directory);
    let setup = deferred_setup();
    let now = manual_clock(&setup, 1_000.0);
    setup.faux.set_responses(vec![faux_assistant_message(
        "deferred answer",
        FauxAssistantMessageOptions::default(),
    )
    .into()]);
    let mut opened = open(&path, &setup).await;
    opened.harness.resume().unwrap();
    deferred_stream(&setup);
    let id = opened
        .root
        .submit(input("hi"), context())
        .await
        .unwrap()
        .id();
    wait_deferred(&opened).await;
    let task_id = run_task_id(&opened).await;
    opened.harness.close(context()).await.unwrap();

    opened = open(&path, &setup).await;
    assert_match(
        &checkpoint(&opened.harness, task_id).await.unwrap(),
        &json(r#"{"phase":"poll","attempt":1,"pollAt":61000}"#),
    );
    now.store(61_000.0_f64.to_bits(), Ordering::SeqCst);
    opened.harness.resume().unwrap();
    let handle = opened
        .harness
        .submission(id, context())
        .await
        .unwrap()
        .unwrap();
    let settled = handle.wait(context()).await.unwrap();
    let answer_id = settled.state.answer().expect("a done input");
    let answer = opened
        .root
        .commit(
            move |tx| async move { tx.entry(answer_id).await },
            context(),
        )
        .await
        .unwrap();
    assert_eq!(
        text_of(
            answer
                .as_ref()
                .and_then(|entry| entry.model.as_ref())
                .and_then(|model| model.first())
        ),
        Some("deferred answer".to_owned())
    );
    assert_eq!(setup.faux.state().deferred_fetch_count, 1);
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn fails_no_model_when_the_pinned_model_is_gone_after_reopen_in_request_and_in_poll() {
    let directory = temp();
    let path = sqlite_path(&directory);
    let setup = deferred_setup();
    let busy = unanswered();
    setup.faux.set_responses(vec![
        busy.step.clone(),
        faux_assistant_message("deferred", FauxAssistantMessageOptions::default()).into(),
    ]);
    let mut opened = open(&path, &setup).await;
    opened.harness.resume().unwrap();
    let requesting = opened
        .root
        .submit(input("one"), context())
        .await
        .unwrap()
        .id();
    busy.reached().await;
    opened.harness.close(context()).await.unwrap();

    // Reopened without the faux provider: the request's pinned model is unknown.
    let empty = setup.with_models(create_models());
    let no_model = |settled: &crate::harness::types::SettledSubmissionRecord| {
        (
            settled.state.status(),
            settled.state.reason().map(str::to_owned),
        )
    };
    opened = open(&path, &empty).await;
    opened.harness.resume().unwrap();
    let handle = opened
        .harness
        .submission(requesting, context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(
        no_model(&handle.wait(context()).await.unwrap()),
        (SubmissionStatus::Unanswered, Some("no_model".to_owned()))
    );
    opened.harness.close(context()).await.unwrap();

    opened = open(&path, &setup).await;
    deferred_stream(&setup);
    opened.harness.resume().unwrap();
    let polling = opened
        .root
        .submit(input("two"), context())
        .await
        .unwrap()
        .id();
    wait_deferred(&opened).await;
    opened.harness.close(context()).await.unwrap();

    opened = open(&path, &empty).await;
    opened.harness.resume().unwrap();
    let handle = opened
        .harness
        .submission(polling, context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(
        no_model(&handle.wait(context()).await.unwrap()),
        (SubmissionStatus::Unanswered, Some("no_model".to_owned()))
    );
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn runs_a_print_style_turn_and_reads_the_durable_answer_after_reopen() {
    let directory = temp();
    let path = sqlite_path(&directory);
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_section(
        &setup.registry,
        "preamble",
        |_, _| async { Ok(Some("You are terse.".to_owned())) }.boxed(),
        Some(false),
        None,
    )
    .unwrap();
    setup.faux.set_responses(vec![faux_assistant_message(
        "42",
        FauxAssistantMessageOptions::default(),
    )
    .into()]);
    let mut opened = open(&path, &setup).await;
    opened.harness.resume().unwrap();
    let submission = opened
        .root
        .submit(input("answer?"), context())
        .await
        .unwrap();
    let settled = submission.wait(context()).await.unwrap();
    let answer_id = settled.state.answer().expect("a done input");
    let read = move |chat: &OpenChat| {
        chat.root.commit(
            move |tx| async move { tx.entry(answer_id).await },
            context(),
        )
    };
    let answer = read(&opened).await.unwrap();
    assert_eq!(
        text_of(
            answer
                .as_ref()
                .and_then(|entry| entry.model.as_ref())
                .and_then(|model| model.first())
        ),
        Some("42".to_owned())
    );
    opened.harness.close(context()).await.unwrap();

    opened = open(&path, &setup).await;
    let handle = opened
        .harness
        .submission(submission.id(), context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(handle.status(context()).await.unwrap(), *settled.record());
    assert_eq!(read(&opened).await.unwrap(), answer);
    opened.harness.close(context()).await.unwrap();
}
