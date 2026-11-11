//! Port of `test/harness-tools.test.ts` `describe("generation hooks")`.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_text, FauxAssistantMessageOptions, FauxDeferredOptions,
    FauxModelDefinition, FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_ai::types::DeferredRequest;
use eukhe_chord::json::{from_json, JsonValue};
use eukhe_types::pi_ai::{
    AssistantMessage, Message, StopReason, TextContent, UserContent, UserContentBlock, UserMessage,
};
use futures::FutureExt;

use super::support::{calls, done, empty_content, run, run_with, submit_and_wait, tool, Prepare};
use crate::harness::live::LIVE_DOC;
use crate::harness::tests::chat_support::{all_entries, chat_setup, text_of, ChatSetup};
use crate::harness::tests::support::{add_hooks, add_tool, context, generation_task, tool_task};
use crate::harness::types::{
    ConversationStreamOptions, GenerationHooks, RequestMessages, ToolHooks, YieldContinuation,
};
use crate::harness::Harness;
use crate::types::{ConversationId, EntryDraft, SubmissionId, SubmissionStatus};

fn lock<T>(mutex: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

fn answer(text: &str) -> AssistantMessage {
    faux_assistant_message(
        vec![faux_text(text)],
        FauxAssistantMessageOptions::default(),
    )
}

fn role(message: &Message) -> &'static str {
    match message {
        Message::System(_) => "system",
        Message::User(_) => "user",
        Message::Assistant(_) => "assistant",
        Message::ToolResult(_) => "toolResult",
    }
}

fn continuation(text: &str) -> YieldContinuation {
    YieldContinuation {
        r#continue: UserContent::Text(text.to_owned()),
        origin: eukhe_types::input_origin::InputOrigin::User,
    }
}

fn kinds(entries: &[crate::types::EntryRecord]) -> Vec<&str> {
    entries.iter().map(|entry| entry.kind.as_str()).collect()
}

#[tokio::test]
async fn replaces_request_messages_observes_responses_and_continues_on_yield() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let requests: Arc<Mutex<Vec<Vec<String>>>> = Arc::default();
    let recorded = Arc::clone(&requests);
    let record = FauxResponseStep::factory(move |request, _, _, _| {
        let mut requests = lock(&recorded);
        requests.push(
            request
                .messages()
                .iter()
                .map(|message| {
                    format!(
                        "{}:{}",
                        role(message),
                        text_of(Some(message)).unwrap_or_default()
                    )
                })
                .collect(),
        );
        Ok(answer(&format!("answer {}", requests.len())))
    });
    add_hooks(
        &setup.registry,
        generation_task(),
        GenerationHooks {
            before_request: Some(Arc::new(|request: &RequestMessages, _, _| {
                let mut messages = request.messages.clone();
                messages.push(Message::User(UserMessage {
                    content: UserContent::Text("injected".to_owned()),
                    timestamp: 0,
                }));
                let force_tool = request.force_tool.clone();
                async move {
                    Ok(Some(RequestMessages {
                        messages,
                        force_tool,
                    }))
                }
                .boxed()
            })),
            ..GenerationHooks::default()
        },
        None,
    )
    .unwrap();
    let responses: Arc<Mutex<Vec<String>>> = Arc::default();
    let observed = Arc::clone(&responses);
    add_hooks(
        &setup.registry,
        generation_task(),
        GenerationHooks {
            after_response: Some(Arc::new(move |message, _, _| {
                lock(&observed)
                    .push(text_of(Some(&Message::Assistant(message.clone()))).unwrap_or_default());
                async { Ok(()) }.boxed()
            })),
            ..GenerationHooks::default()
        },
        None,
    )
    .unwrap();
    let yields = Arc::new(AtomicUsize::new(0));
    add_hooks(
        &setup.registry,
        generation_task(),
        GenerationHooks {
            on_yield: Some(Arc::new(move |_, _, _| {
                let first = yields.fetch_add(1, Ordering::SeqCst) == 0;
                async move {
                    Ok(first.then(|| YieldContinuation {
                        r#continue: UserContent::Blocks(vec![UserContentBlock::Text(
                            TextContent::new("keep going"),
                        )]),
                        origin: eukhe_types::input_origin::InputOrigin::User,
                    }))
                }
                .boxed()
            })),
            ..GenerationHooks::default()
        },
        None,
    )
    .unwrap();
    let ran = run(&setup, vec![record.clone(), record]).await;
    assert_eq!(ran.status, SubmissionStatus::Done);
    let first = lock(&requests)[0].clone();
    assert_eq!(
        first[first.len() - 2..],
        ["user:go".to_owned(), "user:injected".to_owned()]
    );
    assert_eq!(*lock(&responses), ["answer 1", "answer 2"]);
    assert_eq!(
        kinds(&ran.entries),
        ["pi.user", "pi.assistant", "pi.user", "pi.assistant"]
    );
    // The injected message was used for the request only.
    assert!(!ran.entries.iter().any(|entry| {
        text_of(entry.model.as_ref().and_then(|model| model.first())).as_deref() == Some("injected")
    }));
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn keeps_the_runs_input_open_across_an_on_yield_continuation_and_answers_it_with_the_final_answer(
) {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let yields = Arc::new(AtomicUsize::new(0));
    let opened: Arc<Mutex<Option<(Harness, ConversationId)>>> = Arc::default();
    let input: Arc<Mutex<Option<SubmissionId>>> = Arc::default();
    let status_at_second_request: Arc<Mutex<Option<SubmissionStatus>>> = Arc::default();
    add_hooks(
        &setup.registry,
        generation_task(),
        GenerationHooks {
            on_yield: Some(Arc::new(move |_, _, _| {
                let first = yields.fetch_add(1, Ordering::SeqCst) == 0;
                async move { Ok(first.then(|| continuation("again"))) }.boxed()
            })),
            ..GenerationHooks::default()
        },
        None,
    )
    .unwrap();
    let (reader, seen_input, seen_status) = (
        Arc::clone(&opened),
        Arc::clone(&input),
        Arc::clone(&status_at_second_request),
    );
    let second = FauxResponseStep::Factory(Arc::new(move |_, _, _, _| {
        let (harness, id) = lock(&reader).clone().expect("the harness is open");
        let (seen_input, seen_status) = (Arc::clone(&seen_input), Arc::clone(&seen_status));
        async move {
            let live = harness
                .snapshot(&LIVE_DOC, id, context())
                .await
                .unwrap()
                .unwrap();
            let first: SubmissionId = from_json(&live.get("run").unwrap()["inputs"][0]).unwrap();
            *lock(&seen_input) = Some(first);
            let handle = harness.submission(first, context()).await.unwrap().unwrap();
            *lock(&seen_status) = Some(handle.status(context()).await.unwrap().state.status());
            Ok(answer("second"))
        }
        .boxed()
    }));
    let keep = Arc::clone(&opened);
    let prepare: Prepare = Box::new(move |harness, root| {
        *lock(&keep) = Some((harness, root.id()));
        async {}.boxed()
    });
    let ran = run_with(
        &setup,
        vec![answer("first").into(), second],
        Some(prepare),
        None,
    )
    .await;
    assert_eq!(
        *lock(&status_at_second_request),
        Some(SubmissionStatus::Placed)
    );
    let answers: Vec<_> = ran
        .entries
        .iter()
        .filter(|entry| entry.kind == "pi.assistant")
        .collect();
    let id = lock(&input).expect("the second request read the run's input");
    let record = ran
        .harness
        .submission(id, context())
        .await
        .unwrap()
        .unwrap()
        .status(context())
        .await
        .unwrap();
    assert_eq!(
        (record.state.status(), record.state.answer()),
        (SubmissionStatus::Done, Some(answers[1].id))
    );
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn observes_responses_that_arrive_by_polling_a_deferred_request() {
    let setup = chat_setup(RegisterFauxProviderOptions {
        deferred: Some(FauxDeferredOptions {
            pending_fetches: Some(1.0),
            poll_after_ms: Some(1.0),
        }),
        ..RegisterFauxProviderOptions::default()
    });
    let observed: Arc<Mutex<Vec<String>>> = Arc::default();
    let sink = Arc::clone(&observed);
    add_hooks(
        &setup.registry,
        generation_task(),
        GenerationHooks {
            after_response: Some(Arc::new(move |message, _, _| {
                let reason = serde_json::to_value(message.stop_reason).unwrap();
                lock(&sink).push(format!(
                    "{}:{}",
                    reason.as_str().unwrap(),
                    text_of(Some(&Message::Assistant(message.clone()))).unwrap_or_default()
                ));
                async { Ok(()) }.boxed()
            })),
            ..GenerationHooks::default()
        },
        None,
    )
    .unwrap();
    setup.settings.update(|settings| {
        settings.stream = Some(ConversationStreamOptions {
            deferred: Some(DeferredRequest::Flag(true)),
            ..ConversationStreamOptions::default()
        });
    });
    let ran = run(&setup, vec![answer("late").into()]).await;
    assert_eq!(ran.status, SubmissionStatus::Done);
    // The still-deferred results are not terminal.
    assert_eq!(*lock(&observed), ["stop:late"]);
    ran.harness.close(context()).await.unwrap();
}

/// Install one generation hook set in its own extension.
fn install(setup: &crate::harness::tests::chat_support::ChatSetup, hooks: GenerationHooks) {
    add_hooks(&setup.registry, generation_task(), hooks, None).unwrap();
}

#[tokio::test]
async fn lets_the_first_on_yield_continuation_win_and_reports_throws_without_stopping_later_handlers(
) {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let called: Arc<Mutex<Vec<&'static str>>> = Arc::default();
    let throwing = Arc::clone(&called);
    install(
        &setup,
        GenerationHooks {
            after_response: Some(Arc::new(move |_, _, _| {
                lock(&throwing).push("throwing observer");
                async { Err(crate::session::SessionError::error("observer failed")) }.boxed()
            })),
            ..GenerationHooks::default()
        },
    );
    let next = Arc::clone(&called);
    install(
        &setup,
        GenerationHooks {
            after_response: Some(Arc::new(move |_, _, _| {
                lock(&next).push("next observer");
                async { Ok(()) }.boxed()
            })),
            ..GenerationHooks::default()
        },
    );
    let yields = Arc::new(AtomicUsize::new(0));
    install(
        &setup,
        GenerationHooks {
            on_yield: Some(Arc::new(move |_, _, _| {
                let first = yields.fetch_add(1, Ordering::SeqCst) == 0;
                async move { Ok(first.then(|| continuation("first"))) }.boxed()
            })),
            ..GenerationHooks::default()
        },
    );
    let second = Arc::clone(&called);
    install(
        &setup,
        GenerationHooks {
            on_yield: Some(Arc::new(move |_, _, _| {
                let mut called = lock(&second);
                called.push("second onYield");
                let once = called
                    .iter()
                    .filter(|name| **name == "second onYield")
                    .count()
                    == 1;
                async move { Ok(once.then(|| continuation("second"))) }.boxed()
            })),
            ..GenerationHooks::default()
        },
    );
    let ran = run(
        &setup,
        vec![answer("a").into(), answer("b").into(), answer("c").into()],
    )
    .await;
    // The first continuation skips the second handler; on the next answer the second handler's continuation wins.
    let users: Vec<Option<String>> = ran
        .entries
        .iter()
        .filter(|entry| entry.kind == "pi.user")
        .map(|entry| text_of(entry.model.as_ref().and_then(|model| model.first())))
        .collect();
    assert_eq!(
        users,
        [
            Some("go".to_owned()),
            Some("first".to_owned()),
            Some("second".to_owned())
        ]
    );
    let called = lock(&called).clone();
    assert_eq!(
        called
            .iter()
            .filter(|name| **name == "second onYield")
            .count(),
        2
    );
    assert_eq!(
        called
            .iter()
            .filter(|name| **name == "next observer")
            .count(),
        3
    );
    assert!(setup
        .reports()
        .iter()
        .any(|error| error.to_string() == "observer failed"));
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn keeps_durable_hook_decisions_in_task_memos() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let asked = Arc::new(AtomicUsize::new(0));
    let decisions: Arc<Mutex<Vec<(String, String)>>> = Arc::default();
    add_tool(
        &setup.registry,
        tool("echo", |_, _, _| async { Ok(empty_content()) }),
        None,
    )
    .unwrap();
    let (counter, sink) = (Arc::clone(&asked), Arc::clone(&decisions));
    add_hooks(
        &setup.registry,
        tool_task(),
        ToolHooks {
            before_tool: Some(Arc::new(move |_, api, cx| {
                counter.fetch_add(1, Ordering::SeqCst);
                let (api, cx, sink) = (api.clone(), cx.clone(), Arc::clone(&sink));
                async move {
                    let decision: String = api
                        .memo_or("approval:decision", &"approved".to_owned(), &cx)
                        .await?;
                    let again: String = api
                        .memo_or("approval:decision", &"denied".to_owned(), &cx)
                        .await?;
                    lock(&sink).push((decision, again));
                    Ok(None)
                }
                .boxed()
            })),
            ..ToolHooks::default()
        },
        None,
    )
    .unwrap();
    let ran = run(
        &setup,
        vec![
            calls(&[("echo", serde_json::json!({}), "c1")]).into(),
            done().into(),
        ],
    )
    .await;
    assert_eq!(asked.load(Ordering::SeqCst), 1);
    assert_eq!(
        *lock(&decisions),
        [("approved".to_owned(), "approved".to_owned())]
    );
    ran.harness.close(context()).await.unwrap();
}

/// The rows of a session whose `on_truncated` handler writes a
/// `test.warning` row with the warning, after a reply cut at the output
/// limit with text, then a whole answer to a second input: each entry's
/// kind, and the warning a `test.warning` row holds.
async fn rows_after_a_truncated_reply(setup: &ChatSetup) -> Vec<(String, Option<JsonValue>)> {
    add_hooks(
        &setup.registry,
        generation_task(),
        GenerationHooks {
            on_truncated: Some(Arc::new(|warning, _, _| {
                let row = EntryDraft {
                    data: Some(JsonValue::from(warning.to_owned())),
                    ..EntryDraft::new("test.warning")
                };
                async move { Ok(Some(row)) }.boxed()
            })),
            ..GenerationHooks::default()
        },
        None,
    )
    .unwrap();
    let truncated: AssistantMessage = faux_assistant_message(
        vec![faux_text("Here is the whole plan: first")],
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::Length),
            ..FauxAssistantMessageOptions::default()
        },
    );
    let ran = run(setup, vec![truncated.into(), answer("whole").into()]).await;
    submit_and_wait(&ran.root, "more").await;
    let rows = all_entries(&ran.root, context())
        .await
        .unwrap()
        .into_iter()
        .map(|entry| {
            let warning = (entry.kind == "test.warning")
                .then_some(entry.data)
                .flatten();
            (entry.kind, warning)
        })
        .collect();
    ran.harness.close(context()).await.unwrap();
    rows
}

/// The warning of a kept truncated answer. The stop walk keeps a reply
/// that hit the output limit with text and room left in the window
/// (laws/stop/cut.bend). The harness writes the warning and asks each
/// `on_truncated` handler for the row that shows it; the row follows the
/// answer in the transcript. A whole answer asks no handler.
#[tokio::test]
async fn appends_the_on_truncated_row_after_a_kept_truncated_answer() {
    let rows =
        rows_after_a_truncated_reply(&chat_setup(RegisterFauxProviderOptions::default())).await;
    let warning = JsonValue::from(
        "Response hit the faux/faux-1 output limit (8 tokens) and was truncated.".to_owned(),
    );
    assert_eq!(
        rows,
        [
            ("pi.user".to_owned(), None),
            ("pi.assistant".to_owned(), None),
            ("test.warning".to_owned(), Some(warning)),
            ("pi.user".to_owned(), None),
            ("pi.assistant".to_owned(), None),
        ]
    );
}

/// A truncated reply the stop walk drops (text in a window that is
/// unknown, 0, which counts as run out, with nothing to compact:
/// laws/stop/cut.bend) gets no warning: such a turn leaves the model's
/// context with no notice. No `on_truncated` handler is asked; the
/// `pi.drop` entry that takes the reply out of the model's context follows
/// it.
#[tokio::test]
async fn asks_no_on_truncated_row_for_a_dropped_truncated_reply() {
    let rows = rows_after_a_truncated_reply(&chat_setup(RegisterFauxProviderOptions {
        models: Some(vec![FauxModelDefinition {
            context_window: Some(0),
            ..FauxModelDefinition::new("faux-1")
        }]),
        ..RegisterFauxProviderOptions::default()
    }))
    .await;
    assert_eq!(
        rows,
        [
            ("pi.user".to_owned(), None),
            ("pi.assistant".to_owned(), None),
            ("pi.drop".to_owned(), None),
            ("pi.user".to_owned(), None),
            ("pi.assistant".to_owned(), None),
        ]
    );
}
