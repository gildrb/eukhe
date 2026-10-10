//! "compaction estimates and interactions" and "compaction events and live
//! status".

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::json::{to_json, JsonValue};
use eukhe_pi_ai::providers::faux::faux_tool_call;
use eukhe_types::pi_ai::{
    JsonObject as PiJsonObject, Message, StopReason, TextContent, UserContentBlock,
};
use futures::FutureExt;

use super::automatic::{event_kinds, record_events};
use super::{
    answer, compact, compaction_tasks, failure, first_user_text, gated, history, kinds, live, open,
    result, submission, submission_id, submit, summary, text, tool_with, turn, user_text,
    window_setup, with_stop, Chat, OpenOptions, BACKGROUND, MANUAL,
};
use crate::harness::events::{watch_events, AgentEvent};
use crate::harness::live::{CompactionStatus, LiveRetry};
use crate::harness::tests::chat_support::{all_entries, tools_named, wait_for};
use crate::harness::tests::support::{
    add_hooks, add_section, add_task, add_tool, compaction_task, context,
};
use crate::harness::tests::task_support::{deferred, Deferred};
use crate::harness::types::{
    AgentChange, CompactionHooks, CompactionPolicy, CompactionReason, CompactionResult,
    ConversationAbortOptions, ConversationCreateOptions, FieldChange, ToolsChange,
    WriteSubmissionDraft,
};
use crate::session::SessionResult;
use crate::tasks::{define_task, NextTaskState, Task, TaskDefinition};
use crate::types::{
    ContextEdit, ContextEditAction, ConversationOwnership, EntryDraft, SubmissionStatus, TaskId,
    TaskOptions, TaskOutcome, TaskOwnership, TaskState,
};

fn task_id(id: TaskId) -> TaskId<CompactionResult> {
    TaskId::from_number(id.get())
}

fn user(content: &str) -> Message {
    Message::User(eukhe_types::pi_ai::UserMessage {
        content: eukhe_types::pi_ai::UserContent::Text(content.to_owned()),
        timestamp: 0,
    })
}

fn configure_tools(names: &[&str], chat: &Chat) -> AgentChange {
    AgentChange {
        tools: FieldChange::Set(ToolsChange::Exactly(tools_named(&chat.setup, names))),
        ..AgentChange::default()
    }
}

async fn ignores_usage_measured_before_a_summary_placed_mid_run(fixed_clock: bool) {
    let setup = window_setup(2000);
    if fixed_clock {
        setup.set_now(|| 1_000.0);
    }
    let chat = open(OpenOptions {
        context_window: Some(2000),
        setup: Some(setup),
        ..OpenOptions::default()
    })
    .await;
    let tool_gate = deferred();
    let tool_reached = deferred();
    let (gate, reach) = (tool_gate.clone(), tool_reached.clone());
    add_tool(
        &chat.setup.registry,
        tool_with("slow", move || {
            let (gate, reach) = (gate.clone(), reach.clone());
            async move {
                reach.resolve(());
                gate.wait().await;
                vec![UserContentBlock::Text(TextContent::new(text(
                    "result", 200,
                )))]
            }
        }),
        None,
    )
    .unwrap();
    chat.root
        .configure(configure_tools(&["slow"], &chat), context())
        .await
        .unwrap();
    turn(&chat, &text("u1", 220), &text("a1", 220)).await;
    turn(&chat, &text("u2", 220), &text("a2", 220)).await;
    turn(&chat, &text("u3", 220), &text("a3", 220)).await;
    // Background at 900, blocking at 1500: the tool call's usage plus its
    // result would cross 1500.
    chat.set_policy(CompactionPolicy {
        background_tokens: 600.0,
        ..BACKGROUND
    });
    // The request starts a background compaction; its tool call's usage
    // measures the whole context.
    chat.faux.agent(with_stop(
        vec![faux_tool_call("slow", PiJsonObject::new(), None)],
        StopReason::ToolUse,
    ));
    chat.faux.agent(answer("done"));
    let summary_gate = deferred();
    let summary_reached = deferred();
    chat.faux.summary(gated(
        &summary_gate,
        summary("SUMMARY"),
        Some(&summary_reached),
    ));
    let input = submit(&chat, &text("u4", 50)).await;
    tool_reached.wait().await;
    summary_reached.wait().await;
    let background = compaction_tasks(&chat).await.remove(0);
    summary_gate.resolve(());
    // Queued: the run is busy in its tool round.
    let queued = result(&chat, task_id(background.id)).await;
    let id = submission_id(&queued);
    assert_eq!(
        submission(&chat, id)
            .await
            .status(context())
            .await
            .unwrap()
            .state
            .status(),
        SubmissionStatus::Queued
    );
    tool_gate.resolve(());
    assert_eq!(
        input.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Done
    );
    // The summary landed at postTools; the successor saw a small context and
    // did not compact again.
    assert_eq!(chat.faux.summary_requests().len(), 1);
    assert!(compaction_tasks(&chat).await.is_empty());
    assert!(first_user_text(&chat.faux.last_agent_messages()).contains("SUMMARY"));
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn ignores_usage_measured_before_a_summary_placed_mid_run_real_clock() {
    ignores_usage_measured_before_a_summary_placed_mid_run(false).await;
}

#[tokio::test]
async fn ignores_usage_measured_before_a_summary_placed_mid_run_fixed_clock() {
    ignores_usage_measured_before_a_summary_placed_mid_run(true).await;
}

fn system_section(message: &Message, key: &str) -> Option<String> {
    match message {
        Message::System(system) => system
            .sections
            .as_ref()
            .and_then(|sections| sections.get(key).cloned().flatten()),
        Message::User(_) | Message::Assistant(_) | Message::ToolResult(_) => None,
    }
}

#[tokio::test]
async fn rebaselines_the_system_prompt_over_kept_system_deltas() {
    let chat = open(OpenOptions::default()).await;
    let mood = Arc::new(Mutex::new("cheerful".to_owned()));
    let current = Arc::clone(&mood);
    add_section(
        &chat.setup.registry,
        "mood",
        move |_, _| {
            let value = current
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .clone();
            async move { Ok(Some(value)) }.boxed()
        },
        Some(false),
        None,
    )
    .unwrap();
    turn(&chat, &text("u1", 100), &text("a1", 100)).await;
    turn(&chat, &text("u2", 100), &text("a2", 100)).await;
    *mood.lock().unwrap_or_else(PoisonError::into_inner) = "terse".to_owned();
    turn(&chat, &text("u3", 100), &text("a3", 100)).await;
    chat.set_policy(CompactionPolicy {
        keep_recent_tokens: 250.0,
        ..MANUAL
    });
    chat.faux.summary(summary("SUMMARY"));
    result(&chat, compact(&chat, None).await).await;
    // The kept range holds the delta for the terse mood; the next request has
    // one complete baseline.
    assert!(chat
        .root
        .context(context(), crate::harness::types::ContextOptions::default())
        .await
        .unwrap()
        .entries
        .iter()
        .any(|record| record.kind == "pi.system"));
    turn(&chat, "next", "ok").await;
    let systems: Vec<Message> = chat
        .faux
        .last_agent_messages()
        .into_iter()
        .filter(|message| matches!(message, Message::System(_)))
        .collect();
    assert_eq!(systems.len(), 1);
    assert_eq!(
        system_section(&systems[0], "preamble").as_deref(),
        Some("You are helpful.")
    );
    assert_eq!(
        system_section(&systems[0], "mood").as_deref(),
        Some("terse")
    );
    chat.harness.close(context()).await.unwrap();
}

fn replace(target: crate::types::EntryId, content: &str) -> EntryDraft {
    EntryDraft {
        edits: Some(vec![ContextEdit {
            target,
            action: ContextEditAction::Replace {
                messages: vec![user(content)],
            },
        }]),
        ..EntryDraft::new("app.redact")
    }
}

#[tokio::test]
async fn summarizes_a_replaced_entrys_replacement_and_shows_it_to_the_hook() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    let u1 = all_entries(&chat.root, context()).await.unwrap()[0].id;
    chat.root
        .submit(
            WriteSubmissionDraft {
                request_id: None,
                entry: replace(u1, "REDACTED"),
            },
            context(),
        )
        .await
        .unwrap();
    let messages: Arc<Mutex<Vec<Message>>> = Arc::default();
    let sink = Arc::clone(&messages);
    add_hooks(
        &chat.setup.registry,
        compaction_task(),
        CompactionHooks {
            before_compact: Some(Arc::new(move |compaction, _, _| {
                *sink.lock().unwrap_or_else(PoisonError::into_inner) = compaction.messages.clone();
                futures::future::ready(Ok(None)).boxed()
            })),
        },
        None,
    )
    .unwrap();
    chat.faux.summary(summary("SUMMARY"));
    result(&chat, compact(&chat, None).await).await;
    let seen = messages
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    assert_eq!(first_user_text(&seen), "REDACTED");
    assert!(user_text(chat.faux.summary_requests()[0].messages.get(1)).contains("[User]: REDACTED"));
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn compacts_a_fork_whose_cut_falls_on_a_parent_entry() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    let entries = all_entries(&chat.root, context()).await.unwrap();
    let fork = chat
        .root
        .fork(
            entries.last().unwrap().id,
            ConversationCreateOptions::new(ConversationOwnership::Ownerless),
            context(),
        )
        .await
        .unwrap();
    chat.faux.summary(summary("SUMMARY"));
    let outcome = result(&chat, fork.compact(None, context()).await.unwrap()).await;
    assert_eq!(
        submission(&chat, submission_id(&outcome))
            .await
            .wait(context())
            .await
            .unwrap()
            .state
            .status(),
        SubmissionStatus::Done
    );
    let u3 = entries
        .iter()
        .find(|record| {
            user_text(record.model.as_ref().and_then(|model| model.first())).starts_with("u3")
        })
        .unwrap();
    let view = fork
        .context(context(), crate::harness::types::ContextOptions::default())
        .await
        .unwrap();
    let head = view.head.as_ref().unwrap();
    assert_eq!(head.kind, "pi.compaction");
    assert_eq!(head.head, Some(u3.id));
    assert_eq!(head.conversation_id, fork.id());
    assert_eq!(
        view.messages[1..]
            .iter()
            .map(|message| user_text(Some(message)))
            .collect::<Vec<_>>(),
        [text("u3", 100), text("a3", 100)]
    );
    // The parent is untouched.
    assert!(!kinds(&chat.root)
        .await
        .iter()
        .any(|kind| kind == "pi.compaction"));
    // The fork's view keeps the parent entries the summary kept.
    let state = fork.view_state(context()).await.unwrap();
    assert_eq!(state.value()["entries"], to_json(&view.entries).unwrap());
    state.dispose().unwrap();
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn settles_stale_in_a_fork_reset_while_it_summarizes() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    let entries = all_entries(&chat.root, context()).await.unwrap();
    let fork = chat
        .root
        .fork(
            entries.last().unwrap().id,
            ConversationCreateOptions::new(ConversationOwnership::Ownerless),
            context(),
        )
        .await
        .unwrap();
    let gate = deferred();
    let reached = deferred();
    chat.faux
        .summary(gated(&gate, summary("SUMMARY"), Some(&reached)));
    let id = fork.compact(None, context()).await.unwrap();
    reached.wait().await;
    fork.reset(None, context()).await.unwrap();
    gate.resolve(());
    let outcome = result(&chat, id).await;
    let record = submission(&chat, submission_id(&outcome))
        .await
        .status(context())
        .await
        .unwrap();
    assert_eq!(record.state.status(), SubmissionStatus::Unanswered);
    assert_eq!(record.state.reason(), Some("stale"));
    assert_eq!(
        fork.context(context(), crate::harness::types::ContextOptions::default())
            .await
            .unwrap()
            .head
            .map(|head| head.kind),
        Some("pi.reset".to_owned())
    );
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn places_an_older_queued_summary_and_the_current_one_together_when_idle_admission_drains_the_inbox(
) {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    let gate = deferred();
    let reached = deferred();
    chat.faux
        .agent(gated(&gate, failure("bad request"), Some(&reached)));
    let failed = submit(&chat, "fails").await;
    reached.wait().await;
    chat.faux.summary(summary("OLDER"));
    let older = result(&chat, compact(&chat, None).await).await;
    gate.resolve(());
    failed.wait(context()).await.unwrap();
    // Idle now, with the older summary still queued; the current one queues
    // behind it and a final boundary runs.
    chat.faux.summary(summary("CURRENT"));
    let current = result(&chat, compact(&chat, None).await).await;
    let mut statuses = Vec::new();
    for outcome in [older, current] {
        statuses.push(
            submission(&chat, submission_id(&outcome))
                .await
                .status(context())
                .await
                .unwrap()
                .state
                .status(),
        );
    }
    assert_eq!(statuses, [SubmissionStatus::Done, SubmissionStatus::Done]);
    let messages = chat
        .root
        .context(context(), crate::harness::types::ContextOptions::default())
        .await
        .unwrap()
        .messages;
    assert!(first_user_text(&messages).contains("CURRENT"));
    chat.harness.close(context()).await.unwrap();
}

type ChildTask = Task<JsonValue, JsonValue, JsonValue, ()>;

fn define_child_task(gate: &Deferred) -> ChildTask {
    let gate = gate.clone();
    define_task(
        TaskDefinition::new(
            "test.child",
            1,
            |_: &JsonValue| Ok(JsonValue::parse(r#"{"phase":"run"}"#).unwrap()),
            |_, runtime: crate::tasks::TaskRuntime<JsonValue, JsonValue, JsonValue, ()>, cx| async move {
                runtime
                    .commit(
                        |_, _| async {
                            Ok(Some(NextTaskState::Terminal {
                                outcome: TaskOutcome::Aborted {
                                    reason: None,
                                    result: None,
                                },
                            }))
                        },
                        &cx,
                    )
                    .await
            },
        )
        .phase("run", move |_, runtime, cx| {
            let gate = gate.wait();
            async move {
                gate.await;
                runtime
                    .commit(
                        |_, _| async {
                            Ok(Some(NextTaskState::Terminal {
                                outcome: TaskOutcome::Completed {
                                    result: JsonValue::Null,
                                },
                            }))
                        },
                        &cx,
                    )
                    .await
            }
        }),
    )
}

#[tokio::test]
async fn places_a_hooks_summary_and_holds_while_work_the_hook_created_runs() {
    let chat = open(OpenOptions::default()).await;
    let child_gate = deferred();
    let child = define_child_task(&child_gate);
    add_task(&chat.setup.registry, child.erase(), None).unwrap();
    let (harness, root_id) = (chat.harness.clone(), chat.id());
    add_hooks(
        &chat.setup.registry,
        compaction_task(),
        CompactionHooks {
            before_compact: Some(Arc::new(move |_, api, hook_context| {
                let (harness, child, owner) = (harness.clone(), child.clone(), api.task_id());
                let hook_context = hook_context.clone();
                async move {
                    harness
                        .commit(
                            move |tx| async move {
                                tx.create_task(
                                    child.erase().as_definition_ref(),
                                    JsonValue::object(),
                                    TaskOptions {
                                        ownership: TaskOwnership::Task { task_id: owner },
                                        conversation_id: Some(root_id),
                                        background: None,
                                        abandon_on_restart: None,
                                    },
                                )
                                .await?;
                                SessionResult::Ok(())
                            },
                            &hook_context,
                        )
                        .await?;
                    Ok(Some(crate::harness::types::CompactionDecision::Summary(
                        "HOOK".to_owned(),
                    )))
                }
                .boxed()
            })),
        },
        None,
    )
    .unwrap();
    history(&chat).await;
    let id = compact(&chat, None).await;
    wait_for(
        || {
            let task = chat.harness.get_task(id, context());
            async move {
                task.await
                    .unwrap()
                    .is_some_and(|record| matches!(record.state, TaskState::Completing { .. }))
            }
        },
        5000,
    )
    .await;
    // The summary and the status removal landed at the hold.
    assert_eq!(kinds(&chat.root).await.last().unwrap(), "pi.compaction");
    assert_eq!(live(&chat).await.compactions, None);
    child_gate.resolve(());
    assert!(matches!(
        result(&chat, id).await,
        TaskOutcome::Completed { .. }
    ));
    chat.harness.close(context()).await.unwrap();
}

/// A policy whose negative `reserveTokens` pins a negative `maxTokens`, which
/// the summarize phase rejects (see `request_max_tokens`) before any request.
pub(super) fn faulting(policy: CompactionPolicy) -> CompactionPolicy {
    CompactionPolicy {
        reserve_tokens: -1000.0,
        ..policy
    }
}

// TS replaces `models.getModel` with a throwing function. Rust `Models`
// cannot throw there; the closest observable fault is an uncaught phase
// error, here the summarize phase rejecting the negative `maxTokens` the
// selection pinned.
#[tokio::test]
async fn removes_the_status_of_a_faulted_compaction() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    chat.set_policy(faulting(MANUAL));
    let outcome = result(&chat, compact(&chat, None).await).await;
    let TaskOutcome::Faulted { error } = outcome else {
        panic!("faulted: {outcome:?}");
    };
    assert!(error.message.contains("is not a non-negative integer"));
    assert_eq!(live(&chat).await.compactions, None);
    chat.harness.close(context()).await.unwrap();
}

// ─── Events and live status ───────────────────────────────────────────────

#[tokio::test]
async fn reports_start_and_end_and_the_retry_backoff_in_a_late_joiners_snapshot() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    chat.set_retry(2, 60_000.0);
    let (stream, events) = record_events(&chat).await;
    chat.faux.summary(failure("overloaded"));
    let id = compact(&chat, None).await;
    wait_for(
        || async {
            live(&chat)
                .await
                .compactions
                .and_then(|list| list.first().cloned())
                .is_some_and(|status| status.retry.is_some())
        },
        5000,
    )
    .await;
    let late = watch_events(&chat.harness, chat.id(), context())
        .await
        .unwrap();
    let compactions = late.snapshot().compactions.clone();
    assert_eq!(compactions.len(), 1);
    let retry = compactions[0].retry.clone().unwrap();
    assert_eq!(
        compactions[0],
        CompactionStatus {
            task_id: id.erase(),
            reason: CompactionReason::Manual,
            blocking: false,
            attempt: 1,
            retry: Some(LiveRetry {
                at: retry.at,
                error: "overloaded".to_owned(),
            }),
        }
    );
    late.stop().await;
    chat.harness
        .abort_task(id.erase(), context())
        .await
        .unwrap();
    wait_for(
        || async { event_kinds(&events).contains(&"compaction_end") },
        5000,
    )
    .await;
    let compaction_events: Vec<AgentEvent> = events
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .iter()
        .filter(|event| event.kind().starts_with("compaction_"))
        .cloned()
        .collect();
    assert_eq!(
        compaction_events,
        [
            AgentEvent::CompactionStart {
                task_id: id.erase(),
                reason: CompactionReason::Manual,
                blocking: false,
            },
            AgentEvent::CompactionEnd {
                task_id: id.erase(),
                reason: CompactionReason::Manual,
            },
        ]
    );
    stream.stop().await;
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn lists_concurrent_compactions_in_task_id_order() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    let first = deferred();
    let second = deferred();
    chat.faux
        .summary(gated(&deferred(), summary("SUMMARY"), Some(&first)));
    chat.faux
        .summary(gated(&deferred(), summary("SUMMARY"), Some(&second)));
    let a = compact(&chat, None).await;
    let b = compact(&chat, None).await;
    first.wait().await;
    second.wait().await;
    assert_eq!(
        live(&chat)
            .await
            .compactions
            .unwrap()
            .iter()
            .map(|status| status.task_id)
            .collect::<Vec<_>>(),
        [a.erase(), b.erase()]
    );
    chat.root
        .abort(ConversationAbortOptions::default(), context())
        .await
        .unwrap();
    assert_eq!(live(&chat).await.compactions, None);
    chat.harness.close(context()).await.unwrap();
}
