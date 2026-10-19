//! The Director stack on a real Harness with faux models (the goal
//! extension's setup): the goal as a layer until it completes, the global
//! budget, a reminder, a forced tool call, the `directors.push` host
//! request, and the stack across a reopen and a fork.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_tool_call, FauxAssistantMessageOptions, FauxResponseStep,
};
use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::entries::ASSISTANT_ENTRY;
use eukhe_durable::harness::types::ConversationCreateOptions;
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::types::{ConversationOwnership, EntryRecord};
use eukhe_types::input_origin::{AutonomousNudge, InputOrigin};
use eukhe_types::pi_ai::{AssistantMessage, JsonObject, Message, StopReason, UserContent};
use serde_json::json;

use super::{
    director_state, push_director, DirectorLimits, DirectorState, End, Layer, LayerKind, RunLoop,
    DEFAULT_STALL_STEPS, DIRECTOR_NOTICE_CUSTOM_TYPE,
};
use crate::autonomous::AgentAutonomousConfig;
use crate::durable::entries::{CustomEntryData, CUSTOM_ENTRY};
use crate::durable::goals::tests::{
    answer, entries, finish_call, open_jsonl, setup, stored_goal, submit, user_origins, user_texts,
};
use crate::durable::goals::{autonomous_state, set_autonomous, AutonomousChange};
use crate::goals::{GoalContextKind, GoalStatus};

fn cx() -> &'static Context {
    &BACKGROUND_CONTEXT
}

/// The input of the stored loop (an opaque submission id), required.
fn loop_input(state: &DirectorState) -> Option<eukhe_durable::types::SubmissionId> {
    let input = state.run.as_ref().and_then(|run| run.input);
    assert!(input.is_some(), "the loop knows its run: {state:?}");
    input
}

fn assistant_ids(entries: &[EntryRecord]) -> Vec<eukhe_durable::types::EntryId> {
    entries
        .iter()
        .filter(|entry| entry.kind == ASSISTANT_ENTRY.kind())
        .map(|entry| entry.id)
        .collect()
}

#[tokio::test]
async fn a_goal_is_a_director_layer_and_hands_back_when_it_completes() {
    let setup = setup();
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    setup
        .host_request("goal.create", json!({ "objective": "ship it" }))
        .await
        .expect("goal.create succeeds");
    setup.faux.set_responses(vec![
        answer("step one"),
        answer("step two"),
        finish_call(),
        answer("done"),
    ]);

    submit(&root, "work").await;
    harness.wait_for_idle(cx()).await.expect("idle");

    let continuation = InputOrigin::Goal {
        context: GoalContextKind::Continuation,
    };
    assert_eq!(
        user_origins(&entries(&root).await),
        vec![InputOrigin::User, continuation.clone(), continuation]
    );
    assert_eq!(
        stored_goal(&harness, &root).await.status,
        GoalStatus::Complete
    );
    // Two continuations spent the goal layer and the loop; the completed
    // goal yielded, so the loop handed back.
    let state = director_state(&harness, root.id(), cx())
        .await
        .expect("read");
    let max = DirectorLimits::default().max_steps;
    assert_eq!(
        state,
        DirectorState {
            stack: vec![Layer {
                kind: LayerKind::Goal,
                budget: max - 2,
            }],
            run: Some(RunLoop {
                input: loop_input(&state),
                left: max - 2,
                end: Some(End::Hand),
            }),
        }
    );
    harness.close(cx()).await.expect("close");
}

#[tokio::test]
async fn the_global_budget_hands_back_whatever_the_layers_say() {
    let setup = setup();
    *setup.limits.lock().unwrap_or_else(PoisonError::into_inner) = DirectorLimits {
        stack_cap: 8,
        max_steps: 1,
        stall_steps: DEFAULT_STALL_STEPS,
    };
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    set_autonomous(
        &harness,
        root.id(),
        AutonomousChange::On(AgentAutonomousConfig {
            max_continuations: Some(3),
            ..AgentAutonomousConfig::default()
        }),
        cx(),
    )
    .await
    .expect("autonomous on");
    setup
        .faux
        .set_responses(vec![answer("a"), answer("b"), answer("unused")]);

    submit(&root, "go").await;
    harness.wait_for_idle(cx()).await.expect("idle");

    // The autonomous layer still had budget for the second continuation;
    // the loop's one step was spent.
    assert_eq!(
        user_origins(&entries(&root).await),
        vec![
            InputOrigin::User,
            InputOrigin::Autonomous {
                nudge: AutonomousNudge::Continuation,
            },
        ]
    );
    assert_eq!(setup.faux.get_pending_response_count(), 1);
    let state = director_state(&harness, root.id(), cx())
        .await
        .expect("read");
    assert_eq!(
        state,
        DirectorState {
            stack: vec![Layer {
                kind: LayerKind::Autonomous,
                budget: 1,
            }],
            run: Some(RunLoop {
                input: loop_input(&state),
                left: 0,
                end: Some(End::Hand),
            }),
        }
    );
    // The continuation the global budget refused was not charged.
    let autonomous = autonomous_state(&harness, root.id(), cx())
        .await
        .expect("read");
    assert_eq!(
        (autonomous.continuations_used, autonomous.last_stop),
        (1, None)
    );
    harness.close(cx()).await.expect("close");
}

#[tokio::test]
async fn a_reminder_leads_the_next_continuation_and_leaves() {
    let setup = setup();
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    setup
        .host_request("goal.create", json!({ "objective": "ship it" }))
        .await
        .expect("goal.create succeeds");
    let limits = DirectorLimits::default();
    for kind in [
        LayerKind::Goal,
        LayerKind::Reminder {
            text: "Run the tests first.".to_owned(),
        },
    ] {
        push_director(&harness, root.id(), Layer { kind, budget: 0 }, limits, cx())
            .await
            .expect("the layer fits");
    }
    setup
        .faux
        .set_responses(vec![answer("a"), finish_call(), answer("done")]);

    submit(&root, "work").await;
    harness.wait_for_idle(cx()).await.expect("idle");

    let texts = user_texts(&entries(&root).await);
    assert_eq!(texts.len(), 2, "{texts:?}");
    assert!(
        texts[1].starts_with("Run the tests first.\n\n[goal: continuation]"),
        "{texts:?}"
    );
    let state = director_state(&harness, root.id(), cx())
        .await
        .expect("read");
    assert_eq!(
        state,
        DirectorState {
            stack: vec![Layer {
                kind: LayerKind::Goal,
                budget: limits.max_steps - 1,
            }],
            run: Some(RunLoop {
                input: loop_input(&state),
                left: limits.max_steps - 1,
                end: Some(End::Hand),
            }),
        }
    );
    harness.close(cx()).await.expect("close");
}

/// The text of the last message of a request.
fn last_text(messages: &[Message]) -> String {
    match messages.last() {
        Some(Message::User(message)) => match &message.content {
            UserContent::Text(text) => text.clone(),
            UserContent::Blocks(_) => String::new(),
        },
        Some(Message::System(_) | Message::Assistant(_) | Message::ToolResult(_)) | None => {
            String::new()
        }
    }
}

/// Answer `message`, recording the last text the request sent.
fn recorded(seen: &Arc<Mutex<Vec<String>>>, message: AssistantMessage) -> FauxResponseStep {
    let seen = Arc::clone(seen);
    FauxResponseStep::factory(move |request, _, _, _| {
        seen.lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(last_text(request.messages()));
        Ok(message.clone())
    })
}

#[tokio::test]
async fn a_forced_tool_layer_forces_the_requests_until_the_model_calls_it() {
    let setup = setup();
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    push_director(
        &harness,
        root.id(),
        Layer {
            kind: LayerKind::ForceTool {
                tool: "finish".to_owned(),
                tries: 1,
                called: false,
                missed: 0,
            },
            budget: 1,
        },
        DirectorLimits::default(),
        cx(),
    )
    .await
    .expect("the layer fits");
    let seen = Arc::default();
    let call = faux_assistant_message(
        faux_tool_call("finish", JsonObject::new(), Some("call-finish".to_owned())),
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    );
    let text = |text: &str| faux_assistant_message(text, FauxAssistantMessageOptions::default());
    setup.faux.set_responses(vec![
        recorded(&seen, text("no call")),
        recorded(&seen, call),
        recorded(&seen, text("done")),
    ]);

    submit(&root, "go").await;
    harness.wait_for_idle(cx()).await.expect("idle");

    // The first reply missed the call, so the generation asked again (its
    // one try); once called, the next request went unforced, and the made
    // call left the stack at the final answer.
    let soft = "Call the `finish` tool now: your reply must include a call to `finish`.";
    assert_eq!(
        *seen.lock().unwrap_or_else(PoisonError::into_inner),
        vec![soft.to_owned(), soft.to_owned(), String::new()]
    );
    let state = director_state(&harness, root.id(), cx())
        .await
        .expect("read");
    assert_eq!(
        state,
        DirectorState {
            stack: Vec::new(),
            run: Some(RunLoop {
                input: loop_input(&state),
                left: DirectorLimits::default().max_steps,
                end: Some(End::Hand),
            }),
        }
    );
    harness.close(cx()).await.expect("close");
}

/// The display rows of the Director stack, oldest first.
fn director_notices(entries: Vec<EntryRecord>) -> Vec<CustomEntryData> {
    entries
        .into_iter()
        .filter_map(|entry| CUSTOM_ENTRY.narrow(entry).expect("eukhe.custom data"))
        .map(|entry| entry.data().clone())
        .filter(|data| data.custom_type == DIRECTOR_NOTICE_CUSTOM_TYPE)
        .collect()
}

#[tokio::test]
async fn a_forced_call_the_model_never_makes_fails_once_and_the_next_run_is_not_forced() {
    let setup = setup();
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    setup
        .host_request(
            "directors.push",
            json!({ "layer": "forceTool", "tool": "finish", "tries": 1 }),
        )
        .await
        .expect("directors.push succeeds");
    let seen = Arc::default();
    let text = |text: &str| faux_assistant_message(text, FauxAssistantMessageOptions::default());
    setup.faux.set_responses(vec![
        recorded(&seen, text("no call")),
        recorded(&seen, text("still no call")),
        recorded(&seen, text("plain")),
        // Taken only by a forced retry of the second run.
        recorded(&seen, text("unused")),
    ]);

    // The forced run asks twice (its one try), then fails; its last miss
    // removed the layer, so the next run goes unforced.
    submit(&root, "go").await;
    harness.wait_for_idle(cx()).await.expect("idle");
    submit(&root, "again").await;
    harness.wait_for_idle(cx()).await.expect("idle");

    let soft = "Call the `finish` tool now: your reply must include a call to `finish`.";
    assert_eq!(
        *seen.lock().unwrap_or_else(PoisonError::into_inner),
        vec![soft.to_owned(), soft.to_owned(), "again".to_owned()]
    );
    assert_eq!(setup.faux.get_pending_response_count(), 1);
    assert_eq!(
        director_state(&harness, root.id(), cx())
            .await
            .expect("read"),
        DirectorState::default()
    );
    assert_eq!(
        director_notices(entries(&root).await),
        vec![CustomEntryData {
            custom_type: DIRECTOR_NOTICE_CUSTOM_TYPE.to_owned(),
            content: Some(UserContent::Text(
                "The model did not call the forced tool finish in 2 requests. The forced call left the Director stack."
                    .to_owned()
            )),
            display: true,
            details: Some(json!({ "kind": "notCalled", "tool": "finish", "attempts": 2 })),
            input: false,
            origin: None,
        }]
    );
    harness.close(cx()).await.expect("close");
}

#[tokio::test]
async fn a_reminder_waits_on_the_stack_until_a_continuation_comes() {
    let setup = setup();
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    let reminder = "Run the tests first.";
    setup
        .host_request(
            "directors.push",
            json!({ "layer": "reminder", "text": reminder }),
        )
        .await
        .expect("directors.push succeeds");
    setup.faux.set_responses(vec![answer("a")]);

    // No layer continues the first run: the reminder stays.
    submit(&root, "go").await;
    harness.wait_for_idle(cx()).await.expect("idle");
    let limits = DirectorLimits::default();
    let state = director_state(&harness, root.id(), cx())
        .await
        .expect("read");
    assert_eq!(
        state,
        DirectorState {
            stack: vec![Layer::reminder(reminder.to_owned())],
            run: Some(RunLoop {
                input: loop_input(&state),
                left: limits.max_steps,
                end: Some(End::Hand),
            }),
        }
    );

    // The goal's continuation of the next run carries it.
    setup
        .host_request("goal.create", json!({ "objective": "ship it" }))
        .await
        .expect("goal.create succeeds");
    setup
        .faux
        .set_responses(vec![answer("b"), finish_call(), answer("done")]);
    submit(&root, "work").await;
    harness.wait_for_idle(cx()).await.expect("idle");

    let texts = user_texts(&entries(&root).await);
    assert_eq!(texts.len(), 3, "{texts:?}");
    assert!(
        texts[2].starts_with("Run the tests first.\n\n[goal: continuation]"),
        "{texts:?}"
    );
    let state = director_state(&harness, root.id(), cx())
        .await
        .expect("read");
    assert_eq!(
        state,
        DirectorState {
            stack: vec![Layer {
                kind: LayerKind::Goal,
                budget: limits.max_steps - 1,
            }],
            run: Some(RunLoop {
                input: loop_input(&state),
                left: limits.max_steps - 1,
                end: Some(End::Hand),
            }),
        }
    );
    harness.close(cx()).await.expect("close");
}

#[tokio::test]
async fn the_goal_keeps_its_place_on_a_full_stack() {
    let setup = setup();
    let limits = DirectorLimits {
        stack_cap: 1,
        max_steps: 8,
        stall_steps: DEFAULT_STALL_STEPS,
    };
    *setup.limits.lock().unwrap_or_else(PoisonError::into_inner) = limits;
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    let push = |text: &str| {
        setup.host_request(
            "directors.push",
            json!({ "layer": "reminder", "text": text }),
        )
    };
    push("Run the tests first.")
        .await
        .expect("the first reminder fits");
    let refused = push("One too many.").await.expect_err("the cap refuses");
    assert_eq!(
        refused.to_string(),
        "The Director stack is full: 1 reminders and forced calls (directors.stackCap)"
    );
    setup
        .host_request("goal.create", json!({ "objective": "ship it" }))
        .await
        .expect("goal.create succeeds");
    setup
        .faux
        .set_responses(vec![answer("a"), finish_call(), answer("done")]);

    submit(&root, "work").await;
    harness.wait_for_idle(cx()).await.expect("idle");

    // The pushed layer filled the cap; the goal still came on the stack
    // and continued the run.
    let texts = user_texts(&entries(&root).await);
    assert_eq!(texts.len(), 2, "{texts:?}");
    assert!(
        texts[1].starts_with("Run the tests first.\n\n[goal: continuation]"),
        "{texts:?}"
    );
    let state = director_state(&harness, root.id(), cx())
        .await
        .expect("read");
    assert_eq!(
        state,
        DirectorState {
            stack: vec![Layer {
                kind: LayerKind::Goal,
                budget: limits.max_steps - 1,
            }],
            run: Some(RunLoop {
                input: loop_input(&state),
                left: limits.max_steps - 1,
                end: Some(End::Hand),
            }),
        }
    );
    harness.close(cx()).await.expect("close");
}

#[tokio::test]
async fn a_reopen_reads_the_stack_back_and_a_fork_restores_the_stack_of_its_entry() {
    let dir = tempfile::tempdir().expect("tempdir");
    let setup = setup();
    let (harness, root) = setup.open(open_jsonl(dir.path()).await).await;
    setup
        .host_request("goal.create", json!({ "objective": "persist" }))
        .await
        .expect("goal.create succeeds");
    setup.faux.set_responses(vec![
        answer("first"),
        answer("second"),
        finish_call(),
        answer("done"),
    ]);
    submit(&root, "work").await;
    harness.wait_for_idle(cx()).await.expect("idle");
    let before = director_state(&harness, root.id(), cx())
        .await
        .expect("read");
    harness.close(cx()).await.expect("close");
    setup.cell.clear();

    let (harness, root) = setup.open(open_jsonl(dir.path()).await).await;
    assert_eq!(
        director_state(&harness, root.id(), cx())
            .await
            .expect("read"),
        before
    );

    // At the first answer the goal layer had made one step; before it, the
    // conversation had no Director.
    let entries = entries(&root).await;
    let first_answer = assistant_ids(&entries)[0];
    let max = DirectorLimits::default().max_steps;
    let forked = root
        .fork(
            first_answer,
            ConversationCreateOptions::new(ConversationOwnership::Ownerless),
            cx(),
        )
        .await
        .expect("fork");
    assert_eq!(
        director_state(&harness, forked.id(), cx())
            .await
            .expect("read"),
        DirectorState {
            stack: vec![Layer {
                kind: LayerKind::Goal,
                budget: max - 1,
            }],
            run: Some(RunLoop {
                input: loop_input(&before),
                left: max - 1,
                end: None,
            }),
        }
    );
    let at_input = root
        .fork(
            entries[0].id,
            ConversationCreateOptions::new(ConversationOwnership::Ownerless),
            cx(),
        )
        .await
        .expect("fork");
    assert_eq!(
        director_state(&harness, at_input.id(), cx())
            .await
            .expect("read"),
        DirectorState::default()
    );
    harness.close(cx()).await.expect("close");
}
