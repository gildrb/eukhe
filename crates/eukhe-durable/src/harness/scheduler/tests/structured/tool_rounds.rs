//! `describe("tool rounds")`: the built-in generation and tool tasks.

use std::sync::Arc;

use eukhe_pi_ai::providers::faux::RegisterFauxProviderOptions;
use eukhe_types::pi_ai::{Message, ToolResultMessage};
use futures::FutureExt;

use super::chat::{
    blocking_tool, events_of, input, invalid_final_stream, is_tool_result, listen, live, noop,
    run_task, scan, start_hooked, text_message, tool_calls, turns, with_mode, with_stream,
};
use super::rejecting::Failing;
use super::{json, outcome_of, state, status, Behavior, Script};
use crate::harness::define::define_tool;
use crate::harness::live::LiveState;
use crate::harness::tests::chat_support::{all_entries, chat_setup, open_chat, wait_for, OpenChat};
use crate::harness::tests::support::{add_hooks, add_task, add_tool, context, generation_task};
use crate::harness::tests::task_support::settled;
use crate::harness::types::{GenerationHooks, ToolExecutionMode};
use crate::session::{SessionEnd, SessionError};
use crate::storage::MemoryStorage;
use crate::types::{
    SubmissionStatus, TaskOutcome, TaskOutcomeStatus, TaskQuery, TaskState, TaskStatus,
};

/// The tool result messages of the conversation's tool result entries.
async fn results(root: &crate::harness::Conversation) -> Vec<ToolResultMessage> {
    all_entries(root, context())
        .await
        .unwrap()
        .iter()
        .filter(|entry| is_tool_result(entry))
        .map(
            |entry| match &entry.model.as_ref().expect("a tool result model")[0] {
                Message::ToolResult(result) => result.clone(),
                other => panic!("expected a tool result, got {other:?}"),
            },
        )
        .collect()
}

#[tokio::test]
async fn owns_its_tool_tasks_waits_for_them_and_hands_the_run_to_a_conversation_owned_generation() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_tool(&setup.registry, define_tool(noop()), None).unwrap();
    setup.faux.set_responses(vec![
        tool_calls(&[("noop", "c1"), ("noop", "c2")]).into(),
        text_message("done").into(),
    ]);
    let OpenChat { harness, root } = open_chat(Arc::new(MemoryStorage::new()), &setup, None)
        .await
        .unwrap();
    let submission = root.submit(input("go"), context()).await.unwrap();
    assert_eq!(
        submission.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Done
    );
    let tasks = scan(
        &harness,
        TaskQuery {
            conversation_id: Some(root.id()),
            ..TaskQuery::default()
        },
        20,
    )
    .await;
    let generations: Vec<_> = tasks
        .iter()
        .filter(|task| task.kind == "pi.generation")
        .collect();
    let (first, second) = (generations[0], generations[1]);
    let tool_owners: Vec<_> = tasks
        .iter()
        .filter(|task| task.kind == "pi.tool")
        .map(|task| task.owner)
        .collect();
    assert_eq!(tool_owners, [Some(first.id), Some(first.id)]);
    assert_eq!(first.owner, None);
    assert_eq!(second.owner, None);
    let assistant = all_entries(&root, context())
        .await
        .unwrap()
        .into_iter()
        .find(|entry| entry.kind == "pi.assistant")
        .unwrap();
    assert_eq!(
        first.state,
        TaskState::Terminal {
            outcome: TaskOutcome::Completed {
                result: json(&format!(r#"{{"entryId":{}}}"#, assistant.id.get())),
            },
        }
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn aborts_a_parallel_round_with_its_generation_tools_first_then_the_generation_with_every_result_written(
) {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let one = blocking_tool("one");
    let two = blocking_tool("two");
    add_tool(
        &setup.registry,
        define_tool(with_mode(&one.registration, ToolExecutionMode::Parallel)),
        None,
    )
    .unwrap();
    add_tool(
        &setup.registry,
        define_tool(with_mode(&two.registration, ToolExecutionMode::Parallel)),
        None,
    )
    .unwrap();
    setup
        .faux
        .set_responses(vec![tool_calls(&[("one", "c1"), ("two", "c2")]).into()]);
    let OpenChat { harness, root } = open_chat(Arc::new(MemoryStorage::new()), &setup, None)
        .await
        .unwrap();
    let submission = root.submit(input("go"), context()).await.unwrap();
    one.started.wait().await;
    two.started.wait().await;
    let generation = run_task(&harness, &root).await.unwrap();
    harness.abort_task(generation, context()).await.unwrap();
    let settled_submission = submission.wait(context()).await.unwrap();
    assert_eq!(
        settled_submission.state.status(),
        SubmissionStatus::Unanswered
    );
    assert_eq!(settled_submission.state.reason(), Some("aborted"));
    let ids: Vec<String> = results(&root)
        .await
        .into_iter()
        .map(|result| result.tool_call_id)
        .collect();
    assert_eq!(ids, ["c1", "c2"]);
    assert_eq!(live(&harness, &root).await, Some(LiveState::default()));
    assert_eq!(
        outcome_of(&harness, generation).await,
        TaskOutcomeStatus::Aborted
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn answers_the_unstarted_calls_of_an_aborted_sequential_round_with_aborted_results_in_call_order(
) {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let one = blocking_tool("one");
    add_tool(&setup.registry, define_tool(one.registration.clone()), None).unwrap();
    add_tool(
        &setup.registry,
        define_tool(blocking_tool("two").registration),
        None,
    )
    .unwrap();
    setup.faux.set_responses(vec![tool_calls(&[
        ("one", "c1"),
        ("two", "c2"),
        ("two", "c3"),
    ])
    .into()]);
    let OpenChat { harness, root } = open_chat(Arc::new(MemoryStorage::new()), &setup, None)
        .await
        .unwrap();
    let submission = root.submit(input("go"), context()).await.unwrap();
    one.started.wait().await;
    let started: Vec<bool> = live(&harness, &root)
        .await
        .unwrap()
        .tools
        .unwrap()
        .iter()
        .map(|slot| slot.task_id.is_some())
        .collect();
    assert_eq!(started, [true, false, false]);
    let generation = run_task(&harness, &root).await.unwrap();
    harness.abort_task(generation, context()).await.unwrap();
    let settled_submission = submission.wait(context()).await.unwrap();
    assert_eq!(
        settled_submission.state.status(),
        SubmissionStatus::Unanswered
    );
    assert_eq!(settled_submission.state.reason(), Some("aborted"));
    let results = results(&root).await;
    let ids: Vec<&str> = results
        .iter()
        .map(|result| result.tool_call_id.as_str())
        .collect();
    assert_eq!(ids, ["c1", "c2", "c3"]);
    let errors: Vec<bool> = results.iter().map(|result| result.is_error).collect();
    assert_eq!(errors, [true, true, true]);
    assert_eq!(
        serde_json::to_value(&results[1].content).unwrap(),
        serde_json::json!([
            { "type": "text", "text": "<harness>\n[error] Tool two was aborted\n</harness>" }
        ])
    );
    let tools = scan(
        &harness,
        TaskQuery {
            conversation_id: Some(root.id()),
            kind: Some("pi.tool".to_owned()),
            ..TaskQuery::default()
        },
        20,
    )
    .await;
    assert_eq!(tools.len(), 1);
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn ends_a_turn_at_the_generations_hold_before_its_successors_turn_starts() {
    let script = Script::new();
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_task(&setup.registry, script.node().clone(), None).unwrap();
    add_tool(&setup.registry, define_tool(noop()), None).unwrap();
    // An extension's hook starts work owned by the generation, which holds it while the next turn runs.
    let weak = Arc::downgrade(&script);
    add_hooks(
        &setup.registry,
        generation_task(),
        GenerationHooks {
            after_tools: Some(Arc::new(move |_, _, api, cx| {
                start_hooked(&weak, api.task_id(), cx)
            })),
            ..GenerationHooks::default()
        },
        None,
    )
    .unwrap();
    setup.faux.set_responses(vec![
        tool_calls(&[("noop", "c1")]).into(),
        text_message("done").into(),
    ]);
    let OpenChat { harness, root } = open_chat(Arc::new(MemoryStorage::new()), &setup, None)
        .await
        .unwrap();
    script.set_harness(&harness);
    let (stream, events) = listen(&harness, &root).await;
    root.submit(input("go"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    let first = scan(
        &harness,
        TaskQuery {
            kind: Some("pi.generation".to_owned()),
            ..TaskQuery::default()
        },
        1,
    )
    .await
    .remove(0);
    assert_eq!(status(&harness, first.id).await, TaskStatus::Completing);
    let delivered = &events;
    wait_for(
        || async move { turns(&events_of(delivered)).len() == 4 },
        5000,
    )
    .await;
    assert_eq!(
        turns(&events_of(&events)),
        ["turn_start", "turn_end", "turn_start", "turn_end"]
    );
    script.open("hooked");
    assert_eq!(
        outcome_of(&harness, first.id).await,
        TaskOutcomeStatus::Completed
    );
    wait_for(
        || async move { turns(&events_of(delivered)).len() == 4 },
        5000,
    )
    .await;
    stream.stop().await;
    harness.close(context()).await.unwrap();
}

/// TS proxies `models` so that `streamSimple` returns `invalidFinalStream`;
/// Rust replaces the faux provider's `stream_simple` the same way the
/// generation tests do.
#[tokio::test]
async fn keeps_run_control_with_a_faulted_generation_until_its_owned_work_drains_and_fails_the_harness_on_a_failed_final_commit(
) {
    let script = Script::new();
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    with_stream(&setup, invalid_final_stream());
    add_task(&setup.registry, script.node().clone(), None).unwrap();
    let weak = Arc::downgrade(&script);
    add_hooks(
        &setup.registry,
        generation_task(),
        GenerationHooks {
            before_request: Some(Arc::new(move |_, api, cx| {
                start_hooked(&weak, api.task_id(), cx)
                    .map(|started| started.map(|()| None))
                    .boxed()
            })),
            ..GenerationHooks::default()
        },
        None,
    )
    .unwrap();
    script.script("hooked", Behavior::default().gated_abort("abort.hooked"));
    let storage = Failing::new();
    let OpenChat { harness, root } = open_chat(Arc::clone(&storage) as _, &setup, None)
        .await
        .unwrap();
    script.set_harness(&harness);
    let submission = root.submit(input("hi"), context()).await.unwrap();
    let (reader, conversation) = (&harness, &root);
    wait_for(
        || async move {
            match run_task(reader, conversation).await {
                Some(generation) => status(reader, generation).await == TaskStatus::Completing,
                None => false,
            }
        },
        5000,
    )
    .await;
    let generation = run_task(&harness, &root).await.unwrap();
    match state(&harness, generation).await {
        TaskState::Completing { outcome } => {
            assert_eq!(outcome.status(), TaskOutcomeStatus::Faulted);
        }
        other => panic!("expected a completing state, got {other:?}"),
    }
    let waiter = tokio::spawn(submission.wait(context()));
    assert!(!settled(&waiter).await);
    assert_eq!(run_task(&harness, &root).await, Some(generation));
    // The faulted outcome is cancellation intent: the hooked work is aborted, then the run settles.
    let logged = &script;
    wait_for(|| async move { logged.logged("abort:hooked") }, 5000).await;
    storage.arm(generation);
    script.open("abort.hooked");
    // The final commit, with the run's cleanup, fails: nothing of the cleanup lands, and the Harness fails.
    let end = harness.closed().await;
    assert!(
        matches!(&end, SessionEnd::Failed { error } if error.to_string() == "disk gone"),
        "{end:?}"
    );
    match waiter.await.unwrap() {
        Err(SessionError::Failed(failed)) => assert_eq!(failed.cause().to_string(), "disk gone"),
        other => panic!("expected SessionFailed, got {other:?}"),
    }
    harness.close(context()).await.unwrap();
    // Reopening finalizes the run; the partial becomes one aborted entry.
    let reopened = open_chat(storage.reopen() as _, &setup, None)
        .await
        .unwrap();
    script.set_harness(&reopened.harness);
    let again = reopened
        .harness
        .submission(submission.id(), context())
        .await
        .unwrap()
        .unwrap();
    let settled_submission = again.wait(context()).await.unwrap();
    assert_eq!(
        settled_submission.state.status(),
        SubmissionStatus::Unanswered
    );
    assert_eq!(settled_submission.state.reason(), Some("faulted"));
    assert_eq!(
        live(&reopened.harness, &reopened.root).await,
        Some(LiveState::default())
    );
    let kinds = |entries: Vec<crate::types::EntryRecord>| -> Vec<String> {
        entries.into_iter().map(|entry| entry.kind).collect()
    };
    assert_eq!(
        kinds(all_entries(&reopened.root, context()).await.unwrap()),
        ["pi.user", "pi.assistant"]
    );
    reopened.harness.close(context()).await.unwrap();
}
