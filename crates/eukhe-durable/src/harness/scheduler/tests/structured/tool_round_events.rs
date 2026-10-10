//! `describe("tool rounds and events")`.

use std::sync::Arc;

use eukhe_pi_ai::providers::faux::RegisterFauxProviderOptions;
use eukhe_types::pi_ai::{TextContent, Usage, UserContentBlock};

use super::chat::{
    blocking_tool, events_of, input, labels, listen, live, noop, run_task, scan, start_hooked,
    text_message, tool_calls,
};
use super::{
    create, in_conversation, outcome_of, owned, owned_conversation, state, status, Behavior, Script,
};
use crate::harness::define::define_tool;
use crate::harness::live::ToolSlotStatus;
use crate::harness::tests::chat_support::{chat_setup, open_chat, wait_for, OpenChat};
use crate::harness::tests::support::{
    add_hooks, add_task, add_tool, context, empty_object_schema, generation_task,
};
use crate::harness::tests::task_support::settled;
use crate::harness::types::{
    GenerationHooks, ToolExecutionApiExt, ToolExecutionResult, ToolRegistration,
};
use crate::harness::AgentEvent;
use crate::storage::MemoryStorage;
use crate::types::{
    EntryDraft, SubmissionStatus, TaskOutcomeStatus, TaskQuery, TaskState, TaskStatus,
};

#[tokio::test]
async fn ends_an_aborted_sequential_rounds_unstarted_calls_with_their_result_entries_right_before_them(
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
    let (stream, events) = listen(&harness, &root).await;
    let submission = root.submit(input("go"), context()).await.unwrap();
    one.started.wait().await;
    let generation = run_task(&harness, &root).await.unwrap();
    harness.abort_task(generation, context()).await.unwrap();
    submission.wait(context()).await.unwrap();
    let delivered = &events;
    wait_for(
        || async move { labels(&events_of(delivered)).contains(&"result:c3".to_owned()) },
        5000,
    )
    .await;
    let ends: Vec<String> = labels(&events_of(&events))
        .into_iter()
        .filter(|label| !label.starts_with("message:"))
        .collect();
    assert_eq!(
        ends,
        [
            "end:c1:true",
            "result:c1",
            "end:c2:true",
            "result:c2",
            "end:c3:true",
            "result:c3",
        ]
    );
    stream.stop().await;
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn emits_one_turn_end_per_generation_also_for_a_stream_attached_while_it_holds() {
    let script = Script::new();
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_task(&setup.registry, script.node().clone(), None).unwrap();
    add_tool(&setup.registry, define_tool(noop()), None).unwrap();
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
    let (early_stream, early) = listen(&harness, &root).await;
    root.submit(input("go"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    let (late_stream, late) = listen(&harness, &root).await;
    script.open("hooked");
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
    harness.wait_for_task(first.id, context()).await.unwrap();
    let id = root.id();
    root.commit(
        move |tx| async move {
            tx.append_entry(id, EntryDraft::new("note")).await?;
            Ok(())
        },
        context(),
    )
    .await
    .unwrap();
    let delivered = &late;
    wait_for(
        || async move {
            events_of(delivered)
                .iter()
                .any(|event| matches!(event, AgentEvent::EntryAppended { .. }))
        },
        5000,
    )
    .await;
    let turn_ends = |events: &[AgentEvent]| {
        events
            .iter()
            .filter(|event| matches!(event, AgentEvent::TurnEnd))
            .count()
    };
    assert_eq!(turn_ends(&events_of(&early)), 2);
    assert_eq!(turn_ends(&events_of(&late)), 0);
    early_stream.stop().await;
    late_stream.stop().await;
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn lets_a_tool_that_owns_live_work_finish_its_call_at_the_hold_while_the_generation_waits_for_its_final_commit(
) {
    let script = Script::new();
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_task(&setup.registry, script.node().clone(), None).unwrap();
    let node = script.node().clone();
    add_tool(
        &setup.registry,
        define_tool(ToolRegistration::new(
            "delegate",
            "Starts work in a conversation it owns",
            empty_object_schema(),
            move |_, api, cx| {
                let node = node.clone();
                async move {
                    let owner = api.task_id();
                    api.commit(
                        move |tx| async move {
                            let child = tx.create_conversation(owned_conversation(owner)).await?;
                            create(&tx, &node, "sub", in_conversation(child.id)).await?;
                            Ok(())
                        },
                        &cx,
                    )
                    .await?;
                    Ok(ToolExecutionResult {
                        output: Some(vec![UserContentBlock::Text(TextContent::new("started"))]),
                        ..ToolExecutionResult::default()
                    })
                }
            },
        )),
        None,
    )
    .unwrap();
    setup.faux.set_responses(vec![
        tool_calls(&[("delegate", "c1")]).into(),
        text_message("done").into(),
    ]);
    let OpenChat { harness, root } = open_chat(Arc::new(MemoryStorage::new()), &setup, None)
        .await
        .unwrap();
    let (stream, events) = listen(&harness, &root).await;
    let submission = root.submit(input("go"), context()).await.unwrap();
    let (reader, conversation) = (&harness, &root);
    wait_for(
        || async move {
            live(reader, conversation)
                .await
                .and_then(|live| live.tools)
                .and_then(|tools| tools.first().map(|slot| slot.status))
                == Some(ToolSlotStatus::Done)
        },
        5000,
    )
    .await;
    let current = live(&harness, &root).await.unwrap();
    let slot = &current.tools.as_ref().unwrap()[0];
    let tool = slot.task_id.unwrap();
    assert!(slot.entry.is_some());
    assert_eq!(status(&harness, tool).await, TaskStatus::Completing);
    assert_eq!(
        status(&harness, current.run.as_ref().unwrap().task_id).await,
        TaskStatus::Waiting
    );
    let delivered = &events;
    wait_for(
        || async move { labels(&events_of(delivered)).contains(&"end:c1:true".to_owned()) },
        5000,
    )
    .await;
    let waiter = tokio::spawn(submission.wait(context()));
    assert!(!settled(&waiter).await);
    script.open("sub");
    assert_eq!(
        submission.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Done
    );
    assert_eq!(
        outcome_of(&harness, tool).await,
        TaskOutcomeStatus::Completed
    );
    stream.stop().await;
    harness.close(context()).await.unwrap();
}

/// TS returns details holding a function, which is not strict JSON. Rust
/// `JsonValue` cannot hold one; a usage count beyond
/// `Number.MAX_SAFE_INTEGER` is the closest value whose result commit throws
/// the same way (as in the tool task tests).
#[tokio::test]
async fn holds_a_faulted_tools_slot_and_task_failed_until_the_work_it_owns_drained() {
    let script = Script::new();
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_task(&setup.registry, script.node().clone(), None).unwrap();
    script.script("held", Behavior::default().gated_abort("abort.held"));
    let node = script.node().clone();
    add_tool(
        &setup.registry,
        define_tool(ToolRegistration::new(
            "broken",
            "Starts owned work, then returns a result that is not strict JSON",
            empty_object_schema(),
            move |_, api, cx| {
                let node = node.clone();
                async move {
                    let owner = api.task_id();
                    api.commit(
                        move |tx| async move { create(&tx, &node, "held", owned(owner)).await },
                        &cx,
                    )
                    .await?;
                    Ok(ToolExecutionResult {
                        output: Some(Vec::new()),
                        usage: Some(Usage {
                            input: u64::MAX,
                            ..Usage::default()
                        }),
                        ..ToolExecutionResult::default()
                    })
                }
            },
        )),
        None,
    )
    .unwrap();
    setup.faux.set_responses(vec![
        tool_calls(&[("broken", "c1")]).into(),
        text_message("done").into(),
    ]);
    let OpenChat { harness, root } = open_chat(Arc::new(MemoryStorage::new()), &setup, None)
        .await
        .unwrap();
    let (stream, events) = listen(&harness, &root).await;
    let submission = root.submit(input("go"), context()).await.unwrap();
    let logged = &script;
    wait_for(|| async move { logged.logged("abort:held") }, 5000).await;
    let current = live(&harness, &root).await.unwrap();
    let slot = &current.tools.as_ref().unwrap()[0];
    let tool = slot.task_id.unwrap();
    match state(&harness, tool).await {
        TaskState::Completing { outcome } => {
            assert_eq!(outcome.status(), TaskOutcomeStatus::Faulted);
        }
        other => panic!("expected a completing state, got {other:?}"),
    }
    assert_ne!(slot.status, ToolSlotStatus::Done);
    let failed = |events: &[AgentEvent]| {
        events
            .iter()
            .any(|event| matches!(event, AgentEvent::TaskFailed { .. }))
    };
    assert!(!failed(&events_of(&events)));
    script.open("abort.held");
    assert_eq!(
        submission.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Done
    );
    assert_eq!(outcome_of(&harness, tool).await, TaskOutcomeStatus::Faulted);
    let delivered = &events;
    wait_for(|| async move { failed(&events_of(delivered)) }, 5000).await;
    assert!(labels(&events_of(&events)).contains(&"end:c1:false".to_owned()));
    stream.stop().await;
    harness.close(context()).await.unwrap();
}
