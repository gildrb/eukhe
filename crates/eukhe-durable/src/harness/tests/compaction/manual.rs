//! "manual compaction".

use std::sync::Arc;

use eukhe_chord::json::JsonValue;
use eukhe_pi_ai::providers::faux::{faux_tool_call, RegisterFauxProviderOptions};
use eukhe_types::pi_ai::{
    CacheRetention, JsonObject as PiJsonObject, Message, StopReason, SystemMessage,
};

use super::{
    answer, compact, doc, failure, gated, history, input_tokens, kinds, live, open, result, script,
    set_policy, status_of, submission, submission_id, submit, summary, text, text_tool, turn,
    user_text, with_stop, OpenOptions, MANUAL,
};
use crate::harness::provider::{ProviderState, PROVIDER_DOC};
use crate::harness::tests::chat_support::{
    all_entries, chat_setup, open_chat, tools_named, wait_for, OpenChat,
};
use crate::harness::tests::support::{add_tool, context};
use crate::harness::tests::task_support::{deferred, settled};
use crate::harness::types::{
    AgentChange, CompactionPolicy, CompactionResult, ConversationAbortOptions, FieldChange,
    SubmissionAbort, ToolsChange,
};
use crate::storage::MemoryStorage;
use crate::types::{SubmissionStatus, TaskOutcome, TaskState};

fn role(message: &Message) -> &'static str {
    match message {
        Message::System(_) => "system",
        Message::User(_) => "user",
        Message::Assistant(_) => "assistant",
        Message::ToolResult(_) => "toolResult",
    }
}

fn section<'a>(system: &'a SystemMessage, key: &str) -> Option<&'a str> {
    system
        .sections
        .as_ref()
        .and_then(|sections| sections.get(key))
        .and_then(Option::as_deref)
}

#[tokio::test]
async fn places_the_summary_at_once_when_idle_and_keeps_raw_history() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    let before = all_entries(&chat.root, context()).await.unwrap();
    let usage_before = input_tokens(&chat).await;
    chat.faux.summary(summary("SUMMARY"));

    let id = compact(&chat, Some("focus on files")).await;
    let outcome = result(&chat, id).await;
    assert!(matches!(outcome, TaskOutcome::Completed { .. }));
    let placed = submission(&chat, submission_id(&outcome))
        .await
        .wait(context())
        .await
        .unwrap();
    assert_eq!(placed.state.status(), SubmissionStatus::Done);

    // Raw history is unchanged; one summary entry heads the first kept entry, u3.
    let after = all_entries(&chat.root, context()).await.unwrap();
    assert_eq!(after[..before.len()], before[..]);
    let marker = after.last().unwrap();
    let u3 = before
        .iter()
        .find(|record| {
            user_text(record.model.as_ref().and_then(|model| model.first())).starts_with("u3")
        })
        .unwrap();
    assert_eq!(marker.kind, "pi.compaction");
    assert_eq!(marker.head, Some(u3.id));
    assert_eq!(
        marker.data,
        Some(JsonValue::parse(r#"{"reason":"manual"}"#).unwrap())
    );
    assert_eq!(placed.state.entry(), Some(marker.id));
    let wrapped = user_text(marker.model.as_ref().and_then(|model| model.first()));
    assert_eq!(
        wrapped,
        "The conversation history before this point was compacted into the following summary:\n\n<summary>\nSUMMARY\n</summary>"
    );

    // The model context is the summary followed by the kept entries.
    let view = chat.root.context(context()).await.unwrap();
    assert_eq!(
        view.messages
            .iter()
            .map(|message| user_text(Some(message)))
            .collect::<Vec<_>>(),
        [wrapped, text("u3", 100), text("a3", 100)]
    );

    // The summarizer saw the serialized prefix, the prompt, and the
    // instructions, without tools or caching.
    let request = chat.faux.summary_requests()[0].clone();
    assert_eq!(request.messages.len(), 2);
    let prompt = user_text(request.messages.get(1));
    assert!(prompt.starts_with("<conversation>\n[User]: u1 "));
    assert!(prompt.contains("[Assistant]: a2 "));
    assert!(!prompt.contains("u3 "));
    assert!(prompt.contains("## Goal"));
    assert!(prompt.ends_with("\n\nAdditional focus: focus on files"));
    let options = request.options.unwrap();
    let provider: ProviderState = doc(&chat.harness, &PROVIDER_DOC, chat.id()).await.unwrap();
    assert_eq!(options.stream.cache_retention, Some(CacheRetention::None));
    assert_eq!(options.stream.max_tokens, Some(800));
    assert_eq!(options.stream.session_id, Some(provider.session_id));
    assert_eq!(options.deferred, None);

    // The summarizer's spend is in the ledger, and nothing counts it again later.
    assert!(input_tokens(&chat).await > usage_before);
    turn(&chat, "next", "done").await;
    let agent = chat.faux.last_agent_messages();
    // The next request: the summary, the kept turn, the new input, then one
    // complete system baseline.
    assert_eq!(
        agent.iter().map(role).collect::<Vec<_>>(),
        ["user", "user", "assistant", "user", "system"]
    );
    let Message::System(system) = &agent[4] else {
        panic!("a system message");
    };
    assert_eq!(section(system, "preamble"), Some("You are helpful."));
    chat.harness.close(context()).await.unwrap();
}

// Regression coverage for #10424.
#[tokio::test]
async fn creates_provider_state_before_a_legacy_conversations_summarization_request() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    let id = chat.id();
    chat.root
        .commit(
            move |tx| async move { tx.retire_doc(&PROVIDER_DOC, id).await },
            context(),
        )
        .await
        .unwrap();
    assert!(doc::<_, ProviderState>(&chat.harness, &PROVIDER_DOC, id)
        .await
        .is_none());
    chat.faux.summary(summary("SUMMARY"));
    let outcome = result(&chat, compact(&chat, None).await).await;
    assert!(matches!(outcome, TaskOutcome::Completed { .. }));
    let stored: ProviderState = doc(&chat.harness, &PROVIDER_DOC, id).await.unwrap();
    let session_id = &stored.session_id;
    let shape = session_id.split('-').map(str::len).collect::<Vec<_>>();
    assert_eq!(shape, [8, 4, 4, 4, 12]);
    assert!(session_id
        .chars()
        .all(|character| character == '-' || matches!(character, '0'..='9' | 'a'..='f')));
    assert_eq!(&session_id[14..15], "7");
    assert!(matches!(&session_id[19..20], "8" | "9" | "a" | "b"));
    assert_eq!(
        chat.faux.summary_requests()[0]
            .options
            .as_ref()
            .unwrap()
            .stream
            .session_id
            .as_ref(),
        Some(session_id)
    );
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn keeps_working_while_busy_and_places_the_summary_at_the_next_final_boundary() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    let gate = deferred();
    let reached = deferred();
    chat.faux
        .agent(gated(&gate, answer("late answer"), Some(&reached)));
    let input = submit(&chat, "busy").await;
    reached.wait().await;
    chat.faux.summary(summary("SUMMARY"));
    let outcome = result(&chat, compact(&chat, None).await).await;
    let id = submission_id(&outcome);
    assert_eq!(status_of(&chat, id).await, SubmissionStatus::Queued);
    gate.resolve(());
    assert_eq!(
        input.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Done
    );
    let placed = submission(&chat, id).await.wait(context()).await.unwrap();
    assert_eq!(placed.state.status(), SubmissionStatus::Done);
    // The summary follows the answer; the kept range still includes the busy turn.
    let kinds = kinds(&chat.root).await;
    assert_eq!(
        kinds[kinds.len() - 3..],
        ["pi.user", "pi.assistant", "pi.compaction"]
    );
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn places_a_queued_summary_at_post_tools_and_the_run_continues_in_the_compacted_context() {
    let chat = open(OpenOptions::default()).await;
    add_tool(&chat.setup.registry, text_tool("wait", "waited"), None).unwrap();
    chat.root
        .configure(
            AgentChange {
                tools: FieldChange::Set(ToolsChange::Exactly(tools_named(&chat.setup, &["wait"]))),
                ..AgentChange::default()
            },
            context(),
        )
        .await
        .unwrap();
    history(&chat).await;
    let gate = deferred();
    let reached = deferred();
    chat.faux.agent(gated(
        &gate,
        with_stop(
            vec![faux_tool_call("wait", PiJsonObject::new(), None)],
            StopReason::ToolUse,
        ),
        Some(&reached),
    ));
    chat.faux.agent(answer("after tools"));
    let input = submit(&chat, "use a tool").await;
    reached.wait().await;
    chat.faux.summary(summary("SUMMARY"));
    result(&chat, compact(&chat, None).await).await;
    gate.resolve(());
    assert_eq!(
        input.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Done
    );
    // The continuation request starts with the summary.
    let continuation = chat.faux.last_agent_messages();
    assert!(user_text(continuation.first()).contains("<summary>\nSUMMARY\n</summary>"));
    let kinds = kinds(&chat.root).await;
    assert_eq!(
        kinds[kinds.len() - 4..],
        [
            "pi.tool-result",
            "pi.compaction",
            "pi.system",
            "pi.assistant"
        ]
    );
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn runs_follow_ups_left_by_a_failed_run_after_placing_the_summary() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    let gate = deferred();
    let reached = deferred();
    chat.faux
        .agent(gated(&gate, failure("bad request"), Some(&reached)));
    let failed = submit(&chat, "fails").await;
    reached.wait().await;
    let follow_up = submit(&chat, "follow-up").await;
    gate.resolve(());
    assert_eq!(
        failed.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Unanswered
    );
    assert_eq!(
        follow_up.status(context()).await.unwrap().state.status(),
        SubmissionStatus::Queued
    );

    chat.faux.summary(summary("SUMMARY"));
    chat.faux.agent(answer("followed"));
    result(&chat, compact(&chat, None).await).await;
    assert_eq!(
        follow_up.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Done
    );
    let request = chat.faux.last_agent_messages();
    assert!(user_text(request.first()).contains("SUMMARY"));
    assert!(request
        .iter()
        .any(|message| user_text(Some(message)) == "follow-up"));
    chat.harness.close(context()).await.unwrap();
}

/// Assert `id` settled `unanswered` with `stale`.
async fn assert_stale(chat: &super::Chat, id: crate::types::SubmissionId) {
    let record = submission(chat, id).await.status(context()).await.unwrap();
    assert_eq!(record.state.status(), SubmissionStatus::Unanswered);
    assert_eq!(record.state.reason(), Some("stale"));
}

#[tokio::test]
async fn settles_stale_when_a_reset_lands_while_it_summarizes() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    let gate = deferred();
    let reached = deferred();
    chat.faux
        .summary(gated(&gate, summary("SUMMARY"), Some(&reached)));
    let id = compact(&chat, None).await;
    reached.wait().await;
    chat.root.reset(None, context()).await.unwrap();
    gate.resolve(());
    let outcome = result(&chat, id).await;
    assert_stale(&chat, submission_id(&outcome)).await;
    assert_eq!(kinds(&chat.root).await.last().unwrap(), "pi.reset");
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn does_not_make_the_conversation_busy_a_submission_during_summarization_starts_its_run_at_once(
) {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    let summary_gate = deferred();
    let summary_reached = deferred();
    chat.faux.summary(gated(
        &summary_gate,
        summary("SUMMARY"),
        Some(&summary_reached),
    ));
    let id = compact(&chat, None).await;
    summary_reached.wait().await;
    let answer_gate = deferred();
    let answer_reached = deferred();
    chat.faux
        .agent(gated(&answer_gate, answer("a4"), Some(&answer_reached)));
    let input = submit(&chat, "u4").await;
    // Placed and answered immediately with the uncompacted context, not
    // queued behind the compaction.
    assert_eq!(
        input.status(context()).await.unwrap().state.status(),
        SubmissionStatus::Placed
    );
    answer_reached.wait().await;
    assert_eq!(
        user_text(chat.faux.last_agent_messages().first()),
        text("u1", 100)
    );
    // The summary is ready while the run is busy, so it queues and lands
    // after the answer.
    summary_gate.resolve(());
    let outcome = result(&chat, id).await;
    let placed = submission(&chat, submission_id(&outcome)).await;
    assert_eq!(
        placed.status(context()).await.unwrap().state.status(),
        SubmissionStatus::Queued
    );
    answer_gate.resolve(());
    assert_eq!(
        input.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Done
    );
    assert_eq!(
        placed.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Done
    );
    let kinds = kinds(&chat.root).await;
    assert_eq!(
        kinds[kinds.len() - 3..],
        ["pi.user", "pi.assistant", "pi.compaction"]
    );
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn counts_the_spend_of_a_summary_that_ends_stale_and_writes_no_entry_for_it() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    let before = input_tokens(&chat).await;
    let gate = deferred();
    let reached = deferred();
    chat.faux
        .summary(gated(&gate, summary("SUMMARY"), Some(&reached)));
    let id = compact(&chat, None).await;
    reached.wait().await;
    chat.root.reset(None, context()).await.unwrap();
    gate.resolve(());
    let outcome = result(&chat, id).await;
    assert_stale(&chat, submission_id(&outcome)).await;
    assert!(input_tokens(&chat).await > before);
    assert!(!kinds(&chat.root)
        .await
        .iter()
        .any(|kind| kind == "pi.compaction"));
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn lets_the_compaction_that_cuts_furthest_win_whatever_finishes_first() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    let first = deferred();
    let first_reached = deferred();
    chat.faux
        .summary(gated(&first, summary("FIRST"), Some(&first_reached)));
    let early = compact(&chat, None).await;
    first_reached.wait().await;
    turn(&chat, &text("u4", 100), &text("a4", 100)).await;
    chat.faux.summary(summary("SECOND"));
    let later = result(&chat, compact(&chat, None).await).await;
    assert!(matches!(later, TaskOutcome::Completed { .. }));
    first.resolve(());
    let outcome = result(&chat, early).await;
    // The early compaction cut at u3, before the later cut at u4.
    assert_stale(&chat, submission_id(&outcome)).await;
    let messages = chat.root.context(context()).await.unwrap().messages;
    assert!(user_text(messages.first()).contains("SECOND"));
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn places_an_older_selected_summary_that_cuts_later_than_the_newer_one() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    // A: small budget, late cut; selected first, finishes last.
    let gate = deferred();
    let reached = deferred();
    chat.faux
        .summary(gated(&gate, summary("A"), Some(&reached)));
    let a = compact(&chat, None).await;
    reached.wait().await;
    // B: larger budget, earlier cut; placed first.
    chat.set_policy(CompactionPolicy {
        keep_recent_tokens: 350.0,
        ..MANUAL
    });
    chat.faux.summary(summary("B"));
    result(&chat, compact(&chat, None).await).await;
    let messages = chat.root.context(context()).await.unwrap().messages;
    assert!(user_text(messages.first()).contains('B'));
    gate.resolve(());
    let outcome = result(&chat, a).await;
    assert_eq!(
        status_of(&chat, submission_id(&outcome)).await,
        SubmissionStatus::Done
    );
    let messages = chat.root.context(context()).await.unwrap().messages;
    assert!(user_text(messages.first()).contains("<summary>\nA\n</summary>"));
    assert_eq!(
        messages[1..]
            .iter()
            .map(|message| user_text(Some(message)))
            .collect::<Vec<_>>(),
        [text("u3", 100), text("a3", 100)]
    );
    chat.harness.close(context()).await.unwrap();
}

/// Two summaries queued in one busy run, selected with `keeps`; the second
/// is stale only when it cuts before the first.
async fn places_two_queued_summaries_in_one_boundary(keeps: [f64; 2], stale: bool) {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    let gate = deferred();
    let reached = deferred();
    chat.faux
        .agent(gated(&gate, answer("done"), Some(&reached)));
    let input = submit(&chat, "busy").await;
    reached.wait().await;
    let mut submissions = Vec::new();
    for (index, keep) in keeps.into_iter().enumerate() {
        chat.set_policy(CompactionPolicy {
            keep_recent_tokens: keep,
            ..MANUAL
        });
        chat.faux.summary(summary(&format!("S{index}")));
        let outcome = result(&chat, compact(&chat, None).await).await;
        submissions.push(submission_id(&outcome));
    }
    gate.resolve(());
    input.wait(context()).await.unwrap();
    let mut statuses = Vec::new();
    for id in submissions {
        statuses.push(
            submission(&chat, id)
                .await
                .wait(context())
                .await
                .unwrap()
                .state
                .status(),
        );
    }
    let second = if stale {
        SubmissionStatus::Unanswered
    } else {
        SubmissionStatus::Done
    };
    assert_eq!(statuses, [SubmissionStatus::Done, second]);
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn places_two_queued_summaries_in_one_boundary_when_the_second_cuts_before_the_first() {
    places_two_queued_summaries_in_one_boundary([150.0, 350.0], true).await;
}

#[tokio::test]
async fn places_two_queued_summaries_in_one_boundary_when_the_second_cuts_at_the_first() {
    places_two_queued_summaries_in_one_boundary([150.0, 150.0], false).await;
}

#[tokio::test]
async fn places_two_queued_summaries_in_one_boundary_when_the_second_cuts_after_the_first() {
    places_two_queued_summaries_in_one_boundary([350.0, 150.0], false).await;
}

#[tokio::test]
async fn is_aborted_by_conversation_abort_an_already_queued_summary_survives_it() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    let reached = deferred();
    chat.faux
        .summary(gated(&deferred(), summary("SUMMARY"), Some(&reached)));
    let id = compact(&chat, None).await;
    reached.wait().await;
    assert_eq!(
        live(&chat).await.compactions.map(|list| list.len()),
        Some(1)
    );
    chat.root
        .abort(ConversationAbortOptions::default(), context())
        .await
        .unwrap();
    assert!(matches!(
        result(&chat, id).await,
        TaskOutcome::Aborted { .. }
    ));
    assert_eq!(live(&chat).await.compactions, None);
    assert!(!kinds(&chat.root)
        .await
        .iter()
        .any(|kind| kind == "pi.compaction"));

    // Queued while busy, then Esc: the queued write stays and lands with the
    // next run's boundary.
    let busy = deferred();
    chat.faux
        .agent(gated(&deferred(), answer("never"), Some(&busy)));
    submit(&chat, "busy").await;
    busy.wait().await;
    chat.faux.summary(summary("SUMMARY"));
    let queued = result(&chat, compact(&chat, None).await).await;
    chat.root
        .abort(ConversationAbortOptions::default(), context())
        .await
        .unwrap();
    let handle = submission(&chat, submission_id(&queued)).await;
    assert_eq!(
        handle.status(context()).await.unwrap().state.status(),
        SubmissionStatus::Queued
    );
    assert_eq!(
        handle.abort(context()).await.unwrap(),
        SubmissionAbort::Aborted
    );
    turn(&chat, "next", "ok").await;
    let record = handle.status(context()).await.unwrap();
    assert_eq!(record.state.status(), SubmissionStatus::Unanswered);
    assert_eq!(record.state.reason(), Some("aborted"));
    assert!(!kinds(&chat.root)
        .await
        .iter()
        .any(|kind| kind == "pi.compaction"));
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn is_ordinary_work_idle_waits_include_it() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    let gate = deferred();
    let reached = deferred();
    chat.faux
        .summary(gated(&gate, summary("SUMMARY"), Some(&reached)));
    let id = compact(&chat, None).await;
    reached.wait().await;
    let wait = tokio::spawn(chat.root.wait_for_idle(context()));
    // TS sleeps 20 ms; flushing pending work shows the same: it still waits.
    assert!(!settled(&wait).await);
    gate.resolve(());
    wait.await.unwrap().unwrap();
    let record = chat.harness.get_task(id, context()).await.unwrap().unwrap();
    assert!(matches!(record.state, TaskState::Terminal { .. }));
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn enables_scheduling_right_after_open() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let faux = script(&setup);
    let OpenChat { harness, root } = open_chat(Arc::new(MemoryStorage::new()), &setup, None)
        .await
        .unwrap();
    set_policy(
        &setup,
        CompactionPolicy {
            keep_recent_tokens: 10.0,
            ..MANUAL
        },
    );
    let id = root.compact(None, context()).await.unwrap();
    // get_task() only reads, so progress here comes from compact() itself.
    wait_for(
        || {
            let task = harness.get_task(id, context());
            async move {
                task.await
                    .unwrap()
                    .is_some_and(|record| matches!(record.state, TaskState::Terminal { .. }))
            }
        },
        5000,
    )
    .await;
    let record = harness.get_task(id, context()).await.unwrap().unwrap();
    let TaskState::Terminal { outcome } = record.state else {
        panic!("terminal");
    };
    assert_eq!(
        outcome,
        TaskOutcome::Completed {
            result: eukhe_chord::json::to_json(&CompactionResult::default()).unwrap()
        }
    );
    assert!(faux.summary_requests().is_empty());
    harness.close(context()).await.unwrap();
}
