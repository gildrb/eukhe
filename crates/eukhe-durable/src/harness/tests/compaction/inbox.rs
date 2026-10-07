//! "compaction and the inbox", "blocking and manual compaction together",
//! and "context contributions".

use eukhe_chord::json::{to_json, JsonValue};
use eukhe_types::pi_ai::{AssistantMessage, Message, UserContent, UserMessage};

use super::{
    answer, compact, compaction_tasks, failure, gated, history, kinds, live, open, result,
    submission, submission_id, submit, summary, text, turn, user_text, Chat, OpenOptions, BLOCKING,
    MANUAL,
};
use crate::harness::tests::chat_support::{all_entries, wait_for};
use crate::harness::tests::support::context;
use crate::harness::tests::task_support::{deferred, Deferred};
use crate::harness::types::{
    CompactionPolicy, CompactionResult, ConversationAbortOptions, WriteSubmissionDraft,
};
use crate::harness::SubmissionHandle;
use crate::types::{
    ContextEdit, ContextEditAction, EntryDraft, EntryHead, SubmissionStatus, TaskId, TaskOutcome,
};

fn user(content: &str) -> Message {
    Message::User(UserMessage {
        content: UserContent::Text(content.to_owned()),
        timestamp: 0,
    })
}

async fn queued_summary(chat: &Chat, content: &str) -> SubmissionHandle {
    chat.faux.summary(summary(content));
    let outcome = result(chat, compact(chat, None).await).await;
    submission(chat, submission_id(&outcome)).await
}

struct Busy {
    input: SubmissionHandle,
    gate: Deferred,
}

async fn busy(chat: &Chat, reply: AssistantMessage) -> Busy {
    let gate = deferred();
    let reached = deferred();
    chat.faux.agent(gated(&gate, reply, Some(&reached)));
    let input = submit(chat, "busy").await;
    reached.wait().await;
    Busy { input, gate }
}

async fn status(handle: &SubmissionHandle) -> SubmissionStatus {
    handle.status(context()).await.unwrap().state.status()
}

#[tokio::test]
async fn places_a_reset_queued_after_the_summary_last_and_makes_a_summary_queued_after_a_reset_stale(
) {
    for summary_first in [true, false] {
        let chat = open(OpenOptions::default()).await;
        history(&chat).await;
        let run = busy(&chat, answer("done")).await;
        let handle = if summary_first {
            let handle = queued_summary(&chat, "SUMMARY").await;
            chat.root.reset(None, context()).await.unwrap();
            handle
        } else {
            chat.root.reset(None, context()).await.unwrap();
            queued_summary(&chat, "SUMMARY").await
        };
        run.gate.resolve(());
        run.input.wait(context()).await.unwrap();
        let settled = handle.wait(context()).await.unwrap();
        assert_eq!(
            settled.state.status(),
            if summary_first {
                SubmissionStatus::Done
            } else {
                SubmissionStatus::Unanswered
            }
        );
        assert_eq!(kinds(&chat.root).await.last().unwrap(), "pi.reset");
        assert_eq!(
            chat.root
                .context(context())
                .await
                .unwrap()
                .head
                .map(|head| head.kind),
            Some("pi.reset".to_owned())
        );
        chat.harness.close(context()).await.unwrap();
    }
}

#[tokio::test]
async fn places_a_summary_left_queued_by_a_failed_run_at_the_next_submission_before_its_input() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    let run = busy(&chat, failure("bad request")).await;
    let handle = queued_summary(&chat, "SUMMARY").await;
    run.gate.resolve(());
    assert_eq!(
        run.input.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Unanswered
    );
    assert_eq!(status(&handle).await, SubmissionStatus::Queued);
    turn(&chat, "again", "ok").await;
    assert_eq!(status(&handle).await, SubmissionStatus::Done);
    let request = chat.faux.last_agent_messages();
    assert!(user_text(request.first()).contains("SUMMARY"));
    assert!(request
        .iter()
        .any(|message| user_text(Some(message)) == "again"));
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn keeps_the_full_retry_budget_after_an_overflow_compaction() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    chat.set_policy(CompactionPolicy {
        enabled: true,
        ..MANUAL
    });
    chat.faux.summary(summary("SUMMARY"));
    chat.faux.agent(failure("prompt is too long"));
    chat.faux.agent(failure("overloaded"));
    chat.faux.agent(failure("overloaded"));
    chat.faux.agent(answer("finally"));
    let input = submit(&chat, &text("u4", 100)).await;
    assert_eq!(
        input.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Done
    );
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn loses_an_application_edit_placed_while_a_compaction_summarizes() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    let u1 = all_entries(&chat.root, context()).await.unwrap()[0].id;
    let gate = deferred();
    let reached = deferred();
    chat.faux
        .summary(gated(&gate, summary("SUMMARY"), Some(&reached)));
    let id = compact(&chat, None).await;
    reached.wait().await;
    let edit = EntryDraft {
        edits: Some(vec![ContextEdit {
            target: u1,
            action: ContextEditAction::Replace {
                messages: vec![user("REDACTED")],
            },
        }]),
        ..EntryDraft::new("app.redact")
    };
    chat.root
        .submit(
            WriteSubmissionDraft {
                request_id: None,
                entry: edit,
            },
            context(),
        )
        .await
        .unwrap();
    gate.resolve(());
    result(&chat, id).await;
    // The summary was made from the unredacted entry, and the edit's target
    // left the range.
    assert!(user_text(chat.faux.summary_requests()[0].messages.get(1)).contains("[User]: u1 "));
    assert!(!chat
        .root
        .context(context())
        .await
        .unwrap()
        .messages
        .iter()
        .any(|message| user_text(Some(message)) == "REDACTED"));
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn keeps_the_kept_entries_mounted_in_the_conversation_view() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    let state = chat.root.view_state(context()).await.unwrap();
    chat.faux.summary(summary("SUMMARY"));
    result(&chat, compact(&chat, None).await).await;
    wait_for(
        || async { state.value()["entries"][0]["kind"] == JsonValue::from("pi.compaction") },
        5000,
    )
    .await;
    let entries = chat.root.context(context()).await.unwrap().entries;
    assert_eq!(state.value()["entries"], to_json(&entries).unwrap());
    state.dispose().unwrap();
    chat.harness.close(context()).await.unwrap();
}

// ─── Blocking and manual compaction together ──────────────────────────────

/// A run whose generation waits on a blocking compaction whose summary is
/// held.
struct BlockingRun {
    input: SubmissionHandle,
    gate: Deferred,
    blocking: TaskId<CompactionResult>,
}

async fn blocking_run(chat: &Chat) -> BlockingRun {
    history(chat).await;
    chat.set_policy(BLOCKING);
    let gate = deferred();
    let reached = deferred();
    chat.faux
        .summary(gated(&gate, summary("BLOCKING"), Some(&reached)));
    let input = submit(chat, &text("u4", 200)).await;
    reached.wait().await;
    let blocking = compaction_tasks(chat).await.remove(0).id;
    BlockingRun {
        input,
        gate,
        blocking: TaskId::from_number(blocking.get()),
    }
}

fn small() -> OpenOptions {
    OpenOptions {
        context_window: Some(1000),
        ..OpenOptions::default()
    }
}

#[tokio::test]
async fn places_a_manual_summary_selected_before_the_blocking_one_landed_its_equal_cut_replaces_it()
{
    let chat = open(small()).await;
    let run = blocking_run(&chat).await;
    // Selected from the same context as the blocking compaction, so it cuts
    // at the same entry.
    let handle = queued_summary(&chat, "MANUAL").await;
    assert_eq!(status(&handle).await, SubmissionStatus::Queued);
    chat.faux.agent(answer("a4"));
    run.gate.resolve(());
    assert_eq!(
        run.input.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Done
    );
    // The request after the blocking compaction used its summary; the manual
    // one landed at the final boundary.
    assert!(user_text(chat.faux.last_agent_messages().first()).contains("BLOCKING"));
    assert_eq!(
        handle.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Done
    );
    let markers: Vec<_> = all_entries(&chat.root, context())
        .await
        .unwrap()
        .into_iter()
        .filter(|record| record.kind == "pi.compaction")
        .collect();
    assert_eq!(markers.len(), 2);
    assert_eq!(markers[1].head, markers[0].head);
    let messages = chat.root.context(context()).await.unwrap().messages;
    assert!(user_text(messages.first()).contains("MANUAL"));
    assert!(!messages
        .iter()
        .any(|message| user_text(Some(message)).contains("BLOCKING")));
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn finds_nothing_to_compact_for_a_manual_compaction_selected_after_the_blocking_summary_landed(
) {
    let chat = open(small()).await;
    let run = blocking_run(&chat).await;
    let answer_gate = deferred();
    let answer_reached = deferred();
    chat.faux
        .agent(gated(&answer_gate, answer("a4"), Some(&answer_reached)));
    run.gate.resolve(());
    answer_reached.wait().await;
    assert_eq!(
        result(&chat, compact(&chat, None).await).await,
        TaskOutcome::Completed {
            result: CompactionResult::default()
        }
    );
    assert_eq!(chat.faux.summary_requests().len(), 1);
    answer_gate.resolve(());
    assert_eq!(
        run.input.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Done
    );
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn aborts_the_run_and_both_compactions_on_esc_and_appends_nothing() {
    let chat = open(small()).await;
    let run = blocking_run(&chat).await;
    let manual_reached = deferred();
    chat.faux
        .summary(gated(&deferred(), summary("MANUAL"), Some(&manual_reached)));
    let manual = compact(&chat, None).await;
    manual_reached.wait().await;
    assert_eq!(
        live(&chat)
            .await
            .compactions
            .unwrap()
            .iter()
            .map(|status| status.blocking)
            .collect::<Vec<_>>(),
        [true, false]
    );
    chat.root
        .abort(ConversationAbortOptions::default(), context())
        .await
        .unwrap();
    let settled = run.input.wait(context()).await.unwrap();
    assert_eq!(settled.state.status(), SubmissionStatus::Unanswered);
    assert_eq!(settled.state.reason(), Some("aborted"));
    assert!(matches!(
        result(&chat, run.blocking).await,
        TaskOutcome::Aborted { .. }
    ));
    assert!(matches!(
        result(&chat, manual).await,
        TaskOutcome::Aborted { .. }
    ));
    let state = live(&chat).await;
    assert_eq!(state.compactions, None);
    assert_eq!(state.run, None);
    assert!(!kinds(&chat.root)
        .await
        .iter()
        .any(|kind| kind == "pi.compaction"));
    assert!(chat
        .harness
        .inspect(context())
        .await
        .unwrap()
        .submissions
        .is_empty());
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn places_a_summary_that_survived_esc_at_the_next_submission_before_its_input() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    let reached = deferred();
    chat.faux
        .agent(gated(&deferred(), answer("never"), Some(&reached)));
    let busy = submit(&chat, "busy").await;
    reached.wait().await;
    let handle = queued_summary(&chat, "SUMMARY").await;
    chat.root
        .abort(ConversationAbortOptions::default(), context())
        .await
        .unwrap();
    let settled = busy.wait(context()).await.unwrap();
    assert_eq!(settled.state.status(), SubmissionStatus::Unanswered);
    assert_eq!(settled.state.reason(), Some("aborted"));
    assert_eq!(status(&handle).await, SubmissionStatus::Queued);
    turn(&chat, "u5", "a5").await;
    assert_eq!(status(&handle).await, SubmissionStatus::Done);
    let request = chat.faux.last_agent_messages();
    assert!(user_text(request.first()).contains("SUMMARY"));
    assert!(request
        .iter()
        .any(|message| user_text(Some(message)) == "u5"));
    let kinds = kinds(&chat.root).await;
    assert_eq!(
        kinds[kinds.len() - 4..],
        ["pi.compaction", "pi.user", "pi.system", "pi.assistant"]
    );
    chat.harness.close(context()).await.unwrap();
}

// ─── Context contributions ────────────────────────────────────────────────

#[tokio::test]
async fn apply_edits_carried_by_an_older_head_marker_in_the_range() {
    let chat = open(OpenOptions::default()).await;
    let id = chat.id();
    let ids = chat
        .root
        .commit(
            move |tx| async move {
                let note = |content: &str| EntryDraft {
                    model: Some(vec![user(content)]),
                    ..EntryDraft::new("app.note")
                };
                let a = tx.append_entry(id, note("a")).await?;
                let b = tx.append_entry(id, note("b")).await?;
                // An older marker that omits b, then a newer one whose range
                // still contains the older marker.
                tx.append_entry(
                    id,
                    EntryDraft {
                        head: Some(EntryHead::Entry(a.id)),
                        edits: Some(vec![ContextEdit {
                            target: b.id,
                            action: ContextEditAction::Omit,
                        }]),
                        ..EntryDraft::new("app.head")
                    },
                )
                .await?;
                let c = tx.append_entry(id, note("c")).await?;
                tx.append_entry(
                    id,
                    EntryDraft {
                        head: Some(EntryHead::Entry(a.id)),
                        model: Some(vec![user("H")]),
                        ..EntryDraft::new("app.head")
                    },
                )
                .await?;
                Ok([a.id, b.id, c.id])
            },
            context(),
        )
        .await
        .unwrap();
    let view = chat.root.context(context()).await.unwrap();
    assert_eq!(
        view.entries[1..]
            .iter()
            .map(|record| record.id)
            .collect::<Vec<_>>(),
        ids
    );
    let texts = |messages: &[Message]| {
        messages
            .iter()
            .map(|message| user_text(Some(message)))
            .collect::<Vec<_>>()
    };
    assert_eq!(
        view.contributions
            .iter()
            .map(|messages| texts(messages))
            .collect::<Vec<_>>(),
        [
            vec!["H".to_owned()],
            vec!["a".to_owned()],
            vec![],
            vec!["c".to_owned()]
        ]
    );
    assert_eq!(texts(&view.messages), ["H", "a", "c"]);
    // The summarizer sees the same contributions: the omitted entry stays out.
    chat.set_policy(CompactionPolicy {
        keep_recent_tokens: 1.0,
        ..MANUAL
    });
    chat.faux.summary(summary("SUMMARY"));
    result(&chat, compact(&chat, None).await).await;
    let prompt = user_text(chat.faux.summary_requests()[0].messages.get(1));
    assert!(prompt.contains("<conversation>\n[User]: H\n\n[User]: a\n</conversation>"));
    chat.harness.close(context()).await.unwrap();
}
