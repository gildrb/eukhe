//! Port of `test/harness-context.test.ts`.

use std::sync::Arc;

use eukhe_types::pi_ai::{IndexMap, Message};

use super::support::{
    assistant, context, describe_message, open_harness, system, tool_result, user,
    AssistantOptions, OpenHarnessOptions,
};
use crate::harness::types::ConversationCreateOptions;
use crate::harness::{Conversation, Harness, RootOptions};
use crate::storage::MemoryStorage;
use crate::types::{
    ContextEdit, ContextEditAction, ConversationOwnership, EntryDraft, EntryHead, EntryId,
    EntryRecord,
};
use eukhe_types::pi_ai::StopReason;

struct Setup {
    _harness: Harness,
    root: Conversation,
}

impl Setup {
    async fn append(&self, draft: EntryDraft) -> EntryRecord {
        append_to(&self.root, draft).await
    }

    async fn message(&self, model: impl Into<Message>, kind: &str) -> EntryRecord {
        let mut draft = EntryDraft::new(kind);
        draft.model = Some(vec![model.into()]);
        self.append(draft).await
    }
}

async fn append_to(conversation: &Conversation, draft: EntryDraft) -> EntryRecord {
    let id = conversation.id();
    conversation
        .commit(
            move |tx| async move { tx.append_entry(id, draft).await },
            context(),
        )
        .await
        .unwrap()
}

async fn setup() -> Setup {
    let (harness, _registry) = open_harness(
        Arc::new(MemoryStorage::new()),
        &[],
        OpenHarnessOptions::default(),
    )
    .await
    .unwrap();
    let root = harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    Setup {
        _harness: harness,
        root,
    }
}

fn ids(entries: &[EntryRecord]) -> Vec<EntryId> {
    entries.iter().map(|entry| entry.id).collect()
}

fn described(messages: &[Message]) -> Vec<String> {
    messages.iter().map(describe_message).collect()
}

fn sections(pairs: &[(&str, &str)]) -> IndexMap<String, Option<String>> {
    pairs
        .iter()
        .map(|(key, value)| ((*key).to_owned(), Some((*value).to_owned())))
        .collect()
}

fn draft(kind: &str, f: impl FnOnce(&mut EntryDraft)) -> EntryDraft {
    let mut draft = EntryDraft::new(kind);
    f(&mut draft);
    draft
}

fn replace(target: EntryId, text: &str) -> ContextEdit {
    ContextEdit {
        target,
        action: ContextEditAction::Replace {
            messages: vec![user(text).into()],
        },
    }
}

#[tokio::test]
async fn returns_the_whole_transcript_without_a_head_and_excludes_model_less_entries_from_messages()
{
    let setup = setup().await;
    let first = setup.message(user("hi"), "message").await;
    let note = setup
        .append(draft("note", |draft| {
            draft.data =
                Some(eukhe_chord::json::JsonValue::parse(r#"{"text":"display only"}"#).unwrap());
        }))
        .await;
    let answer = setup
        .message(assistant("hello", AssistantOptions::default()), "message")
        .await;
    let view = setup.root.context(context()).await.unwrap();
    assert!(view.head.is_none());
    assert_eq!(ids(&view.entries), vec![first.id, note.id, answer.id]);
    assert_eq!(described(&view.messages), ["user:hi", "assistant:hello"]);
}

#[tokio::test]
async fn excludes_aborted_error_and_deferred_assistant_messages_but_keeps_their_raw_entries() {
    let setup = setup().await;
    let stopped = |text: &str, reason| {
        assistant(
            text,
            AssistantOptions {
                stop_reason: Some(reason),
                ..AssistantOptions::default()
            },
        )
    };
    setup.message(user("q"), "message").await;
    let aborted = setup
        .message(stopped("partial", StopReason::Aborted), "message")
        .await;
    setup
        .message(stopped("failed", StopReason::Error), "message")
        .await;
    setup
        .message(stopped("later", StopReason::Deferred), "message")
        .await;
    setup
        .message(stopped("done", StopReason::Length), "message")
        .await;
    let view = setup.root.context(context()).await.unwrap();
    assert_eq!(view.entries.len(), 5);
    assert_eq!(view.entries[1].id, aborted.id);
    assert_eq!(described(&view.messages), ["user:q", "assistant:done"]);
}

#[tokio::test]
async fn resolves_self_heads_and_uses_the_newest_head_marker() {
    let setup = setup().await;
    setup.message(user("old"), "message").await;
    let reset = setup
        .append(draft("reset", |draft| {
            draft.head = Some(EntryHead::SelfEntry);
            draft.model = Some(vec![user("fresh start").into()]);
        }))
        .await;
    assert_eq!(reset.head, Some(reset.id));
    let after = setup
        .message(
            assistant("after reset", AssistantOptions::default()),
            "message",
        )
        .await;
    let view = setup.root.context(context()).await.unwrap();
    assert_eq!(view.head.as_ref().map(|head| head.id), Some(reset.id));
    assert_eq!(ids(&view.entries), vec![reset.id, after.id]);
    assert_eq!(
        described(&view.messages),
        ["user:fresh start", "assistant:after reset"]
    );

    // A compaction summary heads an earlier kept entry; older head markers in range drop out.
    let summary = setup
        .append(draft("summary", |draft| {
            draft.head = Some(EntryHead::Entry(after.id));
            draft.model = Some(vec![user("summary").into()]);
        }))
        .await;
    let tail = setup.message(user("next"), "message").await;
    let view = setup.root.context(context()).await.unwrap();
    assert_eq!(view.head.as_ref().map(|head| head.id), Some(summary.id));
    assert_eq!(ids(&view.entries), vec![summary.id, after.id, tail.id]);
    assert_eq!(
        described(&view.messages),
        ["user:summary", "assistant:after reset", "user:next"]
    );
}

#[tokio::test]
async fn applies_the_newest_edit_per_target_within_the_active_range() {
    let setup = setup().await;
    let first = setup.message(user("first"), "message").await;
    let second = setup.message(user("second"), "message").await;
    setup
        .append(draft("edit", |draft| {
            draft.edits = Some(vec![replace(first.id, "first v2")]);
        }))
        .await;
    setup
        .append(draft("edit", |draft| {
            draft.edits = Some(vec![replace(first.id, "first v3")]);
        }))
        .await;
    setup
        .append(draft("edit", |draft| {
            draft.edits = Some(vec![ContextEdit {
                target: second.id,
                action: ContextEditAction::Omit,
            }]);
        }))
        .await;
    let view = setup.root.context(context()).await.unwrap();
    assert_eq!(view.entries.len(), 5);
    assert_eq!(described(&view.messages), ["user:first v3"]);

    // Edits before the active range no longer apply.
    let reset = setup
        .append(draft("reset", |draft| {
            draft.head = Some(EntryHead::Entry(second.id));
        }))
        .await;
    let view = setup.root.context(context()).await.unwrap();
    assert_eq!(view.head.as_ref().map(|head| head.id), Some(reset.id));
    assert!(described(&view.messages).is_empty());
    setup
        .append(draft("edit", |draft| {
            draft.edits = Some(vec![replace(second.id, "second v2")]);
        }))
        .await;
    let view = setup.root.context(context()).await.unwrap();
    assert_eq!(described(&view.messages), ["user:second v2"]);
}

#[tokio::test]
async fn keeps_positional_system_messages_and_orders_tool_results_by_call_order() {
    let setup = setup().await;
    setup
        .message(system(sections(&[("preamble", "You help.")])), "pi.system")
        .await;
    setup.message(user("run tools"), "message").await;
    setup
        .message(
            assistant(
                "calling",
                AssistantOptions {
                    calls: &["b", "a"],
                    ..AssistantOptions::default()
                },
            ),
            "message",
        )
        .await;
    setup.message(tool_result("a", None), "message").await;
    setup
        .append(draft("pi.system", |draft| {
            draft.model = Some(vec![system(sections(&[("cwd", "/repo")])).into()]);
        }))
        .await;
    setup.message(tool_result("b", None), "message").await;
    setup.message(tool_result("zz", None), "message").await;
    setup
        .message(assistant("done", AssistantOptions::default()), "message")
        .await;
    let view = setup.root.context(context()).await.unwrap();
    assert_eq!(
        described(&view.messages),
        [
            "system:preamble",
            "user:run tools",
            "assistant:calling",
            "result:b:result b",
            "result:a:result a",
            "system:cwd",
            "assistant:done",
        ]
    );
}

#[tokio::test]
async fn synthesizes_missing_tool_results_after_a_fork_and_drops_results_cut_from_their_call() {
    let setup = setup().await;
    setup.message(user("go"), "message").await;
    let call = setup
        .message(
            assistant(
                "calling",
                AssistantOptions {
                    calls: &["x", "y"],
                    ..AssistantOptions::default()
                },
            ),
            "message",
        )
        .await;
    setup.message(tool_result("x", None), "message").await;
    let second = setup.message(tool_result("y", None), "message").await;
    let child = setup
        .root
        .fork(
            call.id,
            ConversationCreateOptions::new(ConversationOwnership::Ownerless),
            context(),
        )
        .await
        .unwrap();
    let child_view = child.context(context()).await.unwrap();
    assert_eq!(
        described(&child_view.messages),
        [
            "user:go",
            "assistant:calling",
            "result:x:error",
            "result:y:error",
        ]
    );
    let Message::ToolResult(missing) = &child_view.messages[2] else {
        panic!("expected a tool result");
    };
    assert_eq!(missing.tool_name, "tool-x");
    assert_eq!(
        missing.details,
        Some(serde_json::json!({ "reason": "missing_result" }))
    );

    // A head between a call and its results leaves stray results that are not sent.
    append_to(
        &setup.root,
        draft("reset", |draft| {
            draft.head = Some(EntryHead::Entry(second.id));
        }),
    )
    .await;
    let parent_view = setup.root.context(context()).await.unwrap();
    assert!(parent_view.messages.is_empty());
    let kinds: Vec<&str> = parent_view
        .entries
        .iter()
        .map(|entry| entry.kind.as_str())
        .collect();
    assert_eq!(kinds, ["reset", "message"]);
}
