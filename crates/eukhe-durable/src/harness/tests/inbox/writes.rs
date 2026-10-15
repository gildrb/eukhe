//! Display-only writes (pi-durable 1.2: appended and settled at once, busy
//! or not, unless a reset is queued) and input entries (`InputEntry`).

use eukhe_types::input_origin::InputOrigin;
use eukhe_types::pi_ai::UserMessage;

use super::*;
use crate::harness::types::InputEntry;
use crate::session::SessionError;
use crate::types::WriteSubmission;

fn shown_note() -> EntryDraft {
    let mut draft = EntryDraft::new("note");
    draft.data = Some(json(r#""shown""#));
    draft
}

fn card(author: &str) -> InputEntry {
    InputEntry {
        kind: "card".to_owned(),
        data: Some(json(&format!(r#"{{"author":"{author}"}}"#))),
    }
}

fn with_entry(text: &str, entry: InputEntry) -> InputSubmissionDraft {
    InputSubmissionDraft {
        entry: Some(entry),
        ..InputSubmissionDraft::new(text)
    }
}

async fn inbox_state(harness: &Harness, root: &Conversation) -> InboxState {
    let value = harness
        .snapshot(&INBOX_DOC, root.id(), context())
        .await
        .unwrap()
        .unwrap();
    from_json(&JsonValue::Object(value)).unwrap()
}

fn done(entry: EntryId) -> SubmissionState {
    SubmissionState::Write(WriteSubmission::Done { entry })
}

#[tokio::test]
async fn settles_a_display_only_write_at_once_while_busy_ahead_of_the_queued_input_s_answer() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let first = gated(answer("first"));
    setup
        .faux
        .set_responses(vec![first.step.clone(), answer("second").into()]);
    let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
    let input_submission = submit(&root, input("a")).await;
    first.reached().await;
    let f = submit(&root, input("f")).await;
    let shown = submit(&root, write(shown_note())).await;
    let entries = all_entries(&root, context()).await.unwrap();
    let note = entries.last().unwrap();
    assert_eq!(
        (note.kind.as_str(), note.data.clone()),
        ("note", Some(json(r#""shown""#)))
    );
    assert_eq!(status(&shown).await.state, done(note.id));
    assert_eq!(transcript(&entries), ["pi.user:a", "note"]);
    assert_eq!(inbox(&harness, &root).await, vec![(f.id(), "followUp")]);

    first.release();
    settle(&f).await;
    assert_eq!(
        transcript(&all_entries(&root, context()).await.unwrap()),
        [
            "pi.user:a",
            "note",
            "pi.assistant:first",
            "pi.user:f",
            "pi.assistant:second"
        ]
    );
    assert_done(&status(&input_submission).await, None);
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn queues_a_display_only_write_behind_a_queued_reset_so_it_lands_after_the_reset() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let first = gated(answer("first"));
    setup.faux.set_responses(vec![first.step.clone()]);
    let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
    let input_submission = submit(&root, input("a")).await;
    first.reached().await;
    let mut restart = EntryDraft::new("restart");
    restart.head = Some(EntryHead::SelfEntry);
    let reset = submit(&root, write(restart)).await;
    let shown = submit(&root, write(shown_note())).await;
    assert_eq!(
        status(&shown).await.state,
        SubmissionState::Write(WriteSubmission::Queued)
    );
    assert_eq!(
        inbox(&harness, &root).await,
        vec![(reset.id(), "write"), (shown.id(), "write")]
    );

    first.release();
    settle(&input_submission).await;
    harness.wait_for_idle(context()).await.unwrap();
    let entries = all_entries(&root, context()).await.unwrap();
    assert_eq!(
        last(&transcript(&entries), 2),
        ["restart".to_owned(), "note".to_owned()]
    );
    assert_eq!(status(&shown).await.state, done(entries.last().unwrap().id));
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn a_display_only_write_after_a_failed_run_leaves_the_queued_items_queued() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let failing = gated(failure("invalid request"));
    setup
        .faux
        .set_responses(vec![failing.step.clone(), answer("for f").into()]);
    let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
    let input_submission = submit(&root, input("a")).await;
    failing.reached().await;
    let f = submit(&root, input("f")).await;
    failing.release();
    assert_unanswered(&settle(&input_submission).await, "model_error");
    harness.wait_for_idle(context()).await.unwrap();

    let shown = submit(&root, write(shown_note())).await;
    let entries = all_entries(&root, context()).await.unwrap();
    assert_eq!(status(&shown).await.state, done(entries.last().unwrap().id));
    assert_eq!(
        status(&f).await.state,
        SubmissionState::Input(InputSubmission::Queued)
    );
    assert_eq!(inbox(&harness, &root).await, vec![(f.id(), "followUp")]);
    assert_eq!(live(&harness, &root).await, Some(LiveState::default()));
    assert_eq!(setup.faux.state().call_count, 1);
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn places_an_input_with_an_entry_as_that_kind_with_its_user_message_idle_and_queued() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let first = gated(answer("first"));
    setup
        .faux
        .set_responses(vec![first.step.clone(), answer("second").into()]);
    let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
    let input_submission = submit(&root, with_entry("a", card("ann"))).await;
    first.reached().await;
    let f = submit(&root, with_entry("f", card("bob"))).await;
    assert_eq!(
        inbox_state(&harness, &root).await,
        InboxState {
            items: vec![InboxItem::FollowUp {
                id: f.id(),
                content: "f".into(),
                entry: Some(card("bob")),
                origin: InputOrigin::User,
            }],
        }
    );

    first.release();
    settle(&f).await;
    let entries = all_entries(&root, context()).await.unwrap();
    assert_eq!(
        transcript(&entries),
        [
            "card:a",
            "pi.assistant:first",
            "card:f",
            "pi.assistant:second"
        ]
    );
    let placed: Vec<(EntryId, Option<JsonValue>, Option<Vec<Message>>)> = entries
        .iter()
        .filter(|entry| entry.kind == "card")
        .map(|entry| (entry.id, entry.data.clone(), entry.model.clone()))
        .collect();
    let user = |text: &str, entry: &EntryRecord| {
        let timestamp = match entry.model.as_deref() {
            Some([Message::User(message)]) => message.timestamp,
            other => panic!("one user message expected: {other:?}"),
        };
        Some(vec![Message::User(UserMessage {
            content: text.into(),
            timestamp,
        })])
    };
    let cards: Vec<&EntryRecord> = entries
        .iter()
        .filter(|entry| entry.kind == "card")
        .collect();
    assert_eq!(
        placed,
        vec![
            (cards[0].id, card("ann").data, user("a", cards[0])),
            (cards[1].id, card("bob").data, user("f", cards[1])),
        ]
    );
    assert_done(&status(&input_submission).await, None);
    assert_done(&status(&f).await, None);
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn rejects_an_input_entry_with_a_reserved_or_empty_kind() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
    let before = all_entries(&root, context()).await.unwrap();
    for kind in ["pi.user", ""] {
        let entry = InputEntry {
            kind: kind.to_owned(),
            data: None,
        };
        let error = root
            .submit(with_entry("a", entry), context())
            .await
            .unwrap_err();
        assert!(
            matches!(&error, SessionError::Type(message) if **message == *format!(
                "An input entry's kind must be a non-empty string not starting with \"pi.\", got {kind}"
            )),
            "{error:?}"
        );
    }
    assert_eq!(all_entries(&root, context()).await.unwrap(), before);
    harness.close(context()).await.unwrap();
}
