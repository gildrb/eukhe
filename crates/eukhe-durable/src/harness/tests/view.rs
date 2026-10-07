//! Port of `test/harness-view.test.ts`.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::{with_cancel, Context};
use eukhe_chord::delta::{apply_immutable, Op, Seg};
use eukhe_chord::json::{to_json, JsonObject, JsonValue};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_text, FauxAssistantMessageOptions, FauxResponseStep,
    RegisterFauxProviderOptions,
};
use eukhe_types::pi_ai::{AssistantMessage, ModelThinkingLevel};
use futures::FutureExt;

use super::chat_support::{all_entries, chat_setup, open_chat, wait_for, OpenChat};
use super::support::context;
use super::task_support::{deferred, flush, Deferred};
use crate::documents::{ConversationDoc, DocDefinition};
use crate::harness::agent::AGENT_DOC;
use crate::harness::inbox::INBOX_DOC;
use crate::harness::live::LIVE_DOC;
use crate::harness::provider::PROVIDER_DOC;
use crate::harness::types::{
    AgentChange, ConversationCreateOptions, FieldChange, InputSubmissionDraft,
};
use crate::harness::usage::USAGE_DOC;
use crate::harness::{Conversation, ConversationView, ConversationWatch, Harness};
use crate::session::{Ops, SessionError, WatchEnd, WatchListenerError};
use crate::storage::MemoryStorage;
use crate::types::{
    CommitChange, ConversationOwnership, DocumentCommitChange, EntryDraft, EntryHead, EntryRecord,
    LatestFork, Storage,
};

type Frames = Arc<Mutex<Vec<(ConversationView, Ops)>>>;

const MOUNTED: [&str; 5] = ["pi.agent", "pi.inbox", "pi.live", "pi.provider", "pi.usage"];

fn storage() -> Arc<dyn Storage> {
    Arc::new(MemoryStorage::new())
}

fn frames_of(frames: &Frames) -> Vec<(ConversationView, Ops)> {
    frames
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
}

fn json(text: &str) -> JsonValue {
    JsonValue::parse(text).expect("valid JSON literal")
}

fn ops_json(ops: &[Op]) -> JsonValue {
    ops.iter().map(Op::to_json).collect()
}

/// Start `watch`, recording every delivered frame.
fn start(watch: &ConversationWatch) -> Frames {
    let frames: Frames = Arc::default();
    let sink = Arc::clone(&frames);
    watch
        .start(Arc::new(move |value, ops, _| {
            sink.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push((value, ops));
            async { Ok(()) }.boxed()
        }))
        .unwrap();
    frames
}

/// A started watch of `conversation`: its acquisition revision and every delivered frame.
async fn record(conversation: &Conversation) -> (ConversationView, Frames, ConversationWatch) {
    let watch = conversation.watch(context()).await.unwrap();
    let initial = watch.value();
    let frames = start(&watch);
    (initial, frames, watch)
}

/// A freshly built view of `conversation`, as JSON.
async fn fresh(conversation: &Conversation) -> JsonValue {
    let state = conversation.view_state(context()).await.unwrap();
    let value = state.value();
    state.dispose().unwrap();
    value
}

/// The view as committed state defines it, read without any mount.
async fn committed(
    harness: &Harness,
    conversation: &Conversation,
    record: &ConversationView,
) -> JsonValue {
    let id = conversation.id();
    let cx = context();
    let mut docs = JsonObject::new();
    let loaded = [
        (
            "pi.agent",
            harness.snapshot(&AGENT_DOC, id, cx).await.unwrap(),
        ),
        (
            "pi.live",
            harness.snapshot(&LIVE_DOC, id, cx).await.unwrap(),
        ),
        (
            "pi.inbox",
            harness.snapshot(&INBOX_DOC, id, cx).await.unwrap(),
        ),
        (
            "pi.provider",
            harness.snapshot(&PROVIDER_DOC, id, cx).await.unwrap(),
        ),
        (
            "pi.usage",
            harness.snapshot(&USAGE_DOC, id, cx).await.unwrap(),
        ),
    ];
    for (kind, value) in loaded {
        if let Some(value) = value {
            docs.insert(kind, JsonValue::Object(value));
        }
    }
    let entries = conversation.context(cx).await.unwrap().entries;
    let mut root = JsonObject::new();
    root.insert("conversation", to_json(record.conversation()).unwrap());
    root.insert("entries", to_json(&entries).unwrap());
    root.insert("docs", JsonValue::Object(Arc::new(docs)));
    JsonValue::Object(Arc::new(root))
}

/// Replay every frame's operations from `initial`, checking each delivered revision on the way.
fn replay(initial: &ConversationView, frames: &[(ConversationView, Ops)]) -> JsonValue {
    let mut value = initial.to_json_value();
    for (frame, ops) in frames {
        value = apply_immutable(&value, ops).unwrap();
        assert_eq!(value, frame.to_json_value());
    }
    value
}

fn answer(text: &str) -> AssistantMessage {
    faux_assistant_message(
        vec![faux_text(text)],
        FauxAssistantMessageOptions::default(),
    )
}

fn kinds(entries: &[EntryRecord]) -> Vec<&str> {
    entries.iter().map(|entry| entry.kind.as_str()).collect()
}

async fn note(conversation: &Conversation, kind: &'static str) -> EntryRecord {
    note_with(conversation, EntryDraft::new(kind)).await
}

async fn note_with(conversation: &Conversation, draft: EntryDraft) -> EntryRecord {
    let id = conversation.id();
    conversation
        .commit(
            move |tx| async move { tx.append_entry(id, draft).await },
            context(),
        )
        .await
        .unwrap()
}

fn head(kind: &str, target: crate::types::EntryId) -> EntryDraft {
    let mut draft = EntryDraft::new(kind);
    draft.head = Some(EntryHead::Entry(target));
    draft
}

/// Counts commits that touch `conversation`'s mount.
fn touches(harness: &Harness, conversation: &Conversation) -> Arc<Mutex<usize>> {
    let counter = Arc::new(Mutex::new(0));
    let sink = Arc::clone(&counter);
    let id = conversation.id();
    let subscription = harness
        .subscribe_commits(Arc::new(move |publication, _| {
            let touched = publication.changes.iter().any(|change| match change {
                CommitChange::Entry(entry) => entry.conversation_id == id,
                CommitChange::Document(DocumentCommitChange::Document {
                    record,
                    conversation_id,
                    ops,
                    ..
                }) => {
                    *conversation_id == Some(id)
                        && MOUNTED.contains(&record.kind.as_str())
                        && !ops.is_empty()
                }
                CommitChange::Document(DocumentCommitChange::Copy { .. })
                | CommitChange::Conversation(_)
                | CommitChange::Task(_)
                | CommitChange::Submission(_) => false,
            });
            if touched {
                *sink.lock().unwrap_or_else(PoisonError::into_inner) += 1;
            }
        }))
        .unwrap();
    drop(subscription);
    counter
}

/// Faux step held until `release` or the request's abort.
fn held(release: &Deferred, message: AssistantMessage) -> FauxResponseStep {
    let release = release.clone();
    FauxResponseStep::Factory(Arc::new(move |_, options, _, _| {
        let signal = options.and_then(|options| options.stream.request.signal.clone());
        let (release, message) = (release.clone(), message.clone());
        async move {
            if let Some(signal) = signal {
                tokio::select! {
                    () = release.wait() => Ok(message),
                    reason = signal.cancelled() => Err(reason),
                }
            } else {
                release.wait().await;
                Ok(message)
            }
        }
        .boxed()
    }))
}

fn input(text: &str) -> InputSubmissionDraft {
    InputSubmissionDraft::new(text)
}

#[tokio::test]
async fn hydrates_the_active_entries_and_the_built_in_documents() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    setup.faux.set_responses(vec![answer("hello").into()]);
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    root.submit(input("hi"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    let view = fresh(&root).await;
    assert_eq!(
        view["conversation"],
        json(&format!(r#"{{"id":{}}}"#, root.id()))
    );
    assert_eq!(
        view["entries"],
        to_json(&all_entries(&root, context()).await.unwrap()).unwrap()
    );
    let mut keys: Vec<&str> = view["docs"].as_object().unwrap().keys().collect();
    keys.sort_unstable();
    assert_eq!(keys, MOUNTED);
    assert_eq!(view["docs"]["pi.live"], json("{}"));
    assert_eq!(view["docs"]["pi.inbox"], json(r#"{"items":[]}"#));
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn publishes_one_frame_per_touching_commit_whose_operations_rebuild_every_revision() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let release = deferred();
    setup
        .faux
        .set_responses(vec![held(&release, answer("a longer answer"))]);
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let (initial, frames, watch) = record(&root).await;
    let touching = touches(&harness, &root);
    let submission = root.submit(input("hi"), context()).await.unwrap();
    wait_for(
        || {
            let found = frames_of(&frames).iter().any(|(value, _)| {
                value
                    .doc("pi.live")
                    .is_some_and(|live| live.get("generation").is_some())
            });
            async move { found }
        },
        5000,
    )
    .await;
    release.resolve(());
    submission.wait(context()).await.unwrap();
    harness.wait_for_idle(context()).await.unwrap();
    flush().await;
    let delivered = frames_of(&frames);
    assert_eq!(
        delivered.len(),
        *touching.lock().unwrap_or_else(PoisonError::into_inner)
    );
    assert_eq!(
        replay(&initial, &delivered),
        committed(&harness, &root, &initial).await
    );
    let first = ops_json(&delivered[0].1);
    assert!(
        first
            .as_array()
            .unwrap()
            .iter()
            .any(|op| op[0] == json(r#""p""#)
                && op[1] == json(r#"["entries"]"#)
                && op[2] == json("0")
                && op[3] == json("0")
                && op[4][0]["kind"] == json(r#""pi.user""#)),
        "{first}"
    );
    // Document operations keep their exact shape under the mount path.
    let expected = Op::Set(
        vec![
            Seg::from("docs"),
            Seg::from("pi.live"),
            Seg::from("generation"),
        ],
        json(r#"{"attempt":1}"#),
    );
    assert!(delivered
        .iter()
        .flat_map(|(_, ops)| ops.iter())
        .any(|op| *op == expected));
    watch.stop().await;
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn shares_unchanged_parts_between_revisions_and_skips_commits_that_touch_nothing_mounted() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let other = harness
        .create_conversation(
            ConversationCreateOptions::new(ConversationOwnership::Ownerless),
            context(),
        )
        .await
        .unwrap();
    let (initial, frames, watch) = record(&root).await;
    note(&other, "note").await;
    root.configure(
        AgentChange {
            thinking_level: FieldChange::Set(ModelThinkingLevel::High),
            ..AgentChange::default()
        },
        context(),
    )
    .await
    .unwrap();
    note(&root, "note").await;
    flush().await;
    let delivered = frames_of(&frames);
    assert_eq!(delivered.len(), 2);
    assert_eq!(
        ops_json(&delivered[0].1),
        json(r#"[["s",["docs","pi.agent","thinkingLevel"],"high"]]"#)
    );
    assert!(Arc::ptr_eq(delivered[0].0.entries(), initial.entries()));
    assert!(delivered[0]
        .0
        .doc("pi.live")
        .unwrap()
        .strict_equals(initial.doc("pi.live").unwrap()));
    assert!(Arc::ptr_eq(delivered[1].0.docs(), delivered[0].0.docs()));
    watch.stop().await;
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn cuts_the_entries_at_a_head_marker_keeping_the_entries_from_its_head() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    note(&root, "a").await;
    let b = note(&root, "b").await;
    note(&root, "c").await;
    let (initial, frames, watch) = record(&root).await;
    let summary = note_with(&root, head("summary", b.id)).await;
    note(&root, "d").await;
    root.reset(None, context()).await.unwrap();
    flush().await;
    let delivered = frames_of(&frames);
    let kinds: Vec<Vec<&str>> = delivered
        .iter()
        .map(|(value, _)| kinds(value.entries()))
        .collect();
    assert_eq!(
        kinds,
        vec![
            vec!["summary", "b", "c"],
            vec!["summary", "b", "c", "d"],
            vec!["pi.reset"]
        ]
    );
    assert_eq!(
        *delivered[0].1,
        [Op::Splice(
            vec![Seg::from("entries")],
            0,
            1,
            vec![to_json(&summary).unwrap()]
        )]
    );
    assert_eq!(
        replay(&initial, &delivered),
        committed(&harness, &root, &initial).await
    );
    watch.stop().await;
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn keeps_only_mounted_entries_for_a_raw_head_write_that_targets_before_the_active_range() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let old = note(&root, "old").await;
    root.reset(None, context()).await.unwrap();
    let (_, frames, watch) = record(&root).await;
    note_with(&root, head("summary", old.id)).await;
    flush().await;
    // Model context now starts at `old` again, but the mount never held it (spec §12); a rebuilt mount shows it.
    assert_eq!(kinds(frames_of(&frames)[0].0.entries()), ["summary"]);
    watch.stop().await;
    let rebuilt: Vec<String> = fresh(&root).await["entries"]
        .as_array()
        .unwrap()
        .iter()
        .map(|entry| entry["kind"].as_str().unwrap().to_owned())
        .collect();
    assert_eq!(rebuilt, ["summary", "old"]);
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn cuts_a_forks_view_into_its_inherited_entries() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let a = note(&root, "a").await;
    let b = note(&root, "b").await;
    let fork = root
        .fork(
            b.id,
            ConversationCreateOptions::new(ConversationOwnership::Ownerless),
            context(),
        )
        .await
        .unwrap();
    let (initial, frames, watch) = record(&fork).await;
    note_with(&fork, head("summary", b.id)).await;
    flush().await;
    let ids: Vec<_> = initial.entries().iter().map(|entry| entry.id).collect();
    assert_eq!(ids, [a.id, b.id]);
    let delivered = frames_of(&frames);
    assert_eq!(kinds(delivered[0].0.entries()), ["summary", "b"]);
    assert_eq!(
        delivered[0].0.to_json_value(),
        committed(&harness, &fork, &initial).await
    );
    watch.stop().await;
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn shows_a_forks_inherited_entries_and_follows_only_the_forks_own_commits() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let first = note(&root, "first").await;
    let fork = root
        .fork(
            first.id,
            ConversationCreateOptions::new(ConversationOwnership::Ownerless),
            context(),
        )
        .await
        .unwrap();
    let (initial, frames, watch) = record(&fork).await;
    assert_eq!(kinds(initial.entries()), ["first"]);
    let parent = initial.conversation().parent.as_ref().unwrap();
    assert_eq!((parent.conversation_id, parent.at), (root.id(), first.id));
    note(&root, "parent").await;
    note(&fork, "child").await;
    flush().await;
    let delivered = frames_of(&frames);
    let kinds: Vec<Vec<&str>> = delivered
        .iter()
        .map(|(value, _)| kinds(value.entries()))
        .collect();
    assert_eq!(kinds, vec![vec!["first", "child"]]);
    watch.stop().await;
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn unmounts_a_retired_document_and_mounts_its_recreation_whole() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let (_, frames, watch) = record(&root).await;
    let id = root.id();
    root.commit(
        move |tx| async move { tx.retire_doc(&LIVE_DOC, id).await },
        context(),
    )
    .await
    .unwrap();
    root.commit(
        move |tx| async move {
            tx.doc(&LIVE_DOC, id)
                .await?
                .set("tools", JsonValue::array())?;
            Ok(())
        },
        context(),
    )
    .await
    .unwrap();
    flush().await;
    let delivered = frames_of(&frames);
    let ops: Vec<JsonValue> = delivered.iter().map(|(_, ops)| ops_json(ops)).collect();
    assert_eq!(
        ops,
        [
            json(r#"[["d",["docs","pi.live"]]]"#),
            json(r#"[["s",["docs","pi.live"],{"tools":[]}]]"#)
        ]
    );
    assert!(delivered[0].0.doc("pi.live").is_none());
    watch.stop().await;
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn replaces_undelivered_frames_with_the_newest_view_after_100_pending_frames() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let watch = root.watch(context()).await.unwrap();
    for _ in 0..101 {
        note(&root, "note").await;
    }
    let frames = start(&watch);
    flush().await;
    let delivered = frames_of(&frames);
    assert_eq!(delivered.len(), 1);
    assert_eq!(
        *delivered[0].1,
        [Op::Replace(delivered[0].0.to_json_value())]
    );
    assert_eq!(delivered[0].0.entries().len(), 101);
    watch.stop().await;
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn keeps_states_and_watches_of_one_conversation_independent_and_remounts_after_the_last_one_detaches(
) {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let state = root.view_state(context()).await.unwrap();
    let (_, frames, watch) = record(&root).await;
    let state_kinds = |state: &eukhe_chord::AttachedReplicatedState| -> Vec<String> {
        state.value()["entries"]
            .as_array()
            .unwrap()
            .iter()
            .map(|entry| entry["kind"].as_str().unwrap().to_owned())
            .collect()
    };
    note(&root, "one").await;
    flush().await;
    assert_eq!(state_kinds(&state), ["one"]);
    watch.stop().await;
    assert_eq!(frames_of(&frames).len(), 1);
    note(&root, "two").await;
    flush().await;
    assert_eq!(state_kinds(&state), ["one", "two"]);
    let last = state.value();
    state.dispose().unwrap();
    // No observer is left, so the mount was dropped: a new observer builds a new revision from committed state.
    let rebuilt = fresh(&root).await;
    assert_eq!(rebuilt, last);
    assert!(!rebuilt.strict_equals(&last));
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn ends_states_and_watches_at_close_and_rejects_later_acquisition() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let watch = root.watch(context()).await.unwrap();
    let state = root.view_state(context()).await.unwrap();
    harness.close(context()).await.unwrap();
    assert_eq!(watch.closed().await, WatchEnd::SessionClosed);
    assert_eq!(state.value()["entries"], json("[]"));
    assert!(root.watch(context()).await.is_err());
    assert!(root.view_state(context()).await.is_err());
}

/// A commit of `root` held on the Session line until released.
fn hold(root: &Conversation) -> (Deferred, tokio::task::JoinHandle<Result<(), SessionError>>) {
    let release: Deferred = deferred();
    let gate = release.clone();
    let blocking = tokio::spawn(root.commit(
        move |_tx| async move {
            gate.wait().await;
            Ok(())
        },
        context(),
    ));
    (release, blocking)
}

#[tokio::test]
async fn rejects_an_acquisition_cancelled_or_closed_while_it_waits_for_the_session_line() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let (release, blocking) = hold(&root);
    flush().await;
    let (child, cancel): (Context, _) = with_cancel(context());
    let cancelled = tokio::spawn(root.watch(&child));
    cancel.cancel(Some(Arc::new(std::io::Error::other("cancelled"))));
    release.resolve(());
    blocking.await.unwrap().unwrap();
    let error = cancelled.await.unwrap().unwrap_err();
    assert!(error.to_string().contains("cancelled"), "{error}");

    let (release, blocking) = hold(&root);
    flush().await;
    let closed_while_queued = tokio::spawn(root.watch(context()));
    flush().await;
    let closing = tokio::spawn(harness.close(context()));
    flush().await;
    release.resolve(());
    blocking.await.unwrap().unwrap();
    let error = closed_while_queued.await.unwrap().unwrap_err();
    assert!(error.to_string().contains("Harness is closed"), "{error}");
    closing.await.unwrap().unwrap();
}

#[tokio::test]
async fn shares_one_mount_between_concurrent_observers_and_isolates_a_failing_listener() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let failing = root.watch(context()).await.unwrap();
    let (_, frames, watch) = record(&root).await;
    let shared = root.view_state(context()).await.unwrap();
    assert!(failing
        .value()
        .to_json_value()
        .strict_equals(&shared.value()));
    shared.dispose().unwrap();
    failing
        .start(Arc::new(|_, _, _| {
            async { Err(Arc::new(std::io::Error::other("listener failed")) as WatchListenerError) }
                .boxed()
        }))
        .unwrap();
    note(&root, "one").await;
    note(&root, "two").await;
    flush().await;
    assert_eq!(failing.closed().await.reason(), "listener_error");
    assert_eq!(frames_of(&frames).len(), 2);
    watch.stop().await;
    harness.close(context()).await.unwrap();
}

static OTHER_DOC: ConversationDoc<JsonValue> = match ConversationDoc::define(
    DocDefinition {
        kind: "app.other",
        version: 1,
        initial: || JsonValue::parse(r#"{"n":0}"#).expect("valid JSON literal"),
        migrate: None,
        checkpoint_when: None,
    },
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("valid definition"),
};

#[tokio::test]
async fn publishes_one_frame_for_a_commit_that_appends_several_entries_and_edits_a_document() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let (initial, frames, watch) = record(&root).await;
    let id = root.id();
    root.commit(
        move |tx| async move {
            tx.append_entry(id, EntryDraft::new("a")).await?;
            tx.doc(&LIVE_DOC, id)
                .await?
                .set("tools", JsonValue::array())?;
            tx.append_entry(id, EntryDraft::new("b")).await?;
            Ok(())
        },
        context(),
    )
    .await
    .unwrap();
    // A document that is not mounted publishes nothing.
    root.commit(
        move |tx| async move {
            tx.doc(&OTHER_DOC, id).await?.set("n", JsonValue::from(1))?;
            Ok(())
        },
        context(),
    )
    .await
    .unwrap();
    flush().await;
    let delivered = frames_of(&frames);
    assert_eq!(delivered.len(), 1);
    assert_eq!(kinds(delivered[0].0.entries()), ["a", "b"]);
    assert_eq!(
        replay(&initial, &delivered),
        committed(&harness, &root, &initial).await
    );
    watch.stop().await;
    harness.close(context()).await.unwrap();
}
