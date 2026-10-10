//! Port of `test/harness-conversations.test.ts`.

use std::future::Future;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::json::{from_json, to_json, JsonObject, JsonValue};
use eukhe_types::pi_ai::{Message, ModelThinkingLevel};
use futures::FutureExt;

use super::chat_support::text_of;
use super::support::{
    add_tool, context, create_models, create_registry, open_harness, tool, user, OpenHarnessOptions,
};
use crate::documents::{DocDefinition, RewindableConversationDoc};
use crate::entries::Entry;
use crate::harness::agent::{configure, AGENT_DOC};
use crate::harness::define::define_extension;
use crate::harness::live::LIVE_DOC;
use crate::harness::provider::PROVIDER_DOC;
use crate::harness::types::{
    AgentChange, AgentState, ConversationCreateOptions, ConversationInit, Extension, FieldChange,
    HarnessOptions, ModelRef, ToolFilter, ToolsChange,
};
use crate::harness::{Conversation, ConversationEntryQuery, Harness, RootOptions};
use crate::session::tests::support::ControlledStorage;
use crate::session::{create_session, DocumentState, SessionError, SessionResult, Tx};
use crate::storage::sqlite::{open_native_sqlite_storage, NativeSqliteStorageOptions};
use crate::storage::MemoryStorage;
use crate::tasks::{define_task, Task, TaskDefinition};
use crate::types::{
    ConversationId, ConversationOwnership, ConversationRecord, Cursor, EntryDraft, EntryRecord,
    RewindableFork, ScanOrder, Storage, TaskId, TaskOptions, TaskOwnership, ROOT_CONVERSATION_ID,
};

type JsonTask = Task<JsonValue, JsonValue, JsonValue, ()>;

fn json(text: &str) -> JsonValue {
    JsonValue::parse(text).expect("valid JSON literal")
}

fn object(text: &str) -> Arc<JsonObject> {
    match json(text) {
        JsonValue::Object(object) => object,
        other => panic!("not an object literal: {other}"),
    }
}

/// TS `UUID_V7` regex: `^[0-9a-f]{8}-[0-9a-f]{4}-7[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$`.
fn is_uuid_v7(text: &str) -> bool {
    let bytes = text.as_bytes();
    bytes.len() == 36
        && bytes.iter().enumerate().all(|(index, byte)| match index {
            8 | 13 | 18 | 23 => *byte == b'-',
            14 => *byte == b'7',
            19 => matches!(byte, b'8' | b'9' | b'a' | b'b'),
            _ => matches!(byte, b'0'..=b'9' | b'a'..=b'f'),
        })
}

/// A sqlite path in a fresh temp directory; the directory lives as long as
/// the returned guard (TS `afterEach` removes it).
fn sqlite_path() -> (tempfile::TempDir, std::path::PathBuf) {
    let directory = tempfile::Builder::new()
        .prefix("pi-durable-harness-")
        .tempdir()
        .expect("temp dir");
    let path = directory.path().join("session.sqlite");
    (directory, path)
}

async fn sqlite(path: &std::path::Path) -> Arc<dyn Storage> {
    Arc::new(
        open_native_sqlite_storage(path, NativeSqliteStorageOptions::default())
            .await
            .expect("open sqlite storage"),
    )
}

const NOTE_DOC: RewindableConversationDoc<JsonValue> = match RewindableConversationDoc::define(
    DocDefinition {
        kind: "test.note",
        version: 1,
        initial: || json(r#"{"text":""}"#),
        migrate: None,
        checkpoint_when: None,
    },
    RewindableFork::AsOf,
) {
    Ok(token) => token,
    Err(_) => panic!("valid definition"),
};

const MESSAGE: Entry = match Entry::define("message") {
    Ok(token) => token,
    Err(_) => panic!("valid entry kind"),
};

fn ownerless() -> ConversationCreateOptions {
    ConversationCreateOptions::new(ConversationOwnership::Ownerless)
}

#[expect(
    clippy::unnecessary_wraps,
    reason = "mirrors the optional TS `init` field it fills"
)]
fn init<F, Fut>(init: F) -> Option<ConversationInit>
where
    F: FnOnce(Tx, ConversationId) -> Fut + Send + 'static,
    Fut: Future<Output = SessionResult<()>> + Send + 'static,
{
    Some(Box::new(move |tx, id| init(tx, id).boxed()))
}

/// TS `init: () => expect.unreachable()`.
fn unreachable_init() -> Option<ConversationInit> {
    init(|_, _| async { Err(SessionError::error("init must not run")) })
}

fn message_draft(text: &str) -> EntryDraft {
    let mut draft = EntryDraft::new("message");
    draft.model = Some(vec![Message::User(user(text))]);
    draft
}

async fn append(conversation: &Conversation, text: &str) -> EntryRecord {
    let id = conversation.id();
    let draft = message_draft(text);
    conversation
        .commit(
            move |tx| async move { tx.append_entry(id, draft).await },
            context(),
        )
        .await
        .unwrap()
}

/// Texts of every entry, newest first, paging two at a time.
async fn all_entries(conversation: &Conversation) -> Vec<String> {
    entries_in(conversation, None).await
}

/// Texts of every entry in `order`, paging two at a time (TS
/// `allEntries(conversation, order)`).
async fn entries_in(conversation: &Conversation, order: Option<ScanOrder>) -> Vec<String> {
    let mut texts = Vec::new();
    let mut cursor: Option<Cursor> = None;
    loop {
        let query = ConversationEntryQuery {
            order,
            ..ConversationEntryQuery::default()
        };
        let page = conversation
            .entries(query, 2, cursor, context())
            .await
            .unwrap();
        for entry in &page.items {
            texts.push(text_of(entry.model.as_ref().and_then(|model| model.first())).unwrap());
        }
        cursor = page.next;
        if cursor.is_none() {
            break;
        }
    }
    texts
}

async fn agent_state(harness: &Harness, id: ConversationId) -> Option<AgentState> {
    harness
        .snapshot(&AGENT_DOC, id, context())
        .await
        .unwrap()
        .map(|value| from_json(&JsonValue::Object(value)).unwrap())
}

async fn provider_session_id(harness: &Harness, id: ConversationId) -> Option<String> {
    harness
        .snapshot(&PROVIDER_DOC, id, context())
        .await
        .unwrap()
        .and_then(|value| {
            value
                .get("sessionId")
                .and_then(JsonValue::as_str)
                .map(str::to_owned)
        })
}

fn tool_names(tools: &[Arc<crate::harness::types::ToolRegistration>]) -> Vec<String> {
    tools.iter().map(|each| each.name.clone()).collect()
}

fn model(provider: &str, model_id: &str) -> ModelRef {
    ModelRef {
        provider: provider.to_owned(),
        model_id: model_id.to_owned(),
    }
}

fn task_options() -> TaskOptions {
    TaskOptions {
        ownership: TaskOwnership::Conversation,
        conversation_id: None,
        background: None,
        abandon_on_restart: None,
    }
}

/// A task with one phase that does nothing and an abort that does nothing.
fn idle_task(name: &str, phase: &str) -> JsonTask {
    let checkpoint = json(&format!(r#"{{"phase":"{phase}"}}"#));
    define_task(
        TaskDefinition::new(
            name,
            1,
            move |_: &JsonValue| Ok(checkpoint.clone()),
            |_, _, _| async { Ok(()) },
        )
        .phase(phase, |_, _, _| async { Ok(()) }),
    )
}

// Harness root and conversations

#[tokio::test]
#[expect(clippy::too_many_lines, reason = "one TS case, ported whole")]
async fn creates_the_root_lazily_with_its_agent_change_and_init_in_one_commit() {
    let storage = ControlledStorage::new();
    let (harness, _registry) = open_harness(
        Arc::clone(&storage) as Arc<dyn Storage>,
        &["read", "bash"],
        OpenHarnessOptions::default(),
    )
    .await
    .unwrap();
    assert_eq!(storage.commit_count(), 0);
    let seen = Arc::new(Mutex::new(None));
    let sink = Arc::clone(&seen);
    let root = harness
        .root(
            RootOptions {
                agent: Some(AgentChange {
                    thinking_level: FieldChange::Set(ModelThinkingLevel::High),
                    ..AgentChange::default()
                }),
                init: init(move |tx, id| async move {
                    // The agent change applied before init.
                    let agent = tx.doc(&AGENT_DOC, id).await?.value()?;
                    *sink.lock().unwrap_or_else(PoisonError::into_inner) =
                        agent.get("thinkingLevel").cloned();
                    tx.doc(&NOTE_DOC, id).await?.set("text", "root note")?;
                    Ok(())
                }),
            },
            context(),
        )
        .await
        .unwrap();
    assert_eq!(
        *seen.lock().unwrap_or_else(PoisonError::into_inner),
        Some(json(r#""high""#))
    );
    assert_eq!(root.id(), ROOT_CONVERSATION_ID);
    assert_eq!(storage.commit_count(), 1);
    // Conversation, five built-in documents, and the init note.
    let types: Vec<String> = storage.commits()[0]
        .iter()
        .map(|write| {
            to_json(write)
                .unwrap()
                .get("type")
                .and_then(JsonValue::as_str)
                .unwrap()
                .to_owned()
        })
        .collect();
    assert_eq!(
        types,
        [
            "conversation",
            "document.create",
            "document.create",
            "document.create",
            "document.create",
            "document.create",
            "document.create",
        ]
    );
    assert_eq!(
        harness
            .snapshot(&LIVE_DOC, root.id(), context())
            .await
            .unwrap(),
        Some(object("{}"))
    );
    let provider = harness
        .snapshot(&PROVIDER_DOC, root.id(), context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(provider.len(), 1);
    assert!(is_uuid_v7(
        provider
            .get("sessionId")
            .and_then(JsonValue::as_str)
            .unwrap()
    ));
    assert_eq!(
        agent_state(&harness, root.id()).await,
        Some(AgentState {
            thinking_level: Some(ModelThinkingLevel::High),
            ..AgentState::default()
        })
    );
    let agent = root.agent(context()).await.unwrap();
    assert_eq!(agent.thinking_level, ModelThinkingLevel::High);
    assert_eq!(tool_names(&agent.tools), ["read", "bash"]);
    assert_eq!(
        harness
            .snapshot(&NOTE_DOC, root.id(), context())
            .await
            .unwrap(),
        Some(object(r#"{"text":"root note"}"#))
    );

    let again = harness
        .root(
            RootOptions {
                agent: Some(AgentChange {
                    thinking_level: FieldChange::Set(ModelThinkingLevel::Low),
                    ..AgentChange::default()
                }),
                init: unreachable_init(),
            },
            context(),
        )
        .await
        .unwrap();
    assert_eq!(again.id(), root.id());
    assert_eq!(storage.commit_count(), 1);
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn keeps_root_and_conversation_identity_and_state_across_reopen() {
    let (_directory, path) = sqlite_path();
    let (harness, _registry) = open_harness(
        sqlite(&path).await,
        &["read"],
        OpenHarnessOptions::default(),
    )
    .await
    .unwrap();
    let root = harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    root.configure(
        AgentChange {
            model: FieldChange::Set(model("anthropic", "claude")),
            cwd: FieldChange::Set("/repo".to_owned()),
            ..AgentChange::default()
        },
        context(),
    )
    .await
    .unwrap();
    let entry = append(&root, "hello").await;
    let child = harness
        .create_conversation(ownerless(), context())
        .await
        .unwrap();
    let fork = root.fork(entry.id, ownerless(), context()).await.unwrap();
    let mut provider_session_ids = Vec::new();
    for conversation in [&root, &child, &fork] {
        provider_session_ids.push(provider_session_id(&harness, conversation.id()).await);
    }
    // Regression coverage for #10424: a fork must not inherit its parent's provider identity.
    for session_id in &provider_session_ids {
        assert!(is_uuid_v7(session_id.as_deref().unwrap()));
    }
    let distinct: std::collections::HashSet<_> = provider_session_ids.iter().collect();
    assert_eq!(distinct.len(), 3);
    harness.close(context()).await.unwrap();
    assert!(root.agent(context()).await.is_err());

    // The new process installs nothing: the stored choices survive, the tools do not resolve.
    let (harness, _registry) =
        open_harness(sqlite(&path).await, &[], OpenHarnessOptions::default())
            .await
            .unwrap();
    let reopened = harness
        .root(
            RootOptions {
                agent: None,
                init: unreachable_init(),
            },
            context(),
        )
        .await
        .unwrap();
    assert_eq!(reopened.id(), ROOT_CONVERSATION_ID);
    let agent = reopened.agent(context()).await.unwrap();
    assert_eq!(agent.model, Some(model("anthropic", "claude")));
    assert_eq!(agent.cwd.as_deref(), Some("/repo"));
    assert!(agent.tools.is_empty());
    assert_eq!(all_entries(&reopened).await, ["hello"]);
    assert_eq!(
        harness
            .conversation(child.id(), context())
            .await
            .unwrap()
            .map(|conversation| conversation.id()),
        Some(child.id())
    );
    let mut reopened_ids = Vec::new();
    for id in [root.id(), child.id(), fork.id()] {
        reopened_ids.push(provider_session_id(&harness, id).await);
    }
    assert_eq!(reopened_ids, provider_session_ids);
    let reopened_fork = harness
        .conversation(fork.id(), context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(all_entries(&reopened_fork).await, ["hello"]);
    assert_eq!(
        reopened_fork.agent(context()).await.unwrap().model,
        Some(model("anthropic", "claude"))
    );
    assert!(harness
        .conversation(ConversationId::from_number(999), context())
        .await
        .unwrap()
        .is_none());
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn creates_independent_conversations_atomically_with_init_and_rolls_back_failures() {
    let storage = ControlledStorage::new();
    let (harness, registry) = open_harness(
        Arc::clone(&storage) as Arc<dyn Storage>,
        &["read"],
        OpenHarnessOptions::default(),
    )
    .await
    .unwrap();
    let created = harness
        .create_conversation(
            ConversationCreateOptions {
                ownership: ConversationOwnership::Ownerless,
                agent: None,
                init: init(|tx, id| async move {
                    tx.append_entry(id, message_draft("seed")).await?;
                    Ok(())
                }),
            },
            context(),
        )
        .await
        .unwrap();
    assert_eq!(storage.commit_count(), 1);
    assert_eq!(all_entries(&created).await, ["seed"]);

    let before = storage.commit_count();
    let error = harness
        .create_conversation(
            ConversationCreateOptions {
                ownership: ConversationOwnership::Ownerless,
                agent: Some(AgentChange {
                    thinking_level: FieldChange::Set(ModelThinkingLevel::High),
                    ..AgentChange::default()
                }),
                init: init(|_, _| async { Err(SessionError::error("init failed")) }),
            },
            context(),
        )
        .await
        .unwrap_err();
    assert!(error.to_string().contains("init failed"), "{error}");
    assert_eq!(storage.commit_count(), before);

    // A conversation on the default selection follows installs live.
    add_tool(&registry, tool("bash"), None).unwrap();
    let names = tool_names(&created.agent(context()).await.unwrap().tools);
    assert_eq!(names, ["read", "bash"]);
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn forks_at_a_concrete_entry_with_the_as_of_agent_and_applies_agent_and_init_overrides() {
    let (harness, registry) = open_harness(
        Arc::new(MemoryStorage::new()),
        &["read"],
        OpenHarnessOptions::default(),
    )
    .await
    .unwrap();
    let legacy = tool("legacy");
    add_tool(&registry, Arc::clone(&legacy), None).unwrap();
    let root = harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    root.configure(
        AgentChange {
            thinking_level: FieldChange::Set(ModelThinkingLevel::Low),
            ..AgentChange::default()
        },
        context(),
    )
    .await
    .unwrap();
    let at = append(&root, "one").await;
    root.configure(
        AgentChange {
            thinking_level: FieldChange::Set(ModelThinkingLevel::High),
            tools: FieldChange::Set(ToolsChange::Exactly(vec![tool("read")])),
            ..AgentChange::default()
        },
        context(),
    )
    .await
    .unwrap();
    append(&root, "two").await;

    let child = root.fork(at.id, ownerless(), context()).await.unwrap();
    assert_eq!(
        agent_state(&harness, child.id()).await,
        Some(AgentState {
            thinking_level: Some(ModelThinkingLevel::Low),
            ..AgentState::default()
        })
    );
    assert_eq!(all_entries(&child).await, ["one"]);

    let seen = Arc::new(Mutex::new(None));
    let sink = Arc::clone(&seen);
    let overridden = root
        .fork(
            at.id,
            ConversationCreateOptions {
                ownership: ConversationOwnership::Ownerless,
                agent: Some(AgentChange {
                    thinking_level: FieldChange::Set(ModelThinkingLevel::Minimal),
                    tools: FieldChange::Set(ToolsChange::Exactly(vec![legacy])),
                    ..AgentChange::default()
                }),
                init: init(move |tx, id| async move {
                    let agent = tx.doc(&AGENT_DOC, id).await?.value()?;
                    *sink.lock().unwrap_or_else(PoisonError::into_inner) =
                        agent.get("thinkingLevel").cloned();
                    Ok(())
                }),
            },
            context(),
        )
        .await
        .unwrap();
    assert_eq!(
        *seen.lock().unwrap_or_else(PoisonError::into_inner),
        Some(json(r#""minimal""#))
    );
    assert_eq!(
        agent_state(&harness, overridden.id()).await,
        Some(AgentState {
            thinking_level: Some(ModelThinkingLevel::Minimal),
            tools: Some(ToolFilter::Exactly(vec!["legacy".to_owned()])),
            ..AgentState::default()
        })
    );
    assert_eq!(
        agent_state(&harness, root.id()).await,
        Some(AgentState {
            thinking_level: Some(ModelThinkingLevel::High),
            tools: Some(ToolFilter::Exactly(vec!["read".to_owned()])),
            ..AgentState::default()
        })
    );

    let unrelated = harness
        .create_conversation(ownerless(), context())
        .await
        .unwrap();
    assert!(root.fork(at.id, ownerless(), context()).await.is_ok());
    let error = unrelated
        .fork(at.id, ownerless(), context())
        .await
        .unwrap_err();
    assert!(error.to_string().contains("is not visible"), "{error}");
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn paginates_fork_aware_history_through_deep_ancestor_caps_and_same_commit_prefixes() {
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
    append(&root, "r1").await;
    let root_id = root.id();
    let (r2, _r3) = root
        .commit(
            move |tx| async move {
                Ok((
                    tx.append_entry(root_id, message_draft("r2")).await?,
                    tx.append_entry(root_id, message_draft("r3")).await?,
                ))
            },
            context(),
        )
        .await
        .unwrap();
    let child = root.fork(r2.id, ownerless(), context()).await.unwrap();
    let c1 = append(&child, "c1").await;
    append(&child, "c2").await;
    let grandchild = child.fork(c1.id, ownerless(), context()).await.unwrap();
    append(&grandchild, "g1").await;

    assert_eq!(all_entries(&root).await, ["r3", "r2", "r1"]);
    assert_eq!(all_entries(&child).await, ["c2", "c1", "r2", "r1"]);
    assert_eq!(all_entries(&grandchild).await, ["g1", "c1", "r2", "r1"]);
    // #10546
    assert_eq!(
        entries_in(&grandchild, Some(ScanOrder::Ascending)).await,
        ["r1", "r2", "c1", "g1"]
    );
    // TS also passes `conversationId: root.id`, which the handle ignores;
    // the Rust query has no such field.
    let bounded = grandchild
        .entries(
            ConversationEntryQuery {
                min_entry_id: Some(r2.id),
                max_entry_id: Some(c1.id),
                order: None,
            },
            10,
            None,
            context(),
        )
        .await
        .unwrap();
    let ids: Vec<_> = bounded.items.iter().map(|entry| entry.id).collect();
    assert_eq!(ids, [c1.id, r2.id]);
    assert!(MESSAGE.is(bounded.items.first()));
    assert!(!MESSAGE.is(None));
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn binds_commits_and_task_creation_to_the_conversation() {
    let (harness, _registry) = open_harness(
        Arc::new(MemoryStorage::new()),
        &[],
        OpenHarnessOptions::default(),
    )
    .await
    .unwrap();
    let conversation = harness
        .create_conversation(ownerless(), context())
        .await
        .unwrap();
    let task = define_task::<JsonValue, JsonValue, JsonValue, ()>(
        TaskDefinition::new(
            "test.work",
            1,
            |_: &JsonValue| Ok(json(r#"{"phase":"run"}"#)),
            |_, _, _| async { Ok(()) },
        )
        .phase("run", |_, _, _| async { Ok(()) }),
    );
    let definition = task.erase().as_definition_ref();
    let created = Arc::clone(&definition);
    let task_id = conversation
        .commit(
            move |tx| async move {
                tx.create_task(created, json(r#"{"n":1}"#), task_options())
                    .await
            },
            context(),
        )
        .await
        .unwrap();
    let record = harness
        .commit(move |tx| async move { tx.task(task_id).await }, context())
        .await
        .unwrap();
    assert_eq!(
        record.map(|record| record.conversation_id),
        Some(conversation.id())
    );
    let error = harness
        .commit(
            move |tx| async move {
                tx.create_task(definition, json(r#"{"n":2}"#), task_options())
                    .await
            },
            context(),
        )
        .await
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("requires options.conversationId"),
        "{error}"
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
#[expect(clippy::too_many_lines, reason = "one TS case, ported whole")]
async fn runs_conversation_created_in_every_creating_commit_after_the_built_ins_and_before_agent_and_init(
) {
    let seen: Arc<Mutex<Vec<String>>> = Arc::default();
    let hook_seen = Arc::clone(&seen);
    let mut options = HarnessOptions::new(create_models(), Arc::new(create_registry()));
    options.conversation_created =
        Some(Arc::new(move |tx: Tx, conversation: ConversationRecord| {
            let seen = Arc::clone(&hook_seen);
            async move {
                let agent = tx.doc(&AGENT_DOC, conversation.id).await?.value()?;
                let cwd = agent
                    .get("cwd")
                    .and_then(JsonValue::as_str)
                    .map_or_else(|| "undefined".to_owned(), str::to_owned);
                let kind = if conversation.parent.is_none() {
                    "new"
                } else {
                    "fork"
                };
                seen.lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push(format!("{}:{kind}:{cwd}", conversation.id));
                let note = tx.doc(&NOTE_DOC, conversation.id).await?;
                let text = note
                    .value()?
                    .get("text")
                    .and_then(JsonValue::as_str)
                    .unwrap_or_default()
                    .to_owned();
                if text.is_empty() {
                    note.set("text", "created")?;
                }
                if cwd == "/fail" {
                    return Err(SessionError::error("no"));
                }
                Ok(())
            }
            .boxed()
        }));
    let harness = Harness::open(Arc::new(MemoryStorage::new()), options, context())
        .await
        .unwrap();
    let init_seen = Arc::clone(&seen);
    let root = harness
        .root(
            RootOptions {
                agent: Some(AgentChange {
                    cwd: FieldChange::Set("/root".to_owned()),
                    ..AgentChange::default()
                }),
                init: init(move |tx, id| async move {
                    let note = tx.doc(&NOTE_DOC, id).await?.value()?;
                    let text = note
                        .get("text")
                        .and_then(JsonValue::as_str)
                        .unwrap_or_default();
                    init_seen
                        .lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .push(format!("init:{text}"));
                    Ok(())
                }),
            },
            context(),
        )
        .await
        .unwrap();
    // A raw creation in a commit, as in a tool, and a fork, which already has the asOf copies.
    let raw = harness
        .commit(
            |tx| async move {
                Ok(tx
                    .create_conversation(ConversationOwnership::Ownerless)
                    .await?
                    .id)
            },
            context(),
        )
        .await
        .unwrap();
    let entry = append(&root, "hello").await;
    let fork = root.fork(entry.id, ownerless(), context()).await.unwrap();
    assert_eq!(
        *seen.lock().unwrap_or_else(PoisonError::into_inner),
        [
            format!("{}:new:undefined", root.id()),
            "init:created".to_owned(),
            format!("{raw}:new:undefined"),
            format!("{}:fork:/root", fork.id()),
        ]
    );
    assert_eq!(
        harness.snapshot(&NOTE_DOC, raw, context()).await.unwrap(),
        Some(object(r#"{"text":"created"}"#))
    );
    // A throw fails the creating commit.
    root.configure(
        AgentChange {
            cwd: FieldChange::Set("/fail".to_owned()),
            ..AgentChange::default()
        },
        context(),
    )
    .await
    .unwrap();
    assert!(root.fork(entry.id, ownerless(), context()).await.is_ok());
    let failing = append(&root, "after").await;
    let error = root
        .fork(failing.id, ownerless(), context())
        .await
        .unwrap_err();
    assert!(error.to_string().contains("no"), "{error}");
    harness.close(context()).await.unwrap();
}

// Harness agent

#[tokio::test]
#[expect(clippy::too_many_lines, reason = "one TS case, ported whole")]
async fn replaces_whole_fields_clears_them_with_null_and_leaves_undefined_fields_alone() {
    let (harness, registry) = open_harness(
        Arc::new(MemoryStorage::new()),
        &[],
        OpenHarnessOptions::default(),
    )
    .await
    .unwrap();
    let read = tool("read");
    let bash = tool("bash");
    let edit = tool("edit");
    registry
        .install(define_extension(Extension {
            tools: vec![Arc::clone(&read), Arc::clone(&bash), Arc::clone(&edit)],
            ..Extension::named("coding")
        }))
        .unwrap();
    let root = harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    let configure_root = |change: AgentChange| root.configure(change, context());
    let agent = root.agent(context()).await.unwrap();
    assert_eq!(agent.thinking_level, ModelThinkingLevel::Off);
    assert_eq!(tool_names(&agent.tools), ["read", "bash", "edit"]);
    assert!(root.agent(context()).await.unwrap().model.is_none());

    configure_root(AgentChange {
        model: FieldChange::Set(model("openai", "gpt")),
        thinking_level: FieldChange::Set(ModelThinkingLevel::Medium),
        ..AgentChange::default()
    })
    .await
    .unwrap();
    configure_root(AgentChange {
        model: FieldChange::Keep,
        instructions: FieldChange::Set("Be terse.".to_owned()),
        ..AgentChange::default()
    })
    .await
    .unwrap();
    assert_eq!(
        agent_state(&harness, root.id()).await,
        Some(AgentState {
            model: Some(model("openai", "gpt")),
            thinking_level: Some(ModelThinkingLevel::Medium),
            instructions: Some("Be terse.".to_owned()),
            ..AgentState::default()
        })
    );
    configure_root(AgentChange {
        model: FieldChange::Clear,
        instructions: FieldChange::Clear,
        ..AgentChange::default()
    })
    .await
    .unwrap();
    assert_eq!(
        agent_state(&harness, root.id()).await,
        Some(AgentState {
            thinking_level: Some(ModelThinkingLevel::Medium),
            ..AgentState::default()
        })
    );

    let offered = || {
        let agent = root.agent(context());
        async move { tool_names(&agent.await.unwrap().tools) }
    };
    let tools = |change: ToolsChange| AgentChange {
        tools: FieldChange::Set(change),
        ..AgentChange::default()
    };
    configure_root(tools(ToolsChange::Remove(vec![Arc::clone(&edit)])))
        .await
        .unwrap();
    assert_eq!(offered().await, ["read", "bash"]);
    // A new filter replaces the old one: edit is offered again.
    configure_root(tools(ToolsChange::Remove(vec![Arc::clone(&bash)])))
        .await
        .unwrap();
    assert_eq!(offered().await, ["read", "edit"]);
    configure_root(tools(ToolsChange::Exactly(vec![
        Arc::clone(&edit),
        Arc::clone(&read),
    ])))
    .await
    .unwrap();
    assert_eq!(offered().await, ["edit", "read"]);
    configure_root(AgentChange {
        tools: FieldChange::Clear,
        ..AgentChange::default()
    })
    .await
    .unwrap();
    assert_eq!(offered().await, ["read", "bash", "edit"]);
    // Names are stored without checking the registry.
    configure_root(tools(ToolsChange::Exactly(vec![
        tool("missing"),
        Arc::clone(&read),
    ])))
    .await
    .unwrap();
    assert_eq!(
        agent_state(&harness, root.id())
            .await
            .and_then(|state| state.tools),
        Some(ToolFilter::Exactly(vec![
            "missing".to_owned(),
            "read".to_owned()
        ]))
    );
    assert_eq!(offered().await, ["read"]);
    harness.close(context()).await.unwrap();
}

#[tokio::test]
#[expect(clippy::too_many_lines, reason = "one TS case, ported whole")]
async fn gives_conversations_created_through_tx_their_documents_empty_an_owner_copy_or_the_forks_as_of_copy(
) {
    let (harness, _registry) = open_harness(
        Arc::new(MemoryStorage::new()),
        &["read"],
        OpenHarnessOptions::default(),
    )
    .await
    .unwrap();
    let root = harness
        .root(
            RootOptions {
                agent: Some(AgentChange {
                    model: FieldChange::Set(model("faux", "m")),
                    instructions: FieldChange::Set("Main role.".to_owned()),
                    cwd: FieldChange::Set("/repo".to_owned()),
                    ..AgentChange::default()
                }),
                init: None,
            },
            context(),
        )
        .await
        .unwrap();
    let owner_task = idle_task("test.owner", "never").erase().as_definition_ref();
    let copied_cwd = Arc::new(Mutex::new(None));
    let sink = Arc::clone(&copied_cwd);
    let (task_id, plain, owned): (TaskId, ConversationId, ConversationId) = root
        .commit(
            move |tx| async move {
                let task_id = tx
                    .create_task(owner_task, json("{}"), task_options())
                    .await?;
                let plain = tx
                    .create_conversation(ConversationOwnership::Ownerless)
                    .await?;
                let owned = tx
                    .create_conversation(ConversationOwnership::Task { task_id })
                    .await?;
                // The copy exists when createConversation() returns, so a configure() in the same callback overrides it.
                *sink.lock().unwrap_or_else(PoisonError::into_inner) = tx
                    .doc(&AGENT_DOC, owned.id)
                    .await?
                    .value()?
                    .get("cwd")
                    .cloned();
                configure(
                    &tx,
                    owned.id,
                    &AgentChange {
                        cwd: FieldChange::Set("/worktree".to_owned()),
                        ..AgentChange::default()
                    },
                )
                .await?;
                Ok((task_id, plain.id, owned.id))
            },
            context(),
        )
        .await
        .unwrap();
    assert_eq!(
        *copied_cwd.lock().unwrap_or_else(PoisonError::into_inner),
        Some(json(r#""/repo""#))
    );
    assert_eq!(
        agent_state(&harness, plain).await,
        Some(AgentState::default())
    );
    assert_eq!(
        harness.snapshot(&LIVE_DOC, plain, context()).await.unwrap(),
        Some(object("{}"))
    );
    let provider = harness
        .snapshot(&PROVIDER_DOC, plain, context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(provider.len(), 1);
    assert!(is_uuid_v7(
        provider
            .get("sessionId")
            .and_then(JsonValue::as_str)
            .unwrap()
    ));
    assert_ne!(
        provider_session_id(&harness, owned).await,
        provider_session_id(&harness, root.id()).await
    );
    assert_eq!(
        agent_state(&harness, owned).await,
        Some(AgentState {
            model: Some(model("faux", "m")),
            instructions: Some("Main role.".to_owned()),
            cwd: Some("/worktree".to_owned()),
            ..AgentState::default()
        })
    );

    // A later owner change does not reach the child.
    root.configure(
        AgentChange {
            thinking_level: FieldChange::Set(ModelThinkingLevel::High),
            ..AgentChange::default()
        },
        context(),
    )
    .await
    .unwrap();
    assert_eq!(
        agent_state(&harness, owned)
            .await
            .and_then(|state| state.thinking_level),
        None
    );

    // A task-owned fork keeps its as-of copy of its fork parent, not its owner's agent.
    let at = root
        .commit(
            move |tx| async move { Ok(tx.append_entry(plain, EntryDraft::new("note")).await?.id) },
            context(),
        )
        .await
        .unwrap();
    let fork = root
        .commit(
            move |tx| async move {
                Ok(tx
                    .fork_conversation(plain, at, ConversationOwnership::Task { task_id })
                    .await?
                    .id)
            },
            context(),
        )
        .await
        .unwrap();
    assert_eq!(
        agent_state(&harness, fork).await,
        Some(AgentState::default())
    );
    assert_eq!(
        harness.snapshot(&LIVE_DOC, fork, context()).await.unwrap(),
        Some(object("{}"))
    );
    assert_ne!(
        provider_session_id(&harness, fork).await,
        provider_session_id(&harness, plain).await
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn reads_an_absent_agent_for_conversations_a_plain_session_created_without_writing() {
    let storage = ControlledStorage::new();
    let id = create_session(
        Arc::clone(&storage) as Arc<dyn Storage>,
        crate::session::SessionOptions::default(),
    )
    .commit(
        |tx| async move {
            Ok(tx
                .create_conversation(ConversationOwnership::Ownerless)
                .await?
                .id)
        },
        context(),
    )
    .await
    .unwrap();
    let (harness, _registry) = open_harness(
        Arc::clone(&storage) as Arc<dyn Storage>,
        &["read"],
        OpenHarnessOptions::default(),
    )
    .await
    .unwrap();
    let raw = harness.conversation(id, context()).await.unwrap().unwrap();
    assert!(harness
        .snapshot(&LIVE_DOC, id, context())
        .await
        .unwrap()
        .is_none());
    let commits = storage.commit_count();
    let agent = raw.agent(context()).await.unwrap();
    assert_eq!(agent.thinking_level, ModelThinkingLevel::Off);
    assert_eq!(tool_names(&agent.tools), ["read"]);
    assert_eq!(storage.commit_count(), commits);
    raw.configure(
        AgentChange {
            thinking_level: FieldChange::Set(ModelThinkingLevel::Low),
            ..AgentChange::default()
        },
        context(),
    )
    .await
    .unwrap();
    assert_eq!(
        agent_state(&harness, id).await,
        Some(AgentState {
            thinking_level: Some(ModelThinkingLevel::Low),
            ..AgentState::default()
        })
    );
    harness.close(context()).await.unwrap();
}

// Harness lifecycle

#[tokio::test]
async fn returns_stateless_handles_and_rejects_operations_after_close() {
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
    // TS `expect(again).not.toBe(root)`: every call returns a new handle value.
    let again = harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    assert_eq!(again.id(), root.id());
    harness.close(context()).await.unwrap();
    let error = harness
        .root(RootOptions::default(), context())
        .await
        .unwrap_err();
    assert!(error.to_string().contains("is closed"), "{error}");
    let error = harness
        .create_conversation(ownerless(), context())
        .await
        .unwrap_err();
    assert!(error.to_string().contains("is closed"), "{error}");
    let error = harness
        .conversation(root.id(), context())
        .await
        .unwrap_err();
    assert!(error.to_string().contains("is closed"), "{error}");
}

#[tokio::test]
async fn forwards_generic_session_document_apis() {
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
    let root_id = root.id();
    let entry = root
        .commit(
            move |tx| async move {
                tx.doc(&NOTE_DOC, root_id).await?.set("text", "first")?;
                tx.append_entry(root_id, message_draft("m")).await
            },
            context(),
        )
        .await
        .unwrap();
    harness
        .commit(
            move |tx| async move {
                tx.doc(&NOTE_DOC, root_id).await?.set("text", "second")?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    assert_eq!(
        harness
            .snapshot(&NOTE_DOC, root_id, context())
            .await
            .unwrap(),
        Some(object(r#"{"text":"second"}"#))
    );
    assert_eq!(
        harness
            .snapshot_as_of(&NOTE_DOC, root_id, entry.id, context())
            .await
            .unwrap(),
        Some(object(r#"{"text":"first"}"#))
    );
    let state = harness
        .document_state(&NOTE_DOC, root_id, context())
        .await
        .unwrap();
    assert_eq!(
        state.as_ref().map(DocumentState::value),
        Some(json(r#"{"text":"second"}"#))
    );
    if let Some(state) = state {
        state.dispose().unwrap();
    }
    harness.close(context()).await.unwrap();
}
