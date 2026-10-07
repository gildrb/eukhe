//! Port of `test/harness-prompt.test.ts`.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::{with_abort_signal, AbortController, Context};
use eukhe_pi_ai::utils::transcript::{get_current_tools, to_tool_declaration};
use eukhe_types::pi_ai::{
    IndexMap, Message, ModelThinkingLevel, SystemContent, SystemMessage, Tool,
};
use futures::future::{ready, BoxFuture};
use futures::FutureExt;

use super::{plan_system_entries, render_sections, replay_sections, SystemDraft};
use crate::documents::{AnyDocDefinition, ResolvedAddress};
use crate::entries::SYSTEM_ENTRY;
use crate::harness::agent::{resolve_agent, resolve_settings};
use crate::harness::define::{define_extension, section, wrap_section};
use crate::harness::tests::support::{
    add_section, context, create_registry, empty_object_schema, open_harness, user,
    OpenHarnessOptions,
};
use crate::harness::types::{Agent, Extension, PromptInput, PromptSection, RegistryReader};
use crate::harness::{Conversation, ConversationEntryQuery, RootOptions};
use crate::session::{SessionError, SessionResult};
use crate::storage::MemoryStorage;
use crate::types::{
    ContextEditAction, ConversationId, DocumentReader, EntryDraft, EntryHead, EntryId, JsonObject,
};

/// TS `{ snapshot: async () => undefined, snapshotAsOf: async () => undefined }`.
struct NoDocuments;

impl DocumentReader for NoDocuments {
    fn snapshot_definition(
        &self,
        _definition: Arc<dyn AnyDocDefinition>,
        _resolved: ResolvedAddress,
        _cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<JsonObject>>>> {
        ready(Ok(None)).boxed()
    }

    fn snapshot_as_of_definition(
        &self,
        _definition: Arc<dyn AnyDocDefinition>,
        _resolved: ResolvedAddress,
        _at: EntryId,
        _cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<JsonObject>>>> {
        ready(Ok(None)).boxed()
    }
}

/// One planned entry: its section patch and the targets it omits.
#[derive(Debug, PartialEq)]
struct Planned {
    sections: IndexMap<String, Option<String>>,
    omit: Option<Vec<EntryId>>,
}

fn planned(sections: &[(&str, Option<&str>)], omit: Option<Vec<EntryId>>) -> Planned {
    Planned {
        sections: patch(sections),
        omit,
    }
}

fn patch(sections: &[(&str, Option<&str>)]) -> IndexMap<String, Option<String>> {
    sections
        .iter()
        .map(|(key, value)| ((*key).to_owned(), value.map(str::to_owned)))
        .collect()
}

fn desired_map(desired: &[(&str, &str)]) -> IndexMap<String, String> {
    desired
        .iter()
        .map(|(key, value)| ((*key).to_owned(), (*value).to_owned()))
        .collect()
}

fn system_message(draft: &SystemDraft) -> &SystemMessage {
    match draft.model.as_deref() {
        Some([Message::System(message)]) => message,
        other => panic!("expected one system message, got {other:?}"),
    }
}

async fn append_drafts(conversation: &Conversation, drafts: &[SystemDraft]) {
    let id = conversation.id();
    let drafts = drafts.to_vec();
    conversation
        .commit(
            move |tx| async move {
                for draft in drafts {
                    tx.append_typed_entry(&SYSTEM_ENTRY, id, draft).await?;
                }
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
}

/// Plan against the current context, append the plan, and check that replay
/// then yields `desired` in order.
async fn apply(conversation: &Conversation, desired: &[(&str, &str)]) -> Vec<Planned> {
    let desired = desired_map(desired);
    let view = conversation.context(context()).await.unwrap();
    let drafts = plan_system_entries(&view, &desired, &[], 7);
    append_drafts(conversation, &drafts).await;
    let replayed = replay_sections(&conversation.context(context()).await.unwrap().messages);
    assert_eq!(
        replayed.into_iter().collect::<Vec<_>>(),
        desired.into_iter().collect::<Vec<_>>()
    );
    drafts
        .iter()
        .map(|draft| {
            let message = system_message(draft);
            assert_eq!(message.content, SystemContent::from(""));
            assert_eq!(message.timestamp, 7);
            let omit = draft.edits.as_ref().map(|edits| {
                edits
                    .iter()
                    .map(|edit| {
                        assert!(matches!(edit.action, ContextEditAction::Omit));
                        edit.target
                    })
                    .collect()
            });
            Planned {
                sections: message.sections.clone().unwrap(),
                omit,
            }
        })
        .collect()
}

/// The harness stays open for the conversation's lifetime.
struct Root {
    _harness: crate::harness::Harness,
    conversation: Conversation,
}

async fn root() -> Root {
    let (harness, _registry) = open_harness(
        Arc::new(MemoryStorage::new()),
        &[],
        OpenHarnessOptions::default(),
    )
    .await
    .unwrap();
    let conversation = harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    Root {
        _harness: harness,
        conversation,
    }
}

async fn last_system_id(conversation: &Conversation) -> EntryId {
    let page = conversation
        .entries(ConversationEntryQuery::default(), 100, None, context())
        .await
        .unwrap();
    page.items
        .iter()
        .find(|entry| entry.kind == "pi.system")
        .unwrap()
        .id
}

async fn marker(conversation: &Conversation, head: EntryHead) -> EntryId {
    let id = conversation.id();
    let mut draft = EntryDraft::new("summary");
    draft.head = Some(head);
    draft.model = Some(vec![user("summary").into()]);
    conversation
        .commit(
            move |tx| async move { Ok(tx.append_entry(id, draft).await?.id) },
            context(),
        )
        .await
        .unwrap()
}

fn input() -> PromptInput {
    PromptInput {
        conversation_id: ConversationId::from_number(1),
        agent: Arc::new(Agent {
            model: None,
            thinking_level: ModelThinkingLevel::Off,
            extensions: Vec::new(),
            tools: Vec::new(),
            sections: Vec::new(),
            instructions: None,
            cwd: None,
        }),
        env: None,
        shown: IndexMap::new(),
        read: Arc::new(NoDocuments),
    }
}

fn text(value: &'static str) -> BoxFuture<'static, SessionResult<Option<String>>> {
    ready(Ok(Some(value.to_owned()))).boxed()
}

fn fail(message: &'static str) -> BoxFuture<'static, SessionResult<Option<String>>> {
    ready(Err(SessionError::error(message))).boxed()
}

#[tokio::test]
async fn renders_sections_in_order_with_tags_omissions_wrappers_and_failures() {
    let registry = create_registry();
    add_section(
        &registry,
        "preamble",
        |_, _| text("You are helpful."),
        Some(false),
        None,
    )
    .unwrap();
    add_section(
        &registry,
        "cwd",
        |_, _| async { Ok(Some("/repo".to_owned())) }.boxed(),
        None,
        None,
    )
    .unwrap();
    add_section(
        &registry,
        "skipped",
        |_, _| ready(Ok(None)).boxed(),
        None,
        None,
    )
    .unwrap();
    add_section(
        &registry,
        "failing",
        |_, _| fail("render failed"),
        None,
        None,
    )
    .unwrap();
    add_section(
        &registry,
        "new-failing",
        |_, _| fail("also failed"),
        None,
        None,
    )
    .unwrap();
    registry
        .install(define_extension(Extension {
            wraps: vec![wrap_section("cwd", |inner| {
                let wrapped = Arc::clone(inner);
                Ok(Arc::new(PromptSection {
                    render: Arc::new(move |value: &PromptInput, cx: &Context| {
                        let rendered = (wrapped.render)(value, cx);
                        async move {
                            // TS template literal of the awaited value.
                            let text = rendered.await?.unwrap_or_else(|| "undefined".to_owned());
                            Ok(Some(format!("{text} (git)")))
                        }
                        .boxed()
                    }),
                    ..(**inner).clone()
                }))
            })],
            ..Extension::named("git")
        }))
        .unwrap();
    let reports = Mutex::new(Vec::new());
    let shown = desired_map(&[("failing", "<failing>\nold\n</failing>"), ("cwd", "stale")]);
    let agent = resolve_agent(
        None,
        &registry.snapshot(),
        &resolve_settings(None),
        &|error| panic!("{error}"),
    );
    let desired = render_sections(
        &agent.sections,
        &input(),
        &shown,
        &|error| {
            reports
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(error.to_string());
            Ok(())
        },
        context(),
    )
    .await
    .unwrap();
    assert_eq!(
        desired,
        desired_map(&[
            ("preamble", "You are helpful."),
            ("cwd", "<cwd>\n/repo (git)\n</cwd>"),
            ("failing", "<failing>\nold\n</failing>"),
        ])
    );
    assert_eq!(
        reports.into_inner().unwrap_or_else(PoisonError::into_inner),
        ["render failed", "also failed"]
    );
}

#[tokio::test]
async fn propagates_section_errors_after_cancellation() {
    let controller = AbortController::new();
    controller.abort(Some(Arc::new(SessionError::error("cancelled"))));
    let cancelled = with_abort_signal(&controller.signal(), context());
    let failing = section("a", |_, _| fail("cancelled"), None);
    let error = render_sections(
        &[failing],
        &input(),
        &IndexMap::new(),
        &|_| Ok(()),
        &cancelled,
    )
    .await
    .unwrap_err();
    assert_eq!(error.to_string(), "cancelled");
}

#[test]
fn replays_sections_in_place_deletes_on_null_and_appends_re_additions() {
    let system = |sections: &[(&str, Option<&str>)]| {
        Message::System(SystemMessage {
            content: SystemContent::from(""),
            sections: Some(patch(sections)),
            tools_added: None,
            tools_removed: None,
            timestamp: 1,
        })
    };
    let shown = replay_sections(&[
        system(&[("a", Some("1")), ("b", Some("2")), ("c", Some("3"))]),
        user("x").into(),
        system(&[("b", Some("20")), ("a", None)]),
        system(&[("a", Some("10"))]),
    ]);
    assert_eq!(shown, desired_map(&[("b", "20"), ("c", "3"), ("a", "10")]));
}

#[tokio::test]
async fn emits_minimal_value_patches_removals_and_additions() {
    let root = root().await;
    let conversation = &root.conversation;
    assert_eq!(
        apply(conversation, &[("a", "1"), ("b", "2"), ("c", "3")]).await,
        [planned(
            &[("a", Some("1")), ("b", Some("2")), ("c", Some("3"))],
            None
        )]
    );
    assert_eq!(
        apply(
            conversation,
            &[("a", "1"), ("b", "20"), ("c", "3"), ("d", "4")]
        )
        .await,
        [planned(&[("b", Some("20")), ("d", Some("4"))], None)]
    );
    assert_eq!(
        apply(conversation, &[("a", "1"), ("c", "3"), ("d", "4")]).await,
        [planned(&[("b", None)], None)]
    );
    assert_eq!(
        apply(conversation, &[("a", "1"), ("c", "3"), ("d", "4")]).await,
        []
    );
    assert_eq!(
        apply(conversation, &[]).await,
        [planned(&[("a", None), ("c", None), ("d", None)], None)]
    );
}

#[tokio::test]
async fn rewrites_order_only_changes_and_re_additions_as_two_entries() {
    let first = root().await;
    let conversation = &first.conversation;
    apply(conversation, &[("a", "1"), ("b", "2")]).await;
    assert_eq!(
        apply(conversation, &[("b", "2"), ("a", "1")]).await,
        [
            planned(&[("a", None), ("b", None)], None),
            planned(&[("b", Some("2")), ("a", Some("1"))], None),
        ]
    );
    let readded_root = root().await;
    let readded = &readded_root.conversation;
    apply(readded, &[("a", "1"), ("b", "2"), ("c", "3")]).await;
    assert_eq!(
        apply(readded, &[("a", "1"), ("c", "3")]).await,
        [planned(&[("b", None)], None)]
    );
    // Patching would append `b` after `c`.
    assert_eq!(
        apply(readded, &[("a", "1"), ("b", "2"), ("c", "3")]).await,
        [
            planned(&[("a", None), ("c", None)], None),
            planned(
                &[("a", Some("1")), ("b", Some("2")), ("c", Some("3"))],
                None
            ),
        ]
    );
}

#[tokio::test]
async fn rebaselines_after_a_head_marker_omitting_retained_deltas_on_both_sides_of_it() {
    let root = root().await;
    let conversation = &root.conversation;
    apply(conversation, &[("a", "1"), ("b", "2")]).await;
    let id = conversation.id();
    conversation
        .commit(
            move |tx| async move {
                let mut draft = EntryDraft::new("pi.user");
                draft.model = Some(vec![user("hi").into()]);
                tx.append_entry(id, draft).await
            },
            context(),
        )
        .await
        .unwrap();
    apply(conversation, &[("a", "1"), ("b", "20")]).await;
    let delta = last_system_id(conversation).await;
    // The head keeps the delta but cuts its baseline: replay alone would show only `b`.
    marker(conversation, EntryHead::Entry(delta)).await;
    assert_eq!(
        apply(conversation, &[("a", "1"), ("b", "20")]).await,
        [planned(
            &[("a", Some("1")), ("b", Some("20"))],
            Some(vec![delta])
        )]
    );
    let baseline = last_system_id(conversation).await;
    // A system entry follows the marker now, so later changes are ordinary patches.
    assert_eq!(
        apply(conversation, &[("a", "1"), ("b", "21")]).await,
        [planned(&[("b", Some("21"))], None)]
    );
    let after = last_system_id(conversation).await;
    // A second marker keeps deltas from both sides of the first one.
    marker(conversation, EntryHead::Entry(delta)).await;
    assert_eq!(
        apply(conversation, &[("a", "1"), ("b", "21")]).await,
        [planned(
            &[("a", Some("1")), ("b", Some("21"))],
            Some(vec![delta, baseline, after])
        )]
    );
}

#[tokio::test]
async fn writes_a_complete_post_head_baseline_even_when_replay_already_matches() {
    let root = root().await;
    let conversation = &root.conversation;
    apply(conversation, &[("a", "1")]).await;
    let baseline = last_system_id(conversation).await;
    marker(conversation, EntryHead::Entry(baseline)).await;
    assert_eq!(
        apply(conversation, &[("a", "1")]).await,
        [planned(&[("a", Some("1"))], Some(vec![baseline]))]
    );
    marker(conversation, EntryHead::SelfEntry).await;
    assert_eq!(apply(conversation, &[]).await, [planned(&[], None)]);
    assert_eq!(apply(conversation, &[]).await, []);
}

// Tool loadout preparation.

fn declaration(name: &str, description: Option<&str>) -> Tool {
    Tool {
        name: name.to_owned(),
        description: description.unwrap_or(name).to_owned(),
        parameters: empty_object_schema().into(),
        constrained_sampling: None,
    }
}

/// One planned message's tool and section changes.
#[derive(Debug, PartialEq)]
struct ToolPlan {
    removed: Option<Vec<String>>,
    added: Option<Vec<String>>,
    sections: Option<IndexMap<String, Option<String>>>,
}

fn tool_plan(
    removed: Option<&[&str]>,
    added: Option<&[&str]>,
    sections: Option<&[(&str, Option<&str>)]>,
) -> ToolPlan {
    let names = |names: &[&str]| names.iter().map(|name| (*name).to_owned()).collect();
    ToolPlan {
        removed: removed.map(names),
        added: added.map(names),
        sections: sections.map(patch),
    }
}

/// Plan tools only, append the plan, check that replay offers `tools` in
/// order, and return each message's changes.
async fn apply_tools(
    conversation: &Conversation,
    tools: &[Tool],
    sections: &[(&str, &str)],
) -> Vec<ToolPlan> {
    let view = conversation.context(context()).await.unwrap();
    let drafts = plan_system_entries(&view, &desired_map(sections), tools, 7);
    append_drafts(conversation, &drafts).await;
    let offered = get_current_tools(&conversation.context(context()).await.unwrap().messages);
    assert_eq!(
        offered,
        tools.iter().map(to_tool_declaration).collect::<Vec<_>>()
    );
    drafts
        .iter()
        .map(|draft| {
            let message = system_message(draft);
            ToolPlan {
                removed: message
                    .tools_removed
                    .as_ref()
                    .map(|tools| tools.iter().map(|tool| tool.name.clone()).collect()),
                added: message
                    .tools_added
                    .as_ref()
                    .map(|tools| tools.iter().map(|tool| tool.name.clone()).collect()),
                sections: message.sections.clone(),
            }
        })
        .collect()
}

#[tokio::test]
async fn adds_removes_replaces_changed_declarations_and_rewrites_the_order_when_needed() {
    let root = root().await;
    let conversation = &root.conversation;
    let (a, b, c) = (
        declaration("a", None),
        declaration("b", None),
        declaration("c", None),
    );
    assert_eq!(
        apply_tools(conversation, &[a.clone(), b.clone()], &[]).await,
        [tool_plan(None, Some(&["a", "b"]), None)]
    );
    assert_eq!(
        apply_tools(conversation, &[a.clone(), b.clone()], &[]).await,
        []
    );
    assert_eq!(
        apply_tools(conversation, &[a.clone(), b.clone(), c.clone()], &[]).await,
        [tool_plan(None, Some(&["c"]), None)]
    );
    assert_eq!(
        apply_tools(conversation, &[a.clone(), c.clone()], &[]).await,
        [tool_plan(Some(&["b"]), None, None)]
    );
    // A changed declaration at the end is removed and re-added in place.
    let c2 = declaration("c", Some("changed"));
    assert_eq!(
        apply_tools(conversation, &[a.clone(), c2.clone()], &[]).await,
        [tool_plan(Some(&["c"]), Some(&["c"]), None)]
    );
    // A changed declaration in the middle would move to the end, so the whole order is rewritten.
    let a2 = declaration("a", Some("changed"));
    assert_eq!(
        apply_tools(conversation, &[a2.clone(), c2.clone()], &[]).await,
        [tool_plan(Some(&["a", "c"]), Some(&["a", "c"]), None)]
    );
    // Order-only change.
    assert_eq!(
        apply_tools(conversation, &[c2, a2], &[]).await,
        [tool_plan(Some(&["a", "c"]), Some(&["c", "a"]), None)]
    );
    assert_eq!(
        apply_tools(conversation, &[], &[]).await,
        [tool_plan(Some(&["c", "a"]), None, None)]
    );
}

#[tokio::test]
async fn puts_tool_changes_on_the_last_section_entry_and_re_declares_every_tool_after_a_head_cut() {
    let root = root().await;
    let conversation = &root.conversation;
    let (a, b) = (declaration("a", None), declaration("b", None));
    assert_eq!(
        apply_tools(
            conversation,
            std::slice::from_ref(&a),
            &[("x", "1"), ("y", "2")]
        )
        .await,
        [tool_plan(
            None,
            Some(&["a"]),
            Some(&[("x", Some("1")), ("y", Some("2"))])
        )]
    );
    // Section order changes need two entries; the tool change rides on the second.
    assert_eq!(
        apply_tools(
            conversation,
            &[a.clone(), b.clone()],
            &[("y", "2"), ("x", "1")]
        )
        .await,
        [
            tool_plan(None, None, Some(&[("x", None), ("y", None)])),
            tool_plan(
                None,
                Some(&["b"]),
                Some(&[("y", Some("2")), ("x", Some("1"))])
            ),
        ]
    );
    marker(conversation, EntryHead::SelfEntry).await;
    assert_eq!(
        apply_tools(conversation, &[a, b], &[("y", "2"), ("x", "1")]).await,
        [tool_plan(
            None,
            Some(&["a", "b"]),
            Some(&[("y", Some("2")), ("x", Some("1"))])
        )]
    );
}
