use std::path::Path;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::harness::types::{InputSubmissionDraft, ModelRef};
use eukhe_durable::harness::ConversationEntryQuery;
use eukhe_durable::types::EntryRecord;
use eukhe_pi_ai::models::{create_models as create_pi_models, CreateModelsOptions};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_provider, FauxAssistantMessageOptions, FauxProviderHandle,
    FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_pi_ai::utils::text::get_system_message_text;
use eukhe_pi_ai::utils::transcript::{get_current_system_message, get_current_tools};
use eukhe_types::pi_ai::{AssistantContentBlock, Message, Modality, UserContent, UserContentBlock};

use super::*;
use crate::durable::deps::PromptConfig;
use crate::memory::MemoryRole;
use crate::prompts::system_prompt::{
    build_system_prompt, system_prompt_breakdown, BuildSystemPromptOptions,
};

/// The captured request: the system prompt text and the offered tool names.
type Captured = Arc<Mutex<Option<(String, Vec<String>)>>>;

fn cx() -> &'static Context {
    &BACKGROUND_CONTEXT
}

fn answer(text: &str) -> FauxResponseStep {
    faux_assistant_message(text, FauxAssistantMessageOptions::default()).into()
}

struct Fixture {
    _dir: tempfile::TempDir,
    agent_dir: PathBuf,
    cwd: PathBuf,
    sessions: PathBuf,
    faux: FauxProviderHandle,
    models: eukhe_pi_ai::models::Models,
}

fn fixture() -> Fixture {
    let dir = tempfile::tempdir().expect("tempdir");
    let agent_dir = dir.path().join("agent");
    let cwd = dir.path().join("project");
    let sessions = agent_dir.join("sessions");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    std::fs::create_dir_all(&cwd).expect("cwd");
    let faux = faux_provider(RegisterFauxProviderOptions::default());
    let models = create_pi_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    Fixture {
        _dir: dir,
        agent_dir,
        cwd,
        sessions,
        faux,
        models,
    }
}

impl Fixture {
    fn model(&self) -> ModelRef {
        let model = self.faux.get_model();
        ModelRef {
            provider: model.provider,
            model_id: model.id,
        }
    }

    fn config(&self, storage: SessionStorage) -> SessionConfig {
        let mut config = SessionConfig::new(
            &self.agent_dir,
            &self.cwd,
            "0192a000-0000-7000-8000-000000000001",
            storage,
        );
        config.models = Some(self.models.clone());
        config
    }

    fn jsonl(&self) -> SessionStorage {
        SessionStorage::Jsonl {
            dir: self.sessions.join("0192a000-0000-7000-8000-000000000001"),
            fsync: true,
        }
    }
}

async fn entries(session: &EukheSession) -> Vec<EntryRecord> {
    let page = session
        .root()
        .entries(ConversationEntryQuery::default(), 1000, None, cx())
        .await
        .expect("entries");
    page.items.into_iter().rev().collect()
}

fn text_of(message: &Message) -> Option<String> {
    match message {
        Message::User(message) => match &message.content {
            UserContent::Text(text) => Some(text.clone()),
            UserContent::Blocks(blocks) => blocks.iter().find_map(|block| match block {
                UserContentBlock::Text(text) => Some(text.text.clone()),
                UserContentBlock::Image(_) => None,
            }),
        },
        Message::Assistant(message) => message.content.iter().find_map(|block| match block {
            AssistantContentBlock::Text(text) => Some(text.text.clone()),
            AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => None,
        }),
        Message::System(_) | Message::ToolResult(_) => None,
    }
}

/// `(kind, text)` of the conversation's entries, oldest first.
fn transcript(entries: &[EntryRecord]) -> Vec<(String, Option<String>)> {
    entries
        .iter()
        .map(|entry| {
            (
                entry.kind.clone(),
                entry
                    .model
                    .as_ref()
                    .and_then(|model| model.first())
                    .and_then(text_of),
            )
        })
        .collect()
}

async fn ask(session: &EukheSession, text: &str) {
    session
        .root()
        .submit(InputSubmissionDraft::new(text), cx())
        .await
        .expect("submit")
        .wait(cx())
        .await
        .expect("wait");
}

#[tokio::test]
async fn open_submit_answers_and_commits_entries() {
    let fixture = fixture();
    fixture.faux.set_responses(vec![answer("hello back")]);
    let mut config = fixture.config(SessionStorage::Memory);
    config.model = Some(fixture.model().into());
    let session = open_session(config, cx()).await.expect("open");
    assert!(session.deps().harness.get().is_some());
    ask(&session, "hello").await;
    let entries = entries(&session).await;
    // The delivered harness digest row persists between the prompt and the
    // answer (the old engine's `[harness-digest]` row).
    let digest_rows = transcript(&entries)
        .into_iter()
        .filter(|(kind, text)| {
            kind == "eukhe.custom"
                && text
                    .as_deref()
                    .is_some_and(|text| text.starts_with("[harness-digest]"))
        })
        .count();
    assert_eq!(digest_rows, 1);
    let messages: Vec<_> = transcript(&entries)
        .into_iter()
        .filter(|(kind, text)| {
            kind != "pi.system"
                && !(kind == "eukhe.custom"
                    && text
                        .as_deref()
                        .is_some_and(|text| text.starts_with("[harness-digest]")))
        })
        .collect();
    assert_eq!(
        messages,
        vec![
            ("pi.user".to_owned(), Some("hello".to_owned())),
            ("pi.assistant".to_owned(), Some("hello back".to_owned())),
        ]
    );
    let agent = session.root().agent(cx()).await.expect("agent");
    assert_eq!(agent.model, Some(fixture.model()));
    assert_eq!(agent.cwd, Some(fixture.cwd.to_string_lossy().into_owned()));
    let deps = Arc::clone(session.deps());
    session.close(cx()).await.expect("close");
    assert!(deps.harness.get().is_none());
    session
        .close(cx())
        .await
        .expect("a second close is a no-op");
}

#[tokio::test]
async fn reopening_the_storage_keeps_the_root_and_its_entries() {
    let fixture = fixture();
    fixture.faux.set_responses(vec![answer("first answer")]);
    let mut config = fixture.config(fixture.jsonl());
    config.model = Some(fixture.model().into());
    let session = open_session(config.clone(), cx()).await.expect("open");
    let root_id = session.root().id();
    ask(&session, "first").await;
    let before = entries(&session).await;
    session.close(cx()).await.expect("close");

    // The reopen asks for nothing: the root keeps its model.
    config.model = None;
    let session = open_session(config, cx()).await.expect("reopen");
    assert_eq!(session.root().id(), root_id);
    assert_eq!(entries(&session).await, before);
    let agent = session.root().agent(cx()).await.expect("agent");
    assert_eq!(agent.model, Some(fixture.model()));

    fixture.faux.set_responses(vec![answer("second answer")]);
    ask(&session, "second").await;
    let texts: Vec<_> = transcript(&entries(&session).await)
        .into_iter()
        .filter(|(kind, text)| {
            kind != "pi.system"
                && !(kind == "eukhe.custom"
                    && text
                        .as_deref()
                        .is_some_and(|text| text.starts_with("[harness-digest]")))
        })
        .filter_map(|(_, text)| text)
        .collect();
    assert_eq!(texts, ["first", "first answer", "second", "second answer"]);
    // The reopen delivered no second digest: the state did not change.
    assert_eq!(
        transcript(&entries(&session).await)
            .into_iter()
            .filter(|(kind, text)| {
                kind == "eukhe.custom"
                    && text
                        .as_deref()
                        .is_some_and(|text| text.starts_with("[harness-digest]"))
            })
            .count(),
        1
    );
    session.close(cx()).await.expect("close");
}

#[tokio::test]
async fn a_new_root_takes_the_settings_default_model() {
    let fixture = fixture();
    let model = fixture.model();
    std::fs::write(
        fixture.agent_dir.join("settings.json"),
        serde_json::json!({
            "defaultProvider": model.provider,
            "defaultModel": model.model_id,
        })
        .to_string(),
    )
    .expect("settings");
    let session = open_session(fixture.config(SessionStorage::Memory), cx())
        .await
        .expect("open");
    let agent = session.root().agent(cx()).await.expect("agent");
    assert_eq!(agent.model, Some(model));
    session.close(cx()).await.expect("close");
}

/// Regression: closing right after open, with no `await` in between that
/// parks (the cached agent snapshot answers without the line), must still
/// stop the session services — their stop signals are delivered to a task
/// that has never been polled.
#[tokio::test]
async fn closing_a_session_that_never_yielded_stops_its_services() {
    let fixture = fixture();
    let session = open_session(fixture.config(SessionStorage::Memory), cx())
        .await
        .expect("open");
    assert_eq!(
        session.root().agent(cx()).await.expect("agent").model,
        Some(fixture.model())
    );
    session.close(cx()).await.expect("close");
}

#[tokio::test]
async fn settings_changes_reach_the_open_session() {
    let fixture = fixture();
    let mut config = fixture.config(SessionStorage::Memory);
    config.model = Some(fixture.model().into());
    let session = open_session(config, cx()).await.expect("open");
    let settings = &session.deps().settings;
    assert_eq!(settings.manager().get_default_model(), None);
    std::fs::write(
        fixture.agent_dir.join("settings.json"),
        r#"{"defaultModel":"other","retry":{"maxRetries":9}}"#,
    )
    .expect("settings");
    assert_eq!(settings.manager().get_default_model(), Some("other"));
    let resolved = eukhe_durable::harness::agent::resolve_settings(Some(&settings.harness()));
    assert_eq!(resolved.retry.max_retries, 9);
    session.close(cx()).await.expect("close");
}

#[tokio::test]
async fn a_fork_made_main_in_its_creating_commit_is_main_after_reopen() {
    use eukhe_durable::harness::types::ConversationCreateOptions;
    use eukhe_durable::types::ConversationOwnership;
    use futures::FutureExt;

    let fixture = fixture();
    fixture.faux.set_responses(vec![answer("answer")]);
    let mut config = fixture.config(fixture.jsonl());
    config.model = Some(fixture.model().into());
    let session = open_session(config.clone(), cx()).await.expect("open");
    assert_eq!(session.main().id(), session.root().id());
    ask(&session, "question").await;
    let at = entries(&session)
        .await
        .into_iter()
        .find(|entry| entry.kind == "pi.user")
        .expect("user entry")
        .id;
    let mut options = ConversationCreateOptions::new(ConversationOwnership::Ownerless);
    options.init = Some(Box::new(|tx, id| {
        async move { crate::durable::set_main_conversation(&tx, id).await }.boxed()
    }));
    let fork = session.root().fork(at, options, cx()).await.expect("fork");
    assert_eq!(
        session.reload_main(cx()).await.expect("main").id(),
        fork.id()
    );
    session.close(cx()).await.expect("close");

    let session = open_session(config, cx()).await.expect("reopen");
    assert_eq!(session.main().id(), fork.id());
    session
        .set_main(&session.root().clone(), cx())
        .await
        .expect("set main");
    assert_eq!(session.main().id(), session.root().id());
    session.close(cx()).await.expect("close");
}

/// The system prompt the provider receives equals the old engine's
/// `build_system_prompt` output for the same inputs.
#[tokio::test]
async fn prompt_sections_join_to_the_old_system_prompt() {
    let fixture = fixture();
    std::fs::write(
        fixture.agent_dir.join("AGENTS.md"),
        "Global instructions.\n",
    )
    .expect("agents");
    std::fs::write(fixture.cwd.join("AGENTS.md"), "Project instructions.\n").expect("agents");
    let captured: Captured = Arc::default();
    let capture = Arc::clone(&captured);
    fixture
        .faux
        .set_responses(vec![FauxResponseStep::factory(move |context, _, _, _| {
            let messages = context.messages();
            let system = get_current_system_message(messages).expect("a system prompt");
            let tools = get_current_tools(messages)
                .into_iter()
                .map(|tool| tool.name)
                .collect();
            *capture.lock().unwrap_or_else(PoisonError::into_inner) =
                Some((get_system_message_text(&system), tools));
            Ok(faux_assistant_message(
                "ok",
                FauxAssistantMessageOptions::default(),
            ))
        })]);
    let mut config = fixture.config(fixture.jsonl());
    config.model = Some(fixture.model().into());
    config.prompt = PromptConfig {
        append_system_prompt: Some("Appended.".to_owned()),
        guidelines: vec!["Be brief.".to_owned(), "Be brief.".to_owned()],
        generic_mcp_servers: vec!["docs".to_owned()],
        allow_recursion: Some(false),
        ..PromptConfig::default()
    };
    let session = open_session(config, cx()).await.expect("open");
    ask(&session, "hi").await;
    let (actual, tools) = captured
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .take()
        .expect("the request was captured");

    let deps = session.deps();
    let model = fixture.faux.get_model();
    let selector = format!("{}/{}", model.provider, model.id);
    let expected = build_system_prompt(&BuildSystemPromptOptions {
        custom_prompt: deps.resources.system_prompt.clone(),
        model: Some(&selector),
        vision_capable: Some(model.input.contains(&Modality::Image)),
        selected_tools: Some(tools.iter().map(String::as_str).collect()),
        prompt_guidelines: Some(deps.prompt.guidelines.clone()),
        append_system_prompt: deps.prompt.append_system_prompt.clone(),
        cwd: fixture.cwd.display().to_string(),
        messages_path: deps
            .storage_dir
            .as_ref()
            .map(|dir| dir.display().to_string()),
        context_files: deps
            .resources
            .agents_files
            .iter()
            .map(|file| (file.path.display().to_string(), file.content.clone()))
            .collect(),
        skills: deps.resources.skills.clone(),
        allow_recursion: Some(false),
        rlm_depth: Some(0),
        rlm_parent_agent: None,
        generic_mcp_servers: deps.generic_mcp_servers.clone(),
        memory: None,
    });
    assert!(expected.contains("Project instructions."));
    assert!(expected.contains("Appended."));
    assert_eq!(actual, expected);
    session.close(cx()).await.expect("close");
}

/// Every segment the old builder can produce has a section, in the same
/// order, for each memory side and for a replaced prompt.
#[test]
fn section_keys_follow_the_breakdown_order() {
    let skills = Vec::new();
    for memory in [None, Some(MemoryRole::Root), Some(MemoryRole::Subagent)] {
        for custom_prompt in [None, Some("Custom.".to_owned())] {
            let breakdown = system_prompt_breakdown(&BuildSystemPromptOptions {
                custom_prompt,
                model: Some("anthropic/claude-opus-4-5"),
                vision_capable: Some(true),
                selected_tools: Some(vec!["ipython"]),
                prompt_guidelines: Some(vec!["Guide.".to_owned()]),
                append_system_prompt: Some("Appended.".to_owned()),
                cwd: "/work".to_owned(),
                messages_path: Some("/log".to_owned()),
                context_files: vec![("/work/AGENTS.md".to_owned(), "Context.".to_owned())],
                skills: skills.clone(),
                allow_recursion: None,
                rlm_depth: Some(1),
                rlm_parent_agent: Some("parent"),
                generic_mcp_servers: vec!["docs".to_owned()],
                memory,
            });
            let keys = crate::durable::section_keys(memory);
            let mut positions = breakdown.segments.iter().map(|segment| {
                keys.iter()
                    .position(|key| *key == segment.name)
                    .unwrap_or_else(|| panic!("no section for segment {}", segment.name))
            });
            let mut previous = positions.next().expect("segments");
            for position in positions {
                assert!(position > previous, "segment order differs: {memory:?}");
                previous = position;
            }
            assert!(breakdown
                .segments
                .iter()
                .all(|segment| !segment.text.is_empty()));
        }
    }
}

#[test]
fn legacy_file_is_imported_only_into_a_missing_directory() {
    let dir = tempfile::tempdir().expect("tempdir");
    let storage = dir.path().join("abc");
    assert_eq!(legacy_session_file(&storage, "abc"), None);
    std::fs::write(dir.path().join("abc.jsonl"), "{}\n").expect("legacy");
    assert_eq!(
        legacy_session_file(&storage, "abc"),
        Some(dir.path().join("abc.jsonl"))
    );
    std::fs::create_dir(&storage).expect("storage");
    assert_eq!(legacy_session_file(Path::new(&storage), "abc"), None);
}
