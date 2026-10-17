use std::collections::BTreeMap;
use std::path::Path;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_ai::models::{create_models as create_pi_models, CreateModelsOptions};
use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_provider, faux_tool_call, FauxAssistantMessageOptions,
    FauxProviderHandle, FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_ai::utils::text::get_system_message_text;
use eukhe_ai::utils::transcript::{get_current_system_message, get_current_tools};
use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::harness::types::{InputSubmissionDraft, ModelRef};
use eukhe_durable::harness::ConversationEntryQuery;
use eukhe_durable::harness::Truncation;
use eukhe_durable::storage::jsonl::open_native_jsonl_storage;
use eukhe_durable::tree::{
    Applied, NodeId, StateKey, StateKind, StateNode, StateTree, TreeOp, TreeRecord,
};
use eukhe_durable::types::{EntryRecord, Seq};
use eukhe_types::job::JobId;
use eukhe_types::pi_ai::{
    AssistantContentBlock, Message, Modality, StopReason, UserContent, UserContentBlock,
};

use super::*;
use crate::durable::deps::PromptConfig;
use crate::durable::jobs::{
    stop_orphans, Job, JobEnd, JobEvent, JobKind, JobSpec, JobState, Orphans, JOB_DOC_KIND,
};
use crate::durable::rlm::CustomNotice;
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
    models: eukhe_ai::models::Models,
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
    // answer (the `[harness-digest]` row).
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
async fn the_state_tree_follows_the_history_and_the_live_commits() {
    let fixture = fixture();
    fixture.faux.set_responses(vec![answer("first answer")]);
    let mut config = fixture.config(fixture.jsonl());
    config.model = Some(fixture.model().into());
    let session = open_session(config.clone(), cx()).await.expect("open");
    ask(&session, "first").await;
    session.close(cx()).await.expect("close");

    config.model = None;
    let session = open_session(config, cx()).await.expect("reopen");
    fixture.faux.set_responses(vec![answer("second answer")]);
    ask(&session, "second").await;
    let live = session
        .state_tree()
        .read(by_key)
        .await
        .expect("the state tree is built");
    session.close(cx()).await.expect("close");

    // The whole committed history makes the same tree. The ids may differ:
    // the history keeps no early state of a terminal task, so the tree
    // can see its records in another order.
    let SessionStorage::Jsonl { dir, .. } = fixture.jsonl() else {
        unreachable!("a JSONL storage")
    };
    let storage = open_native_jsonl_storage(
        &dir.to_string_lossy(),
        cx(),
        JsonlStorageOptions {
            fsync: false,
            history: CommitHistory::Keep,
        },
    )
    .await
    .expect("the storage opens");
    let (replayed, results) = StateTree::from_history(&storage.take_history());
    assert_eq!(results, vec![Ok(Applied::Accepted); results.len()]);
    assert_eq!(live, by_key(&replayed));
}

/// The nodes of the state tree by key, each with the key of its parent,
/// and the last commit.
type NodesByKey = BTreeMap<StateKey, (Option<StateKey>, StateNode)>;

fn by_key(state: &StateTree) -> (NodesByKey, Option<Seq>) {
    let key = |id| state.key(id).cloned().expect("every node has a key");
    let nodes = state
        .tree()
        .iter()
        .map(|(id, node)| {
            let parent = (node.parent != NodeId::ROOT).then(|| key(node.parent));
            (key(id), (parent, node.value.clone()))
        })
        .collect();
    (nodes, state.seq())
}

fn tool_call(name: &str, arguments: serde_json::Value, id: &str) -> FauxResponseStep {
    let serde_json::Value::Object(arguments) = arguments else {
        panic!("tool arguments are an object");
    };
    faux_assistant_message(
        faux_tool_call(name, arguments, Some(id.to_owned())),
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )
    .into()
}

/// `(tool name, is_error, text)` of each tool result, oldest first.
fn tool_results(entries: &[EntryRecord]) -> Vec<(String, bool, String)> {
    entries
        .iter()
        .filter_map(|entry| match entry.model.as_deref() {
            Some([Message::ToolResult(result)]) => Some((
                result.tool_name.clone(),
                result.is_error,
                result
                    .content
                    .iter()
                    .filter_map(|block| match block {
                        UserContentBlock::Text(text) => Some(text.text.as_str()),
                        UserContentBlock::Image(_) => None,
                    })
                    .collect::<Vec<_>>()
                    .join("\n"),
            )),
            Some(_) | None => None,
        })
        .collect()
}

/// The coding agent offers `codemode`: a script calls the session's wire
/// `read` tool as a nested call and gets its text output.
#[tokio::test]
async fn a_model_calls_the_session_tools_from_a_codemode_script() {
    let fixture = fixture();
    std::fs::write(fixture.cwd.join("notes.txt"), "alpha\nbeta\n").expect("file");
    fixture.faux.set_responses(vec![
        tool_call(
            "codemode",
            serde_json::json!({
                "code": "const text = await tools.read({ i: \"Reading notes\", path: \"notes.txt\" });\nreturn [text.includes(\"2:beta\"), ALL_TOOLS.some((tool) => tool.name === \"codemode\")];"
            }),
            "call-codemode",
        ),
        answer("done"),
    ]);
    let mut config = fixture.config(SessionStorage::Memory);
    config.model = Some(fixture.model().into());
    let session = open_session(config, cx()).await.expect("open");
    ask(&session, "read the notes in a script").await;
    let results = tool_results(&entries(&session).await);
    assert_eq!(
        (results[0].0.as_str(), results[0].1),
        ("codemode", false),
        "{}",
        results[0].2
    );
    assert_eq!(
        results[0].2.lines().last(),
        Some("[true,false]"),
        "{}",
        results[0].2
    );
    session.close(cx()).await.expect("close");
}

/// A model's wire `read` then `edit` round-trip through the session's edit
/// store: the read's header and rows anchor the edit, the misspelled
/// argument is repaired with a warning, and the file changes on disk.
#[tokio::test]
async fn a_model_reads_then_edits_through_the_wire_tools() {
    let fixture = fixture();
    let file = fixture.cwd.join("notes.txt");
    std::fs::write(&file, "alpha\nbeta\ngamma\n").expect("file");
    let tag = eukhe_docs::file_hash("alpha\nbeta\ngamma\n");
    fixture.faux.set_responses(vec![
        tool_call(
            "read",
            serde_json::json!({"i": "Reading notes", "file_path": "notes.txt"}),
            "call-read",
        ),
        tool_call(
            "edit",
            serde_json::json!({
                "i": "Fixing beta",
                "input": format!("[notes.txt#{tag}]\nPUT 2.=2:\n+BETA"),
            }),
            "call-edit",
        ),
        answer("done"),
    ]);
    let mut config = fixture.config(SessionStorage::Memory);
    config.model = Some(fixture.model().into());
    let session = open_session(config, cx()).await.expect("open");
    ask(&session, "fix the notes").await;
    let results = tool_results(&entries(&session).await);
    assert_eq!(
        results[0],
        (
            "read".to_owned(),
            false,
            format!(
                "[notes.txt#{tag}]\n1:alpha\n2:beta\n3:gamma\n<harness>\n[warn] Repaired argument: file_path read as path\n</harness>"
            ),
        )
    );
    assert_eq!((results[1].0.as_str(), results[1].1), ("edit", false));
    assert!(
        results[1].2.starts_with("[notes.txt#"),
        "the edit answers with the fresh header: {}",
        results[1].2
    );
    assert_eq!(
        std::fs::read_to_string(&file).expect("file"),
        "alpha\nBETA\ngamma\n"
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
    assert_eq!(
        settings.manager().get_default_model(),
        Some("other".to_string())
    );
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

/// The system prompt the provider receives is `build_system_prompt`'s
/// output for the same inputs, followed by the `codemode` section.
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
    // A user rule map in the agent dir: its additions join the cached
    // prefix for every model.
    std::fs::write(
        fixture.agent_dir.join("model-prompts.toml"),
        "[[rule]]\nmatch = [\"*\"]\nfiles = [\"model.md\"]\n",
    )
    .expect("model prompts");
    std::fs::write(fixture.agent_dir.join("model.md"), "Model guidance.\n").expect("model.md");
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
    let expected = build_system_prompt(&BuildSystemPromptOptions {
        custom_prompt: deps.resources.system_prompt.clone(),
        model_prompt_extras: Some("Model guidance."),
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
        // No daemon child host in this fixture.
        daemonless: true,
        generic_mcp_servers: deps.generic_mcp_servers.clone(),
        memory: None,
    });
    assert!(expected.contains("Project instructions."));
    assert!(expected.contains("Appended."));
    assert!(expected.contains("Model guidance."));
    assert!(expected.contains("Subagents and completion notifications are unavailable"));
    // The `codemode` section, which the old builder lacks, follows it: the
    // tools scripts can call.
    let codemode = actual
        .strip_prefix(expected.as_str())
        .unwrap_or_else(|| panic!("the old prompt starts the system prompt:\n{actual}"));
    assert!(
        codemode
            .trim_start()
            .starts_with("<codemode>\nTools scripts can call (`await tools.<name>(args)`):")
            && codemode.ends_with("</codemode>"),
        "{codemode}"
    );
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
                model_prompt_extras: Some("Model guidance."),
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
                daemonless: true,
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

/// The job nodes of the state tree (their ids), in start order.
fn job_nodes(state: &StateTree) -> Vec<String> {
    state
        .tree()
        .iter()
        .filter(|(_, node)| {
            node.value.kind == StateKind::Document && node.value.value["kind"] == JOB_DOC_KIND
        })
        .filter_map(|(_, node)| node.value.value["key"].as_str().map(str::to_owned))
        .collect()
}

/// Wait until the job nodes of the state tree are `expected`.
async fn job_nodes_become(session: &EukheSession, expected: &[&str]) {
    let mut cursor = session.state_tree().cursor();
    let nodes = async {
        loop {
            let nodes = session.state_tree().read(job_nodes).await.expect("a tree");
            if nodes == expected {
                return;
            }
            cursor.changed().await.expect("the tree records");
        }
    };
    tokio::time::timeout(std::time::Duration::from_secs(10), nodes)
        .await
        .unwrap_or_else(|_| panic!("the job nodes never became {expected:?}"));
}

/// A job of `session` whose kill ends it at once.
fn sleeper(session: &EukheSession, id: &str) -> Job {
    session.deps().jobs.start(JobSpec {
        id: JobId::new(id).expect("id"),
        kind: JobKind::UserBash,
        label: "sleep 60".to_owned(),
        truncation: Truncation::default(),
        written: 0,
        kill: Box::new(|job| {
            job.record(JobEvent::Killed);
        }),
    })
}

/// A job is a node of the state tree while it runs; the system prompt
/// shows the running jobs of the tree; a rewind to an entry stops the
/// running jobs started after it and keeps the others; a reopen retires
/// the nodes of the jobs of the closed session.
#[tokio::test]
async fn jobs_are_state_tree_nodes_the_prompt_shows_and_a_rewind_stops_the_orphans() {
    let fixture = fixture();
    let captured: Arc<Mutex<Option<String>>> = Arc::default();
    let capture = Arc::clone(&captured);
    fixture.faux.set_responses(vec![
        answer("first answer"),
        FauxResponseStep::factory(move |context, _, _, _| {
            let system = get_current_system_message(context.messages()).expect("a system prompt");
            *capture.lock().unwrap_or_else(PoisonError::into_inner) =
                Some(get_system_message_text(&system));
            Ok(faux_assistant_message(
                "second answer",
                FauxAssistantMessageOptions::default(),
            ))
        }),
    ]);
    let mut config = fixture.config(fixture.jsonl());
    config.model = Some(fixture.model().into());
    let session = open_session(config.clone(), cx()).await.expect("open");
    let kept = sleeper(&session, "bash-kept");
    job_nodes_become(&session, &["bash-kept"]).await;
    ask(&session, "first").await;
    let target = entries(&session).await.last().expect("the answer").id;
    let orphan = sleeper(&session, "bash-orphan");
    job_nodes_become(&session, &["bash-kept", "bash-orphan"]).await;

    ask(&session, "second").await;
    let system = captured
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .take()
        .expect("the request was captured");
    assert!(
        system.contains(
            "\n\n<running-jobs>\n2 background jobs run: bash-kept, bash-orphan.\n</running-jobs>\n\n"
        ),
        "{system}"
    );

    let stopped = stop_orphans(&session, Some(target)).await;
    assert_eq!(
        stopped,
        Orphans {
            stopped: vec![JobId::new("bash-orphan").expect("id")],
            stopping: Vec::new(),
        }
    );
    assert_eq!(
        (kept.state(), orphan.state()),
        (
            JobState::START,
            JobState::Ended {
                kept: 0,
                dropped: 0,
                end: JobEnd::Killed,
            }
        )
    );
    job_nodes_become(&session, &["bash-kept"]).await;
    session.close(cx()).await.expect("close");

    config.model = None;
    let session = open_session(config, cx()).await.expect("reopen");
    job_nodes_become(&session, &[]).await;
    session.close(cx()).await.expect("close");
}

/// The index of the first record of the state tree that puts a node
/// `put` matches (its key, the node).
fn put_at(state: &StateTree, put: impl Fn(Option<&StateKey>, &StateNode) -> bool) -> Option<usize> {
    state
        .records_since(0)
        .expect("the start of the tree")
        .iter()
        .position(|record| match record {
            TreeRecord::Do(TreeOp::Put { id, value, .. }) => put(state.key(*id), value),
            TreeRecord::Do(TreeOp::Del { .. }) | TreeRecord::Rewind(_) => false,
        })
}

/// A rewind orders the jobs by the entry commits they started after, not
/// by their nodes: the writer commits a node later, so an entry can come
/// before the node of a job that started before it. That job stays; a
/// job started after the entry stops; a job whose kill sends only a
/// signal is `stopping` until its end comes.
#[tokio::test]
async fn a_rewind_keeps_a_job_that_started_before_its_target_when_the_node_came_after() {
    let fixture = fixture();
    std::fs::write(
        fixture.agent_dir.join("settings.json"),
        r#"{"toolBlockingBudgetMs":200}"#,
    )
    .expect("settings");
    let session = open_session(fixture.config(SessionStorage::Memory), cx())
        .await
        .expect("open");
    let early = sleeper(&session, "bash-early");
    let root = session.root().id();
    let draft = CustomNotice::new("test_note", "target".to_owned(), false, None)
        .draft()
        .expect("a draft");
    let target = session
        .harness()
        .commit(
            move |tx| async move { tx.append_entry(root, draft).await },
            cx(),
        )
        .await
        .expect("the entry commits")
        .id;
    let late = sleeper(&session, "bash-late");
    let deaf = session.deps().jobs.start(JobSpec {
        id: JobId::new("bash-deaf").expect("id"),
        kind: JobKind::UserBash,
        label: "trap '' TERM; sleep 60".to_owned(),
        truncation: Truncation::default(),
        written: 0,
        kill: Box::new(|_| {}),
    });
    job_nodes_become(&session, &["bash-early", "bash-late", "bash-deaf"]).await;
    // The writer was behind: the target entry came before the early node.
    let order = session
        .state_tree()
        .read(|state| {
            let entry = StateKey::Entry(target.to_string());
            (
                put_at(state, |key, _| key == Some(&entry)),
                put_at(state, |_, node| {
                    node.kind == StateKind::Document && node.value["key"] == "bash-early"
                }),
            )
        })
        .await
        .expect("a tree");
    assert!(
        matches!(order, (Some(entry), Some(node)) if entry < node),
        "{order:?}"
    );

    let stopped = stop_orphans(&session, Some(target)).await;
    assert_eq!(
        (stopped, early.state(), late.state(), deaf.state()),
        (
            Orphans {
                stopped: vec![JobId::new("bash-late").expect("id")],
                stopping: vec![JobId::new("bash-deaf").expect("id")],
            },
            JobState::START,
            JobState::Ended {
                kept: 0,
                dropped: 0,
                end: JobEnd::Killed,
            },
            JobState::START,
        )
    );
    session.close(cx()).await.expect("close");
}

/// A chat-memory compactor that is never asked: every test message is
/// short.
struct NoSummarizer;

impl crate::memory::Summarizer for NoSummarizer {
    fn complete(
        &self,
        _context: eukhe_types::pi_ai::Context,
        _started: crate::memory::ResponseStarted,
    ) -> crate::memory::SummarizerFuture {
        Box::pin(async { Err(anyhow::anyhow!("no model in this test")) })
    }
}

/// The wire `read` tool serves the internal URLs (docs/tools.md S7):
/// a chat-memory message, a subagent's chat, a skill's `SKILL.md` and a
/// workspace file; a `..` above `repo://` is rejected even though the file
/// it names exists, never clamped to the root.
#[tokio::test]
async fn the_read_tool_serves_internal_urls() {
    use crate::durable::children::{tx_put_row, ChildRow, ChildStatus};
    use crate::memory::{Kind, Memory};
    let fixture = fixture();
    let child_id = "0192a000-0000-7000-8000-0000000000c1";
    let child_dir = fixture.sessions.join(child_id);
    fixture.faux.set_responses(vec![answer("found it")]);
    let mut child = SessionConfig::new(
        &fixture.agent_dir,
        &fixture.cwd,
        child_id,
        SessionStorage::Jsonl {
            dir: child_dir.clone(),
            fsync: true,
        },
    );
    child.models = Some(fixture.models.clone());
    child.model = Some(fixture.model().into());
    let child = open_session(child, cx()).await.expect("open the subagent");
    ask(&child, "find the bug").await;
    child.close(cx()).await.expect("close the subagent");

    let skill_dir = fixture.agent_dir.join("skill-notes/notes");
    std::fs::create_dir_all(&skill_dir).expect("skill dir");
    let skill = "---\nname: notes\ndescription: Notes.\n---\n# Notes\n";
    std::fs::write(skill_dir.join("SKILL.md"), skill).expect("skill");
    std::fs::write(fixture.cwd.join("a.txt"), "alpha\n").expect("file");
    let outside = fixture.cwd.parent().expect("parent").join("secret.txt");
    std::fs::write(&outside, "outside\n").expect("outside file");
    let memory = Memory::open(fixture.agent_dir.join("chat"), Arc::new(NoSummarizer))
        .await
        .expect("memory");
    memory.append(Kind::User, "earlier").await.expect("append");
    fixture.faux.set_responses(vec![
        tool_call(
            "read",
            serde_json::json!({ "path": "memory://0" }),
            "call-1",
        ),
        tool_call(
            "read",
            serde_json::json!({ "path": "agent://scout" }),
            "call-2",
        ),
        tool_call(
            "read",
            serde_json::json!({ "path": "skill://notes" }),
            "call-3",
        ),
        tool_call(
            "read",
            serde_json::json!({ "path": "repo://a.txt" }),
            "call-4",
        ),
        tool_call(
            "read",
            serde_json::json!({ "path": "repo://../secret.txt" }),
            "call-5",
        ),
        answer("done"),
    ]);
    let mut config = fixture.config(SessionStorage::Memory);
    config.model = Some(fixture.model().into());
    config.memory = Some(memory);
    config.prompt.additional_skill_paths = vec![skill_dir.to_string_lossy().into_owned()];
    let session = open_session(config, cx()).await.expect("open");
    let row = ChildRow {
        task_id: 7,
        rlm_child_id: "sub-1".to_owned(),
        session_id: child_id.to_owned(),
        session_name: "scout".to_owned(),
        label: "find the bug".to_owned(),
        started_at: 0.0,
        status: ChildStatus::Done,
        active_session_id: None,
        session_dir: Some(child_dir.to_string_lossy().into_owned()),
        model: None,
        answer_preview: None,
        error: None,
        replied_since_task: false,
        deletion: None,
        settled: true,
        usage: None,
        progress: None,
        reporter: None,
        handback: None,
    };
    let root = session.root().id();
    session
        .harness()
        .commit(
            move |tx| async move { tx_put_row(&tx, root, &row).await },
            cx(),
        )
        .await
        .expect("the subagent's row");
    ask(&session, "read the urls").await;
    let tag = eukhe_docs::file_hash;
    assert_eq!(
        tool_results(&entries(&session).await),
        vec![
            ("read".to_owned(), false, "0+0|user: earlier".to_owned()),
            (
                "read".to_owned(),
                false,
                "user: find the bug\neukhe: found it".to_owned()
            ),
            (
                "read".to_owned(),
                false,
                format!(
                    "[{}#{}]\n1:---\n2:name: notes\n3:description: Notes.\n4:---\n5:# Notes",
                    skill_dir.join("SKILL.md").display(),
                    tag(skill)
                )
            ),
            (
                "read".to_owned(),
                false,
                format!("[a.txt#{}]\n1:alpha", tag("alpha\n"))
            ),
            (
                "read".to_owned(),
                true,
                "repo://../secret.txt goes above the root of repo://; `..` cannot leave it"
                    .to_owned()
            ),
        ]
    );
    session.close(cx()).await.expect("close");
}

/// A raw JSON-RPC stdio MCP server with resources: a paginated listing, a
/// text resource and a binary one.
const RESOURCE_SERVER: &str = r#"import base64, json, sys
while line := sys.stdin.readline():
    request = json.loads(line)
    if request.get("id") is None:
        continue
    method = request.get("method")
    params = request.get("params") or {}
    if method == "initialize":
        result = {"protocolVersion": "2025-06-18", "capabilities": {"tools": {}, "resources": {}}, "serverInfo": {"name": "fixture", "version": "1"}}
    elif method == "tools/list":
        result = {"tools": []}
    elif method == "resources/list" and params.get("cursor") is None:
        result = {"resources": [{"uri": "note://a", "name": "a", "mimeType": "text/plain", "description": "A note"}], "nextCursor": "2"}
    elif method == "resources/list":
        result = {"resources": [{"uri": "bin://b", "name": "b", "mimeType": "image/png"}]}
    elif method == "resources/read" and params["uri"] == "note://a":
        result = {"contents": [{"uri": "note://a", "mimeType": "text/plain", "text": "alpha\nbeta"}]}
    elif method == "resources/read":
        result = {"contents": [{"uri": params["uri"], "mimeType": "image/png", "blob": base64.b64encode(b"\x89PNG1234").decode()}]}
    else:
        result = {}
    print(json.dumps({"jsonrpc": "2.0", "id": request["id"], "result": result}), flush=True)
"#;

/// The wire `read` tool reads an MCP server's resources through the
/// session's kernel (where the MCP client runs): `mcp://<server>` lists
/// them, `mcp://<server>/<uri>` reads one (a binary one as a note of its
/// size and type); a server the session does not have is rejected.
#[tokio::test]
async fn the_read_tool_reads_mcp_resources() {
    let fixture = fixture();
    let server = fixture.agent_dir.join("resource_server.py");
    std::fs::write(&server, RESOURCE_SERVER).expect("server");
    let mut config = fixture.config(SessionStorage::Memory);
    let python = config
        .kernel_python
        .clone()
        .expect("the test kernel python");
    std::fs::write(
        fixture.agent_dir.join("settings.json"),
        serde_json::json!({
            "mcpServers": {
                "fx": { "type": "stdio", "command": python, "args": [server] }
            }
        })
        .to_string(),
    )
    .expect("settings");
    fixture.faux.set_responses(vec![
        tool_call("read", serde_json::json!({ "path": "mcp://fx" }), "call-1"),
        tool_call(
            "read",
            serde_json::json!({ "path": "mcp://fx/note://a" }),
            "call-2",
        ),
        tool_call(
            "read",
            serde_json::json!({ "path": "mcp://fx/bin://b" }),
            "call-3",
        ),
        tool_call(
            "read",
            serde_json::json!({ "path": "mcp://nope/x" }),
            "call-4",
        ),
        answer("done"),
    ]);
    config.model = Some(fixture.model().into());
    config.prompt.generic_mcp_servers = vec!["fx".to_owned()];
    let session = open_session(config, cx()).await.expect("open");
    ask(&session, "read the resources").await;
    assert_eq!(
        tool_results(&entries(&session).await),
        vec![
            (
                "read".to_owned(),
                false,
                "mcp://fx/note://a\ta\ttext/plain\tA note\nmcp://fx/bin://b\tb\timage/png\t"
                    .to_owned()
            ),
            ("read".to_owned(), false, "alpha\nbeta".to_owned()),
            (
                "read".to_owned(),
                false,
                "[binary resource bin://b: 8 bytes, image/png]".to_owned()
            ),
            (
                "read".to_owned(),
                true,
                "No MCP server nope in this session; its servers: fx".to_owned()
            ),
        ]
    );
    session.close(cx()).await.expect("close");
}
