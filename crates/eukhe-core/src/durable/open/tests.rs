use std::collections::BTreeMap;
use std::path::Path;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_ai::models::{create_models as create_pi_models, CreateModelsOptions};
use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_provider, faux_tool_call, FauxAssistantMessageOptions,
    FauxModelDefinition, FauxProviderHandle, FauxResponseStep, RegisterFauxProviderOptions,
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
    AssistantContentBlock, Message, Modality, ModelThinkingLevel, StopReason, UserContent,
    UserContentBlock,
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
    let messages: Vec<_> = transcript(&entries)
        .into_iter()
        .filter(|(kind, _)| kind != "pi.system")
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
        .filter(|(kind, _)| kind != "pi.system")
        .filter_map(|(_, text)| text)
        .collect();
    assert_eq!(texts, ["first", "first answer", "second", "second answer"]);
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

/// Regression (a remote session corrupted a stylesheet): the scrubber of a
/// remote model's requests (`privacy.anonymizeRemote`) read `::before` as
/// an IPv6 and hashed it one way, so the model read `.cardIP_<hash>` and
/// its edit wrote that into the file. Now the model reads the stylesheet
/// as it is (only the address in its comment becomes a token), its edit
/// names that token, and the file on disk is the edit applied to the real
/// bytes.
#[tokio::test]
async fn a_remote_model_edits_a_stylesheet_through_the_scrub_without_corrupting_it() {
    let fixture = fixture();
    std::fs::write(
        fixture.agent_dir.join("settings.json"),
        serde_json::json!({ "privacy": { "anonymizeRemote": true } }).to_string(),
    )
    .expect("settings");
    // The faux model behind a remote endpoint.
    let mut provider = fixture.faux.provider.clone();
    let mut remote = fixture.faux.get_model();
    remote.base_url = "https://api.example.com/v1".to_owned();
    let listed: Arc<[eukhe_types::pi_ai::AnyModel]> =
        Arc::new([eukhe_types::pi_ai::AnyModel::Chat(remote)]);
    provider.get_models = Arc::new(move || Ok(Arc::clone(&listed)));
    fixture.models.set_provider(provider);
    let file = fixture.cwd.join("style.css");
    let css = "/* origin 203.0.113.7 */\n.card::before { content: \"\"; }\nli::marker { color: #ffcc00; }\n";
    std::fs::write(&file, css).expect("file");
    let reads: Arc<Mutex<Vec<String>>> = Arc::default();
    let recorded = Arc::clone(&reads);
    let edit = FauxResponseStep::factory(
        move |context: &eukhe_types::pi_ai::TranscriptContext,
              _options: Option<&eukhe_ai::types::SimpleStreamOptions>,
              _state: &eukhe_ai::providers::faux::FauxProviderState,
              _model: &eukhe_types::pi_ai::Model| {
            // The model edits rows 1 and 2 as it read them.
            let read = context
                .messages()
                .iter()
                .rev()
                .find_map(|message| match message {
                    Message::ToolResult(result) => {
                        result.content.iter().find_map(|block| match block {
                            UserContentBlock::Text(text) => Some(text.text.clone()),
                            UserContentBlock::Image(_) => None,
                        })
                    }
                    Message::System(_) | Message::User(_) | Message::Assistant(_) => None,
                })
                .unwrap_or_default();
            recorded
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(read.clone());
            let header = read.lines().next().unwrap_or_default();
            let row = |number: usize| {
                read.lines()
                    .find_map(|line| line.strip_prefix(&format!("{number}:")))
                    .unwrap_or_default()
            };
            let serde_json::Value::Object(arguments) = serde_json::json!({
                "i": "Marking the origin",
                "input": format!(
                    "{header}\nPUT 1.=2:\n+{}\n+{}",
                    row(1).replace(" */", ", staging */"),
                    row(2).replace("\"\"", "\"\\2192\""),
                ),
            }) else {
                unreachable!("an object literal");
            };
            Ok(faux_assistant_message(
                faux_tool_call("edit", arguments, Some("call-edit".to_owned())),
                FauxAssistantMessageOptions {
                    stop_reason: Some(StopReason::ToolUse),
                    ..FauxAssistantMessageOptions::default()
                },
            ))
        },
    );
    fixture.faux.set_responses(vec![
        tool_call(
            "read",
            serde_json::json!({"i": "Reading the stylesheet", "path": "style.css"}),
            "call-read",
        ),
        edit,
        answer("done"),
    ]);
    let mut config = fixture.config(SessionStorage::Memory);
    config.model = Some(fixture.model().into());
    let session = open_session(config, cx()).await.expect("open");
    // A caller-supplied collection stays unwrapped at open; the session's
    // own collection gets the provider runtime, whose dispatch scrubs a
    // remote model's requests and restores its answers.
    let _runtime = ProviderRuntime::install(&session.deps().models, session.deps());
    ask(
        &session,
        "mark the origin as staging and give the card an arrow",
    )
    .await;
    let read = reads.lock().unwrap_or_else(PoisonError::into_inner)[0].clone();
    let rows: Vec<&str> = read.lines().skip(1).take(3).collect();
    assert!(
        rows[0].starts_with("1:/* origin IP_") && rows[0].ends_with(" */"),
        "the address became a token: {read}"
    );
    assert_eq!(
        rows[1..],
        [
            "2:.card::before { content: \"\"; }",
            "3:li::marker { color: #ffcc00; }"
        ],
        "the code reads as it is: {read}"
    );
    let results = tool_results(&entries(&session).await);
    assert_eq!(
        (results[1].0.as_str(), results[1].1),
        ("edit", false),
        "{results:?}"
    );
    assert_eq!(
        std::fs::read_to_string(&file).expect("file"),
        "/* origin 203.0.113.7, staging */\n.card::before { content: \"\\2192\"; }\nli::marker { color: #ffcc00; }\n"
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

/// Regression (audit H4): a saved default model missing from the catalog
/// was replaced by the next startup default with only a log line. The
/// session now opens on the next model and shows one row that names the
/// saved default and the reason.
#[tokio::test]
async fn a_saved_default_missing_from_the_catalog_shows_a_notice_row() {
    let fixture = fixture();
    let model = fixture.model();
    std::fs::write(
        fixture.agent_dir.join("settings.json"),
        serde_json::json!({
            "defaultProvider": model.provider,
            "defaultModel": "gone",
        })
        .to_string(),
    )
    .expect("settings");
    let session = open_session(fixture.config(SessionStorage::Memory), cx())
        .await
        .expect("open");
    let agent = session.root().agent(cx()).await.expect("agent");
    assert_eq!(agent.model, Some(model.clone()));
    let rows: Vec<crate::durable::entries::CustomEntryData> = session
        .main()
        .entries(ConversationEntryQuery::default(), 1000, None, cx())
        .await
        .expect("entries")
        .items
        .into_iter()
        .filter_map(|entry| {
            crate::durable::entries::CUSTOM_ENTRY
                .narrow(entry)
                .expect("custom data")
        })
        .map(|entry| entry.data().clone())
        .filter(|data| data.custom_type == DEFAULT_MODEL_NOTICE_CUSTOM_TYPE)
        .collect();
    assert_eq!(
        rows,
        vec![crate::durable::entries::CustomEntryData {
            custom_type: DEFAULT_MODEL_NOTICE_CUSTOM_TYPE.to_owned(),
            content: Some(UserContent::Text(format!(
                "The saved default model {provider}/gone did not run: the model catalog does not have it. The session runs on {provider}/{id}.",
                provider = model.provider,
                id = model.model_id
            ))),
            display: true,
            details: None,
            input: false,
            origin: None,
        }]
    );
    session.close(cx()).await.expect("close");
}

/// Regression (audit M1): a bad models.json entry failed the session open
/// as a whole. Now the session opens on the good providers, and the bad
/// entry shows on its settings-error row.
#[tokio::test]
async fn a_bad_models_json_entry_shows_on_the_settings_error_row() {
    let fixture = fixture();
    std::fs::write(
        fixture.agent_dir.join("models.json"),
        serde_json::json!({ "providers": {
            "custom": { "models": [{ "id": "x" }] },
            "battery": {
                "baseUrl": "http://127.0.0.1:9/v1", "apiKey": "battery-key",
                "api": "openai-completions", "models": [{ "id": "mock" }]
            }
        } })
        .to_string(),
    )
    .expect("models.json");
    let mut config = fixture.config(SessionStorage::Memory);
    config.models = None;
    config.model = Some(crate::durable::deps::ModelRequest {
        provider: Some("battery".to_owned()),
        pattern: "mock".to_owned(),
    });
    let session = open_session(config, cx()).await.expect("open");
    let main = session.main();
    let mut rows = Vec::new();
    // The settings service submits the row from its own task.
    for _ in 0..500 {
        rows = main
            .entries(ConversationEntryQuery::default(), 1000, None, cx())
            .await
            .expect("entries")
            .items
            .into_iter()
            .filter_map(|entry| {
                crate::durable::entries::CUSTOM_ENTRY
                    .narrow(entry)
                    .expect("custom data")
            })
            .map(|entry| entry.data().clone())
            .filter(|data| data.custom_type == crate::durable::settings::SETTINGS_ERROR_CUSTOM_TYPE)
            .map(|data| data.content)
            .collect::<Vec<_>>();
        if !rows.is_empty() {
            break;
        }
        tokio::time::sleep(std::time::Duration::from_millis(20)).await;
    }
    assert_eq!(
        rows,
        vec![Some(UserContent::Text(
            "Settings errors (the rest of the settings apply):\n- global: models.json providers.custom: \"baseUrl\" is required when defining custom models."
                .to_owned()
        ))]
    );
    let agent = session.root().agent(cx()).await.expect("agent");
    assert_eq!(
        agent.model,
        Some(ModelRef {
            provider: "battery".to_owned(),
            model_id: "mock".to_owned(),
        })
    );
    session.close(cx()).await.expect("close");
}

/// Regression: a main conversation with a model and no stored thinking
/// level (a legacy import) ran at `off`'s wire value, or at the server's
/// own default, while the session showed `off`. Open settles it on the
/// settings default clamped to the model's ladder (`xhigh` -> `high` on a
/// ladder that stops at `high`), so the shown level is the sent one.
#[tokio::test]
async fn open_settles_an_unset_thinking_level_on_the_clamped_default() {
    let fixture = fixture();
    let thinker = faux_provider(RegisterFauxProviderOptions {
        provider: Some("thinker".to_owned()),
        models: Some(vec![FauxModelDefinition {
            id: "deep".to_owned(),
            reasoning: Some(true),
            ..FauxModelDefinition::default()
        }]),
        ..RegisterFauxProviderOptions::default()
    });
    fixture.models.set_provider(thinker.provider.clone());
    std::fs::write(
        fixture.agent_dir.join("settings.json"),
        r#"{"defaultThinkingLevel":"xhigh"}"#,
    )
    .expect("settings");
    let model = ModelRef {
        provider: "thinker".to_owned(),
        model_id: "deep".to_owned(),
    };
    let mut config = fixture.config(fixture.jsonl());
    config.model = Some(model.clone().into());
    let session = open_session(config.clone(), cx()).await.expect("open");
    session
        .root()
        .configure(
            AgentChange {
                thinking_level: FieldChange::Clear,
                ..AgentChange::default()
            },
            cx(),
        )
        .await
        .expect("clear the level");
    session.close(cx()).await.expect("close");

    let session = open_session(config, cx()).await.expect("reopen");
    let state: AgentState = from_json(&JsonValue::Object(
        session
            .harness()
            .snapshot(&AGENT_DOC, session.main().id(), cx())
            .await
            .expect("snapshot")
            .expect("agent state"),
    ))
    .expect("decode");
    assert_eq!(
        (state.model, state.thinking_level),
        (Some(model), Some(ModelThinkingLevel::High))
    );
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
    let default_model = || {
        settings
            .manager()
            .cvars()
            .optional_text(&crate::settings::cvar::table::DEFAULT_MODEL)
    };
    assert_eq!(default_model(), None);
    std::fs::write(
        fixture.agent_dir.join("settings.json"),
        r#"{"defaultModel":"other","retry":{"maxRetries":9}}"#,
    )
    .expect("settings");
    assert_eq!(default_model(), Some("other".to_string()));
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
/// output for the same inputs, with the `codemode` section just before its
/// closing `<critical>` block, which the project's instructions and the
/// environment follow.
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
        append_system_prompt: vec![crate::resources::SystemPromptInput::Text(
            "Appended.".to_owned(),
        )],
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
        append_system_prompt: deps.resources.append_system_prompt.clone(),
        cwd: fixture.cwd.display().to_string(),
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
    assert!(expected.contains("Subagents are unavailable in this session"));
    let critical = crate::prompts::closing_block(None).expect("the layered prompt closes");
    let (head, tail) = expected
        .split_once(&format!("\n\n{critical}\n\n"))
        .unwrap_or_else(|| panic!("the old prompt holds the critical block:\n{expected}"));
    // The `codemode` section, which the old builder lacks, sits between the
    // install-stable sections and the critical block when scripts can call
    // tools the model lacks; it is absent otherwise.
    let codemode = actual
        .strip_prefix(head)
        .and_then(|rest| rest.strip_suffix(tail))
        .and_then(|rest| rest.strip_suffix(&format!("{critical}\n\n")))
        .unwrap_or_else(|| panic!("the old prompt wraps the system prompt:\n{actual}"))
        .trim();
    assert!(
        codemode.is_empty()
            || (codemode.starts_with("<codemode>\n") && codemode.ends_with("</codemode>")),
        "{codemode}"
    );
    session.close(cx()).await.expect("close");
}

/// The Anthropic Messages body an OAuth client sends for a request the
/// faux provider captured: the payload hook keeps it and fails the request
/// before anything goes out.
async fn anthropic_body(
    context: &eukhe_types::pi_ai::TranscriptContext,
    options: &eukhe_ai::types::SimpleStreamOptions,
) -> serde_json::Value {
    let model = eukhe_ai::providers::all::get_builtin_model("anthropic", "claude-opus-5-5")
        .expect("catalog model");
    let payload: Arc<Mutex<Option<serde_json::Value>>> = Arc::default();
    let sink = Arc::clone(&payload);
    let mut options = options.clone();
    options.stream.request.api_key = Some("sk-ant-oat-test".to_owned());
    options.stream.request.on_payload = Some(Arc::new(move |body, _model| {
        *sink.lock().unwrap_or_else(PoisonError::into_inner) = Some(body);
        Box::pin(async {
            Err(
                eukhe_ai::utils::diagnostics::ErrorObject::named("PayloadCaptured", "captured")
                    .thrown(),
            )
        })
    }));
    let _ = eukhe_ai::api::anthropic_messages::stream_simple(&model, context, &options)
        .result()
        .await;
    let body = payload
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .take();
    body.expect("the payload was captured")
}

/// Sessions in two projects (other working directory, other AGENTS.md)
/// send the shared prefix of the system prompt as the same cache-marked
/// block at the same position, so the second session reads it from the
/// provider's cache; each project's values follow in a block of their own.
#[tokio::test]
async fn sessions_in_two_projects_send_one_marked_prompt_prefix() {
    let fixture = fixture();
    let mut systems = Vec::new();
    for (project, id) in [
        ("alpha", "0192a000-0000-7000-8000-0000000000a1"),
        ("beta", "0192a000-0000-7000-8000-0000000000b1"),
    ] {
        let cwd = fixture.cwd.join(project);
        std::fs::create_dir_all(&cwd).expect("cwd");
        std::fs::write(cwd.join("AGENTS.md"), format!("Rules of {project}.\n")).expect("agents");
        let captured = Arc::new(Mutex::new(None));
        let capture = Arc::clone(&captured);
        fixture.faux.set_responses(vec![FauxResponseStep::factory(
            move |context, options, _, _| {
                *capture.lock().unwrap_or_else(PoisonError::into_inner) =
                    Some((context.clone(), options.cloned().unwrap_or_default()));
                Ok(faux_assistant_message(
                    "ok",
                    FauxAssistantMessageOptions::default(),
                ))
            },
        )]);
        let mut config = SessionConfig::new(&fixture.agent_dir, &cwd, id, SessionStorage::Memory);
        config.models = Some(fixture.models.clone());
        config.model = Some(fixture.model().into());
        let session = open_session(config, cx()).await.expect("open");
        ask(&session, "hi").await;
        let (context, options) = captured
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .take()
            .expect("the request was captured");
        let body = anthropic_body(&context, &options).await;
        session.close(cx()).await.expect("close");
        let system = body["system"].as_array().expect("system blocks").clone();
        systems.push((project, cwd, system));
    }
    let [(_, _, alpha), (_, _, beta)] = &systems[..] else {
        panic!("two sessions");
    };
    // Billing, identity, the shared prefix, the project's tail: the prefix
    // is byte for byte the same block, marked at the same position.
    assert_eq!(alpha[2], beta[2]);
    for (project, cwd, system) in &systems {
        let marked: Vec<usize> = system
            .iter()
            .enumerate()
            .filter(|(_, block)| block.get("cache_control").is_some())
            .map(|(at, _)| at)
            .collect();
        assert_eq!(marked, vec![2, 3], "{project}: {system:?}");
        let text = |at: usize| system[at]["text"].as_str().expect("text").to_owned();
        let cwd = cwd.display().to_string();
        assert!(!text(2).contains("Rules of") && !text(2).contains(&cwd));
        assert!(text(3).contains(&format!("Rules of {project}.")) && text(3).contains(&cwd));
    }
}

/// Every segment the old builder can produce has a section, in the same
/// order, for each memory side and for a replaced prompt; the closing
/// `<critical>` block is in a layered prompt only. The shared sections are
/// exactly the static segments, the breakdown's cached prefix.
#[test]
fn section_keys_follow_the_breakdown_order() {
    let skills = Vec::new();
    for memory in [None, Some(MemoryRole::Root), Some(MemoryRole::Subagent)] {
        let custom = crate::prompts::SourcedPrompt {
            origin: crate::prompts::PromptOrigin::Flag("--system-prompt"),
            text: "Custom.".to_owned(),
        };
        for custom_prompt in [None, Some(custom)] {
            let replaced = custom_prompt.is_some();
            let breakdown = system_prompt_breakdown(&BuildSystemPromptOptions {
                custom_prompt,
                model_prompt_extras: Some("Model guidance."),
                vision_capable: Some(true),
                selected_tools: Some(vec!["ipython"]),
                prompt_guidelines: Some(vec!["Guide.".to_owned()]),
                append_system_prompt: vec![crate::prompts::SourcedPrompt {
                    origin: crate::prompts::PromptOrigin::Flag("--append-system-prompt"),
                    text: "Appended.".to_owned(),
                }],
                cwd: "/work".to_owned(),
                context_files: vec![("/work/AGENTS.md".to_owned(), "Context.".to_owned())],
                skills: skills.clone(),
                allow_recursion: None,
                rlm_depth: Some(1),
                rlm_parent_agent: Some("parent"),
                daemonless: true,
                generic_mcp_servers: vec!["docs".to_owned()],
                memory,
            });
            let keys: Vec<&str> = crate::durable::SECTION_KEYS
                .into_iter()
                .chain(crate::durable::CLOSING_KEYS)
                .collect();
            assert_eq!(
                breakdown
                    .segments
                    .iter()
                    .any(|segment| segment.name == crate::prompts::CLOSING_SEGMENT),
                !replaced,
                "the closing block is in a layered prompt only: {memory:?}"
            );
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
            for segment in &breakdown.segments {
                let at = keys.iter().position(|key| *key == segment.name);
                assert_eq!(
                    at.is_some_and(|at| at < crate::durable::SHARED_SECTIONS),
                    segment.kind == crate::prompts::SegmentKind::Static,
                    "segment {} is shared exactly when static: {memory:?}",
                    segment.name
                );
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
    // Last: it comes and goes, after every stable section.
    assert!(
        system.ends_with(
            "\n\n<running-jobs>\n2 background jobs run: bash-kept, bash-orphan.\n</running-jobs>"
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

/// The wire `read` tool serves the internal URLs:
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
        failure: None,
        replied_since_task: false,
        deletion: None,
        settled: true,
        read: false,
        report_submission: None,
        usage: None,
        progress: None,
        reporter: None,
        handback: None,
        phase: None,
        answer: None,
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

/// A session dir that an older eukhe made with the umask (0755) is made
/// private (0700) when the session opens.
#[tokio::test]
async fn open_makes_an_existing_session_dir_private() {
    use std::os::unix::fs::PermissionsExt;
    let fixture = fixture();
    let SessionStorage::Jsonl { dir, .. } = fixture.jsonl() else {
        unreachable!("a JSONL storage")
    };
    std::fs::create_dir_all(&dir).expect("session dir");
    std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o755)).expect("loose mode");
    let session = open_session(fixture.config(fixture.jsonl()), cx())
        .await
        .expect("open");
    assert_eq!(
        crate::platform::perms::file_mode(&dir),
        Some(eukhe_types::platform::access::PRIVATE_DIR_MODE)
    );
    session.close(cx()).await.expect("close");
}

/// A root session with chat memory and its subagent (depth 1, no chat
/// memory, the daemon's subagent cvar agent), otherwise configured alike.
async fn root_and_subagent_configs(fixture: &Fixture) -> (SessionConfig, SessionConfig) {
    use crate::durable::cvar_agent::CvarAgent;
    use crate::durable::deps::{ParentLink, SessionRole};
    use crate::memory::Memory;
    let memory = Memory::open(fixture.agent_dir.join("chat"), Arc::new(NoSummarizer))
        .await
        .expect("memory");
    let mut root = fixture.config(SessionStorage::Memory);
    root.model = Some(fixture.model().into());
    root.role.rlm_max_depth = 2;
    let mut child = root.clone();
    root.memory = Some(memory);
    child.session_id = "0192a000-0000-7000-8000-0000000000c1".to_owned();
    child.role = SessionRole {
        rlm_depth: 1,
        rlm_max_depth: 2,
        parent: Some(ParentLink {
            session_id: root.session_id.clone(),
            task_id: Some("task-1".to_owned()),
            agent_name: Some("main".to_owned()),
            spawned_by_request_id: None,
        }),
    };
    child.cvar_agent = CvarAgent::Subagent {
        inherited: Vec::new(),
        name: Some("scout".to_owned()),
    };
    (root, child)
}

/// A subagent's first request offers exactly its parent's tools (names,
/// descriptions, parameters, order), so it reads the tools prefix the
/// parent wrote to the provider's prompt cache: a session without chat
/// memory still offers `zoom` and `date`.
#[tokio::test]
async fn a_subagent_offers_the_same_tools_as_its_root_with_chat_memory() {
    let fixture = fixture();
    let (root, child) = root_and_subagent_configs(&fixture).await;
    let mut offered = Vec::new();
    for config in [root, child] {
        let captured: Arc<Mutex<Option<Vec<eukhe_types::pi_ai::Tool>>>> = Arc::default();
        let capture = Arc::clone(&captured);
        fixture
            .faux
            .set_responses(vec![FauxResponseStep::factory(move |context, _, _, _| {
                *capture.lock().unwrap_or_else(PoisonError::into_inner) =
                    Some(get_current_tools(context.messages()));
                Ok(faux_assistant_message(
                    "ok",
                    FauxAssistantMessageOptions::default(),
                ))
            })]);
        let session = open_session(config, cx()).await.expect("open");
        ask(&session, "hi").await;
        session.close(cx()).await.expect("close");
        offered.push(
            captured
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .take()
                .expect("the request was captured"),
        );
    }
    let names: Vec<&str> = offered[0].iter().map(|tool| tool.name.as_str()).collect();
    assert!(
        names.contains(&"zoom") && names.contains(&"date"),
        "{names:?}"
    );
    assert_eq!(offered[1], offered[0]);
}

/// In a session without chat memory, `zoom` on a line and `date` refuse
/// with a tool error; `zoom("Name")` reads the subagent registry, which
/// needs no chat memory.
#[tokio::test]
async fn without_chat_memory_zoom_on_a_line_and_date_refuse() {
    let fixture = fixture();
    let (_root, child) = root_and_subagent_configs(&fixture).await;
    fixture.faux.set_responses(vec![
        tool_call("zoom", serde_json::json!({ "id": 0, "n": 1 }), "call-1"),
        tool_call("date", serde_json::json!({ "id": 0 }), "call-2"),
        tool_call("zoom", serde_json::json!({ "id": "scout" }), "call-3"),
        answer("done"),
    ]);
    let session = open_session(child, cx()).await.expect("open");
    ask(&session, "look back").await;
    let refusal = "<harness>\n[error] This session has no chat memory: zoom on a line and date read the chat view, which only a session with chat memory has.\n</harness>";
    assert_eq!(
        tool_results(&entries(&session).await),
        vec![
            ("zoom".to_owned(), true, refusal.to_owned()),
            ("date".to_owned(), true, refusal.to_owned()),
            ("zoom".to_owned(), false, "No agent scout.".to_owned()),
        ]
    );
    session.close(cx()).await.expect("close");
}
