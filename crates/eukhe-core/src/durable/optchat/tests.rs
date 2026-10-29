//! `eukhe.optchat` over a real Harness, a faux model, and a real chat
//! memory in a temp dir.

use std::path::Path;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_ai::models::{create_models, CreateModelsOptions, Models};
use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_provider, faux_tool_call, FauxAssistantMessageOptions,
    FauxProviderHandle, FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::harness::define::{define_extension, define_tool};
use eukhe_durable::harness::registry::{create_registry, Registry};
use eukhe_durable::harness::types::{
    AgentChange, Extension, FieldChange, HarnessOptions, InputSubmissionDraft, ModelRef,
    ToolExecutionResult, ToolRegistration,
};
use eukhe_durable::harness::{Conversation, Harness, RootOptions};
use eukhe_durable::session::SessionError;
use eukhe_durable::storage::jsonl::{JsonlStorage, JsonlStorageOptions};
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::types::{Storage, ROOT_CONVERSATION_ID};
use eukhe_types::goal::GoalContextKind;
use eukhe_types::input_origin::{AutonomousNudge, ChildExit, InputOrigin, Report};
use eukhe_types::pi_ai::{
    AssistantContentBlock, CacheBreakpoint, ImageContent, Message, StopReason, SystemContent,
    SystemMessage, TextContent, UserContent, UserContentBlock, UserMessage,
};
use tokio::sync::Notify;

use super::docs::{decode, write, CallState, LoggedState, LOGGED_DOC};
use super::lines::LogLine;
use super::logger::LoggerHandle;
use super::request::request_messages;
use super::OptChat;
use crate::durable::HarnessCell;
use crate::memory::{
    AppendKey, CompactionPrompt, Kind, Memory, MemoryRole, Summarizer, SummarizerFuture, CAP,
    DATE_TOOL_DESCRIPTION, TURN_TASK, ZOOM_TOOL_DESCRIPTION,
};

fn cx() -> &'static Context {
    &BACKGROUND_CONTEXT
}

fn lock<T>(mutex: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// A compactor with no model: every test message is short, so every view
/// line is free (the message itself).
struct NoModel;

impl Summarizer for NoModel {
    fn complete(
        &self,
        _context: eukhe_types::pi_ai::Context,
        _started: crate::memory::ResponseStarted,
    ) -> SummarizerFuture {
        Box::pin(async { Err(anyhow::anyhow!("no model in this test")) })
    }
}

/// One logged line as the chat files hold it.
#[derive(Debug, Clone, PartialEq, Eq, serde::Deserialize)]
struct Line {
    i: u64,
    kind: Kind,
    text: String,
    #[serde(default)]
    key: Option<AppendKey>,
}

/// Every logged line, by id.
fn chat_lines(chat_dir: &Path) -> Vec<(Kind, String)> {
    let mut lines: Vec<Line> = Vec::new();
    let Ok(days) = std::fs::read_dir(chat_dir.join("main")) else {
        return Vec::new();
    };
    for day in days {
        let text = std::fs::read_to_string(day.unwrap().path()).unwrap();
        lines.extend(
            text.lines()
                .map(|line| serde_json::from_str::<Line>(line).unwrap()),
        );
    }
    lines.sort_by_key(|line| line.i);
    lines
        .into_iter()
        .map(|line| (line.kind, line.text))
        .collect()
}

/// A message as the tests compare it: role, then text blocks (cache marks
/// shown) and tool calls.
fn describe(message: &Message) -> String {
    match message {
        Message::System(_) => "system".to_string(),
        Message::User(user) => {
            let blocks = match &user.content {
                UserContent::Text(text) => vec![text.clone()],
                UserContent::Blocks(blocks) => blocks
                    .iter()
                    .map(|block| match block {
                        UserContentBlock::Text(text) => match text.cache_breakpoint {
                            Some(CacheBreakpoint::Ephemeral) => format!("{}[cache]", text.text),
                            None => text.text.clone(),
                        },
                        UserContentBlock::Image(image) => format!("[image {}]", image.mime_type),
                    })
                    .collect(),
            };
            format!("user:{}", blocks.join("|"))
        }
        Message::Assistant(assistant) => {
            let blocks: Vec<String> = assistant
                .content
                .iter()
                .map(|block| match block {
                    AssistantContentBlock::Text(text) => text.text.clone(),
                    AssistantContentBlock::Thinking(thinking) => thinking.thinking.clone(),
                    AssistantContentBlock::ToolCall(call) => format!("call {}", call.name),
                })
                .collect();
            format!("assistant:{}", blocks.join("|"))
        }
        Message::ToolResult(result) => {
            let blocks: Vec<String> = result
                .content
                .iter()
                .map(|block| match block {
                    UserContentBlock::Text(text) => text.text.clone(),
                    UserContentBlock::Image(image) => format!("[image {}]", image.mime_type),
                })
                .collect();
            format!("toolResult:{}", blocks.join("|"))
        }
    }
}

fn answer(text: &str) -> eukhe_types::pi_ai::AssistantMessage {
    faux_assistant_message(text, FauxAssistantMessageOptions::default())
}

fn call(name: &str, arguments: serde_json::Value) -> eukhe_types::pi_ai::AssistantMessage {
    let serde_json::Value::Object(arguments) = arguments else {
        panic!("tool arguments are an object");
    };
    faux_assistant_message(
        faux_tool_call(name, arguments, Some(format!("call-{name}"))),
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )
}

/// The requests the faux model received, each described.
#[derive(Clone, Default)]
struct Requests(Arc<Mutex<Vec<Vec<Message>>>>);

impl Requests {
    /// A step that records its request and answers `reply`.
    fn step(&self, reply: eukhe_types::pi_ai::AssistantMessage) -> FauxResponseStep {
        let requests = Arc::clone(&self.0);
        FauxResponseStep::factory(move |request, _, _, _| {
            lock(&requests).push(request.messages().to_vec());
            Ok(reply.clone())
        })
    }

    fn all(&self) -> Vec<Vec<Message>> {
        lock(&self.0).clone()
    }

    fn described(&self) -> Vec<Vec<String>> {
        self.all()
            .iter()
            .map(|messages| messages.iter().map(describe).collect())
            .collect()
    }
}

/// Models, registry, and memory that survive a close/reopen, like a host
/// process's own objects.
struct Setup {
    dir: tempfile::TempDir,
    faux: FauxProviderHandle,
    models: Models,
    registry: Registry,
    memory: Memory,
    chat: Arc<OptChat>,
    cell: HarnessCell,
    /// Released by the `wait` tool's caller; the tool reports it started.
    started: Arc<Notify>,
    /// Ends the `hold` tool's call (it reports its start on `started`).
    release: Arc<Notify>,
    /// What the Harness reported.
    reports: Arc<Mutex<Vec<String>>>,
}

impl Setup {
    async fn new(role: MemoryRole) -> Setup {
        let dir = tempfile::tempdir().unwrap();
        let memory = Memory::open(dir.path().join("chat"), Arc::new(NoModel))
            .await
            .unwrap();
        let faux = faux_provider(RegisterFauxProviderOptions::default());
        let models = create_models(CreateModelsOptions::default());
        models.set_provider(faux.provider.clone());
        let cell = HarnessCell::default();
        let chat = OptChat::new(
            memory.clone(),
            role,
            "session".to_string(),
            Arc::new(crate::durable::EukheSettings::new(dir.path(), dir.path())),
            cell.clone(),
        );
        let registry = create_registry();
        registry.install(chat.extension()).unwrap();
        let started = Arc::new(Notify::new());
        let release = Arc::new(Notify::new());
        registry
            .install(define_extension(Extension {
                tools: vec![
                    wait_tool(Arc::clone(&started)),
                    hold_tool(Arc::clone(&started), Arc::clone(&release)),
                ],
                ..Extension::named("test.tools")
            }))
            .unwrap();
        Setup {
            dir,
            faux,
            models,
            registry,
            memory,
            chat,
            cell,
            started,
            release,
            reports: Arc::default(),
        }
    }

    fn chat_dir(&self) -> std::path::PathBuf {
        self.dir.path().join("chat")
    }

    async fn jsonl(&self) -> Arc<dyn Storage> {
        let fs = Arc::new(eukhe_durable::env::NativeExecutionEnv::new(
            eukhe_durable::env::NativeExecutionEnvOptions {
                cwd: self.dir.path().to_string_lossy().into_owned(),
                ..eukhe_durable::env::NativeExecutionEnvOptions::default()
            },
        ));
        Arc::new(
            JsonlStorage::open(
                &self.dir.path().join("session").to_string_lossy(),
                fs,
                cx(),
                JsonlStorageOptions {
                    fsync: false,
                    ..JsonlStorageOptions::default()
                },
            )
            .await
            .unwrap(),
        )
    }

    /// Open a session over `storage`: the Harness, the root with the faux
    /// model, and (root role) the logger, then resume scheduling.
    async fn open(&self, storage: Arc<dyn Storage>, logger: Logging) -> Session {
        let mut options = HarnessOptions::new(self.models.clone(), Arc::new(self.registry.clone()));
        let reports = Arc::clone(&self.reports);
        options.on_report = Some(Arc::new(move |error| {
            lock(&reports).push(error.to_string());
        }));
        let harness = Harness::open(storage, options, cx()).await.unwrap();
        let root = harness
            .root(
                RootOptions {
                    agent: Some(AgentChange {
                        model: FieldChange::Set(ModelRef {
                            provider: "faux".to_string(),
                            model_id: "faux-1".to_string(),
                        }),
                        ..AgentChange::default()
                    }),
                    ..RootOptions::default()
                },
                cx(),
            )
            .await
            .unwrap();
        self.cell.set(harness.clone(), root.clone());
        let logger = match logger {
            Logging::On => Some(self.chat.start_logger(harness.clone()).await.unwrap()),
            Logging::Off => None,
        };
        harness.resume().unwrap();
        Session {
            harness,
            root,
            logger,
        }
    }
}

/// Whether a session runs the chat logger.
#[derive(Clone, Copy)]
enum Logging {
    On,
    Off,
}

struct Session {
    harness: Harness,
    root: Conversation,
    logger: Option<LoggerHandle>,
}

impl Session {
    /// Submit `text` and wait until the conversation is idle and the logger
    /// has logged everything.
    async fn run(&self, chat: &OptChat, text: &str) {
        self.submit(text).await;
        self.root.wait_for_idle(cx()).await.unwrap();
        if self.logger.is_some() {
            chat.flush().await.unwrap();
        }
    }

    async fn submit(&self, text: &str) {
        self.root
            .submit(
                InputSubmissionDraft {
                    request_id: None,
                    content: UserContent::Text(text.to_string()),
                    when_busy: None,
                    origin: eukhe_types::input_origin::InputOrigin::User,
                    entry: None,
                },
                cx(),
            )
            .await
            .unwrap();
    }

    /// Send `text` to the running call: it joins at the next tool boundary.
    async fn steer(&self, text: &str) {
        self.root
            .submit(
                InputSubmissionDraft {
                    request_id: None,
                    content: UserContent::Text(text.to_string()),
                    when_busy: Some(eukhe_durable::harness::types::WhenBusy::Steer),
                    origin: eukhe_types::input_origin::InputOrigin::User,
                    entry: None,
                },
                cx(),
            )
            .await
            .unwrap();
    }

    /// Stop the logger and close the Harness; nothing was reported.
    async fn close(self, setup: &Setup) {
        if let Some(logger) = self.logger {
            logger.stop().await;
        }
        setup.cell.clear();
        self.harness.close(cx()).await.unwrap();
        assert_eq!(*lock(&setup.reports), Vec::<String>::new());
    }

    async fn cursor(&self) -> LoggedState {
        decode(
            &self
                .harness
                .snapshot(&LOGGED_DOC, ROOT_CONVERSATION_ID, cx())
                .await
                .unwrap()
                .unwrap(),
        )
        .unwrap()
    }
}

/// A tool that reports it started, then runs until its call is aborted.
fn wait_tool(started: Arc<Notify>) -> Arc<ToolRegistration> {
    define_tool(ToolRegistration::new(
        "wait",
        "Waits until aborted.",
        serde_json::json!({ "type": "object", "properties": {} }),
        move |_params, _api, cx: Context| {
            let started = Arc::clone(&started);
            async move {
                started.notify_one();
                if let Some(signal) = cx.abort_signal() {
                    signal.cancelled().await;
                }
                Err::<ToolExecutionResult, _>(SessionError::error("stopped"))
            }
        },
    ))
}

/// A tool that reports it started, then answers `held` once released.
fn hold_tool(started: Arc<Notify>, release: Arc<Notify>) -> Arc<ToolRegistration> {
    define_tool(ToolRegistration::new(
        "hold",
        "Holds until released.",
        serde_json::json!({ "type": "object", "properties": {} }),
        move |_params, _api, _cx| {
            let (started, release) = (Arc::clone(&started), Arc::clone(&release));
            async move {
                started.notify_one();
                release.notified().await;
                Ok(ToolExecutionResult {
                    output: Some(vec![UserContentBlock::Text(TextContent::new("held"))]),
                    ..ToolExecutionResult::default()
                })
            }
        },
    ))
}

/// The view as the call's first message describes it: its pieces, the
/// first marked at the view's last whole block of lines.
async fn view_text(memory: &Memory) -> String {
    let pieces = memory.render().await.unwrap().pieces();
    let marked = pieces.len() - 1;
    pieces
        .iter()
        .enumerate()
        .map(|(at, piece)| {
            if at < marked {
                format!("{piece}[cache]")
            } else {
                piece.clone()
            }
        })
        .collect::<Vec<_>>()
        .join("|")
}

#[tokio::test]
async fn a_run_sends_the_pinned_view_and_its_own_messages_and_logs_them() {
    let setup = Setup::new(MemoryRole::Root).await;
    setup.memory.append(Kind::User, "earlier").await.unwrap();
    let requests = Requests::default();
    setup.faux.set_responses(vec![
        requests.step(call("zoom", serde_json::json!({ "id": 0, "n": 1 }))),
        requests.step(answer("done")),
        requests.step(answer("ok")),
    ]);
    let session = setup
        .open(Arc::new(MemoryStorage::new()), Logging::On)
        .await;
    let first_view = view_text(&setup.memory).await;
    session.run(&setup.chat, "hello").await;
    let zoomed = setup.memory.zoom(0, 1).await.unwrap().text;
    let after_first = chat_lines(&setup.chat_dir());
    let second_view = view_text(&setup.memory).await;
    session.run(&setup.chat, "again").await;
    // The end of the call's first message carries the request's end mark.
    // The turn line goes to the model only; the chat logs the words alone.
    let first_user = format!("user:{first_view}|{TURN_TASK}\nhello[cache]");
    assert_eq!(
        (requests.described(), after_first,),
        (
            vec![
                vec!["system".to_string(), first_user.clone()],
                vec![
                    "system".to_string(),
                    first_user,
                    "assistant:call zoom".to_string(),
                    format!("toolResult:{zoomed}"),
                ],
                vec![
                    "system".to_string(),
                    format!("user:{second_view}|{TURN_TASK}\nagain[cache]"),
                ],
            ],
            vec![
                (Kind::User, "earlier".to_string()),
                (Kind::User, "hello".to_string()),
                (Kind::Tool, r#"zoom {"id":0,"n":1}"#.to_string()),
                (Kind::Echo, zoomed),
                (Kind::Eukhe, "done".to_string()),
            ],
        ),
    );
    // The first message of a run is byte-identical across its requests.
    let all = requests.all();
    assert_eq!(all[0][1], all[1][1]);
    // The run handed its system prompt and tools to the compactor, saved
    // for a restarted owner too: compactions reuse the turns' prefix.
    let Message::System(system) = &all[0][0] else {
        panic!("a system message leads the request");
    };
    let saved: CompactionPrompt = serde_json::from_str(
        &std::fs::read_to_string(setup.chat_dir().join("prompt.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(
        saved,
        CompactionPrompt {
            system: eukhe_ai::utils::text::get_system_message_text(system),
            tools: eukhe_ai::utils::transcript::get_current_tools(&all[0]),
        }
    );
    session.close(&setup).await;
}

#[tokio::test]
async fn zoom_and_date_keep_their_schemas_and_read_the_chat() {
    let setup = Setup::new(MemoryRole::Root).await;
    setup
        .memory
        .append(Kind::User, "remember me")
        .await
        .unwrap();
    let tools = super::tools::memory_tools(&setup.memory);
    let declared: Vec<_> = tools
        .iter()
        .map(|tool| {
            (
                tool.name.clone(),
                tool.description.clone(),
                tool.parameters.json().clone(),
            )
        })
        .collect();
    assert_eq!(
        declared,
        vec![
            (
                "zoom".to_string(),
                ZOOM_TOOL_DESCRIPTION.to_string(),
                serde_json::json!({
                    "type": "object",
                    "required": ["id"],
                    "properties": {
                        "i": {
                            "type": "string",
                            "description": "Short present-participle intent for this call."
                        },
                        "id": {
                            "anyOf": [
                                { "type": "integer", "minimum": 0 },
                                { "type": "string" }
                            ]
                        },
                        "n": { "type": "integer", "minimum": 1 }
                    },
                    "additionalProperties": false,
                    "title": "v2"
                }),
            ),
            (
                "date".to_string(),
                DATE_TOOL_DESCRIPTION.to_string(),
                serde_json::json!({
                    "type": "object",
                    "required": ["id"],
                    "properties": {
                        "i": {
                            "type": "string",
                            "description": "Short present-participle intent for this call."
                        },
                        "id": { "type": "integer", "minimum": 0 }
                    },
                    "additionalProperties": false,
                    "title": "v1"
                }),
            ),
        ]
    );
    let requests = Requests::default();
    setup.faux.set_responses(vec![
        requests.step(call("date", serde_json::json!({ "id": 0 }))),
        requests.step(call("zoom", serde_json::json!({ "id": 0, "n": 1 }))),
        requests.step(call("date", serde_json::json!({ "id": 99 }))),
        requests.step(answer("done")),
    ]);
    let session = setup
        .open(Arc::new(MemoryStorage::new()), Logging::On)
        .await;
    session.run(&setup.chat, "when?").await;
    let date = setup.memory.date(0).await.unwrap();
    let zoomed = setup.memory.zoom(0, 1).await.unwrap().text;
    let results: Vec<String> = requests
        .all()
        .last()
        .unwrap()
        .iter()
        .filter(|message| matches!(message, Message::ToolResult(_)))
        .map(describe)
        .collect();
    assert_eq!(
        results,
        vec![
            format!("toolResult:{date}"),
            format!("toolResult:{zoomed}"),
            "toolResult:No message 99.".to_string(),
        ]
    );
    session.close(&setup).await;
}

#[tokio::test]
async fn the_pinned_view_survives_a_reopen_mid_run() {
    let setup = Setup::new(MemoryRole::Root).await;
    setup.memory.append(Kind::User, "earlier").await.unwrap();
    let requests = Requests::default();
    setup
        .faux
        .set_responses(vec![requests.step(call("wait", serde_json::json!({})))]);
    let session = setup.open(setup.jsonl().await, Logging::On).await;
    let started = setup.started.notified();
    session.submit("hello").await;
    started.await;
    session.close(&setup).await;
    // The chat moves on while the session is down: a fresh render would
    // differ from the pinned view.
    setup.memory.append(Kind::User, "meanwhile").await.unwrap();
    setup
        .faux
        .set_responses(vec![requests.step(answer("done"))]);
    let session = setup.open(setup.jsonl().await, Logging::On).await;
    session.root.wait_for_idle(cx()).await.unwrap();
    setup.chat.flush().await.unwrap();
    let all = requests.all();
    let fresh = view_text(&setup.memory).await;
    assert_eq!(
        (
            all.len(),
            all[1].get(1) == all[0].get(1),
            describe(&all[1][1]).contains(&fresh)
        ),
        (2, true, false)
    );
    assert_eq!(
        chat_lines(&setup.chat_dir())
            .into_iter()
            .map(|(kind, _)| kind)
            .collect::<Vec<_>>(),
        vec![
            Kind::User,
            Kind::User,
            Kind::Tool,
            Kind::User,
            Kind::Echo,
            Kind::Eukhe
        ]
    );
    session.close(&setup).await;
}

#[tokio::test]
async fn a_crash_between_append_and_cursor_logs_no_line_twice() {
    let setup = Setup::new(MemoryRole::Root).await;
    let requests = Requests::default();
    setup.faux.set_responses(vec![
        requests.step(call("zoom", serde_json::json!({ "id": 0, "n": 1 }))),
        requests.step(answer("done")),
    ]);
    let session = setup.open(setup.jsonl().await, Logging::On).await;
    session.run(&setup.chat, "hello").await;
    let logged = chat_lines(&setup.chat_dir());
    let cursor = session.cursor().await;
    session.close(&setup).await;
    // The crash: every line is in the chat, the cursor never committed.
    let session = setup.open(setup.jsonl().await, Logging::Off).await;
    session
        .harness
        .commit(
            |tx| async move {
                let draft = tx.doc(&LOGGED_DOC, ROOT_CONVERSATION_ID).await?;
                write(&draft, &LoggedState::default(), &["through"])
            },
            cx(),
        )
        .await
        .unwrap();
    session.close(&setup).await;
    let session = setup.open(setup.jsonl().await, Logging::On).await;
    setup.chat.flush().await.unwrap();
    assert_eq!(
        (
            chat_lines(&setup.chat_dir()),
            session.cursor().await,
            logged.len()
        ),
        (logged, cursor, 4)
    );
    session.close(&setup).await;
}

#[tokio::test]
async fn a_subagent_pins_one_view_for_its_conversation_and_logs_nothing() {
    let setup = Setup::new(MemoryRole::Subagent).await;
    setup.memory.append(Kind::User, "earlier").await.unwrap();
    let requests = Requests::default();
    setup.faux.set_responses(vec![
        requests.step(answer("a1")),
        requests.step(answer("a2")),
    ]);
    let session = setup
        .open(Arc::new(MemoryStorage::new()), Logging::Off)
        .await;
    let view = view_text(&setup.memory).await;
    session.run(&setup.chat, "task").await;
    setup.memory.append(Kind::User, "later").await.unwrap();
    session.run(&setup.chat, "next").await;
    assert_eq!(
        (requests.described(), chat_lines(&setup.chat_dir())),
        (
            vec![
                vec!["system".to_string(), format!("user:{view}|task[cache]")],
                vec![
                    "system".to_string(),
                    format!("user:{view}|task[cache]"),
                    "assistant:a1".to_string(),
                    "user:next".to_string(),
                ],
            ],
            vec![
                (Kind::User, "earlier".to_string()),
                (Kind::User, "later".to_string()),
            ],
        )
    );
    session.close(&setup).await;
}

fn user(text: &str, timestamp: u64) -> Message {
    Message::User(UserMessage {
        content: UserContent::Text(text.to_string()),
        timestamp,
    })
}

fn system(text: &str, timestamp: u64) -> Message {
    Message::System(SystemMessage {
        content: SystemContent::Text(text.to_string()),
        sections: None,
        tools_added: None,
        tools_removed: None,
        timestamp,
    })
}

/// The request shape: systems before the call's first non-user message
/// replayed into one; the view pieces (all but the last cache-marked), the
/// leading user texts joined, their images after; harness state after the
/// first message; earlier messages dropped. A root call marks its texts
/// as a turn (a bare message once read as a compaction input); a
/// subagent's texts are its task alone.
#[test]
fn a_request_joins_the_leading_user_texts_behind_the_view() {
    let call = CallState {
        run_key: Some("input:1".to_string()),
        pieces: vec!["<chat>\n0+1|a\n".to_string(), "1+1|b\n</chat>".to_string()],
        through: 2,
        timestamp: 7,
    };
    let image = UserContentBlock::Image(ImageContent {
        data: "AA==".to_string(),
        mime_type: "image/png".to_string(),
    });
    let state = user("[state] kernel restored", 5);
    let messages = vec![
        system("base", 1),
        user("before the run", 2),
        user("first", 3),
        system("patch", 4),
        Message::User(UserMessage {
            content: UserContent::Blocks(vec![
                UserContentBlock::Text(TextContent::new("second")),
                image.clone(),
            ]),
            timestamp: 4,
        }),
        state.clone(),
        Message::Assistant(answer("reply")),
    ];
    let subagent = request_messages(
        &call,
        MemoryRole::Subagent,
        messages.clone(),
        2,
        |message| *message == state,
    );
    let request = request_messages(&call, MemoryRole::Root, messages, 2, |message| {
        *message == state
    });
    let Message::System(system) = &request[0] else {
        panic!("a system message leads");
    };
    assert_eq!(
        (
            system.content.clone(),
            request[1..].iter().map(describe).collect::<Vec<_>>(),
            request[1].clone(),
            describe(&subagent[1]),
        ),
        (
            SystemContent::Text("base\n\npatch".to_string()),
            vec![
                format!("user:<chat>\n0+1|a\n[cache]|1+1|b\n</chat>|{TURN_TASK}\nfirst\n\nsecond[cache]|[image image/png]"),
                "user:[state] kernel restored".to_string(),
                "assistant:reply".to_string(),
            ],
            Message::User(UserMessage {
                content: UserContent::Blocks(vec![
                    UserContentBlock::Text(TextContent {
                        text: "<chat>\n0+1|a\n".to_string(),
                        text_signature: None,
                        cache_breakpoint: Some(CacheBreakpoint::Ephemeral),
                    }),
                    UserContentBlock::Text(TextContent::new("1+1|b\n</chat>")),
                    UserContentBlock::Text(TextContent {
                        text: format!("{TURN_TASK}\nfirst\n\nsecond"),
                        text_signature: None,
                        cache_breakpoint: Some(CacheBreakpoint::Ephemeral),
                    }),
                    image,
                ]),
                timestamp: 7,
            }),
            "user:<chat>\n0+1|a\n[cache]|1+1|b\n</chat>|first\n\nsecond[cache]|[image image/png]"
                .to_string(),
        )
    );
}

/// A `pi.user` entry of `text` placed by an input of `origin`, as the
/// boundary commits it.
fn user_entry(text: &str, origin: InputOrigin) -> eukhe_durable::types::EntryRecord {
    use eukhe_durable::entries::{UserData, USER_ENTRY};
    use eukhe_durable::types::{EntryId, TypedEntryDraft};
    let draft = USER_ENTRY
        .draft(&TypedEntryDraft {
            model: Some(vec![user(text, 1)]),
            data: UserData { origin },
            head: None,
            edits: None,
        })
        .unwrap();
    eukhe_durable::types::EntryRecord {
        model: draft.model,
        data: draft.data,
        edits: None,
        kind: draft.kind,
        id: EntryId::from_number(1),
        conversation_id: ROOT_CONVERSATION_ID,
        head: None,
        by_task_id: None,
    }
}

/// A logged line without images.
fn logged(kind: Kind, text: &str) -> LogLine {
    LogLine {
        kind,
        text: text.to_string(),
        images: Vec::new(),
    }
}

#[test]
fn reports_delivered_as_input_are_logged_as_their_id_line() {
    let exited = Report::ChildExited {
        child: "scout".to_owned(),
        exit: ChildExit::NoReply,
    };
    let failed = Report::ChildFailed {
        child: "scout".to_owned(),
        failure: Some(eukhe_types::input_origin::ChildFailure::Provider {
            kind: eukhe_types::pi_ai::StreamFailureKind::Auth,
        }),
    };
    let message = Report::AgentMessage {
        sender: "child:x".to_owned(),
    };
    let entries = [
        user_entry(
            &exited.render("Last assistant text: hi"),
            InputOrigin::Report { report: exited },
        ),
        user_entry(
            &failed.render("boom"),
            InputOrigin::Report { report: failed },
        ),
        user_entry(
            &message.render("body"),
            InputOrigin::Report { report: message },
        ),
        user_entry(
            "keep going",
            InputOrigin::Goal {
                context: GoalContextKind::Continuation,
            },
        ),
        user_entry(
            "go on",
            InputOrigin::Autonomous {
                nudge: AutonomousNudge::Continuation,
            },
        ),
        user_entry("plain words", InputOrigin::User),
    ];
    let lines: Vec<_> = entries
        .iter()
        .flat_map(|entry| super::lines::entry_lines(entry).unwrap())
        .collect();
    assert_eq!(
        lines,
        vec![
            logged(
                Kind::Work,
                "[child:scout] exited (no-reply)\nLast assistant text: hi"
            ),
            logged(Kind::Work, "[child:scout] failed (provider-auth)\nboom"),
            logged(Kind::Work, "[child:x] body"),
            logged(Kind::User, "plain words"),
        ]
    );
}

/// An input placed as its own `eukhe.custom` input entry (an injected custom
/// turn) is logged by its origin, as its `pi.user` entry was, and leads a
/// call as the user's texts do.
#[test]
fn input_entries_are_logged_by_their_origin() {
    use eukhe_durable::types::{EntryId, EntryRecord};
    let message = Report::AgentMessage {
        sender: "child:x".to_owned(),
    };
    let input = |text: &str, origin: InputOrigin| {
        let entry = crate::durable::input_entry(
            "agent_message",
            UserContent::Text(format!("card {text}")),
            true,
            None,
            origin,
        )
        .unwrap();
        EntryRecord {
            model: Some(vec![user(text, 1)]),
            data: entry.data,
            edits: None,
            kind: entry.kind,
            id: EntryId::from_number(1),
            conversation_id: ROOT_CONVERSATION_ID,
            head: None,
            by_task_id: None,
        }
    };
    let entries = [
        input(
            &message.render("body"),
            InputOrigin::Report { report: message },
        ),
        input(
            "go on",
            InputOrigin::Autonomous {
                nudge: AutonomousNudge::Continuation,
            },
        ),
        input("plain words", InputOrigin::User),
    ];
    let lines: Vec<_> = entries
        .iter()
        .flat_map(|entry| super::lines::entry_lines(entry).unwrap())
        .collect();
    assert_eq!(
        lines,
        vec![
            logged(Kind::Work, "[child:x] body"),
            logged(Kind::User, "plain words"),
        ]
    );
    assert!(entries
        .iter()
        .all(|entry| super::lines::lead_of(entry) == super::lines::Lead::Joins));
}

/// Regression: the user's own words that look like a harness header are
/// logged as the user's words.
#[test]
fn user_words_shaped_like_a_harness_header_are_logged_as_typed() {
    let texts = [
        "[goal: continuation] keep going",
        "[autonomous-continuation]\n\nmore",
        "[child-failed child:scout]\n\nboom",
    ];
    let lines: Vec<_> = texts
        .iter()
        .flat_map(|text| super::lines::entry_lines(&user_entry(text, InputOrigin::User)).unwrap())
        .collect();
    assert_eq!(
        lines,
        texts
            .iter()
            .map(|text| logged(Kind::User, text))
            .collect::<Vec<_>>()
    );
}

/// An agent's answer to the user's `@name` message is logged once as the
/// `work` line `[name] answer`; the answering agent's owed-reply
/// bookkeeping row is never logged.
#[test]
fn agent_replies_are_logged_as_work_and_owed_rows_are_not() {
    use eukhe_durable::types::{EntryId, EntryRecord};
    let custom = |draft: eukhe_durable::types::EntryDraft| EntryRecord {
        model: draft.model,
        data: draft.data,
        edits: None,
        kind: draft.kind,
        id: EntryId::from_number(1),
        conversation_id: ROOT_CONVERSATION_ID,
        head: None,
        by_task_id: None,
    };
    let reply = crate::durable::custom_entry_draft(
        crate::agent_messaging::AGENT_REPLY_CUSTOM_TYPE,
        UserContent::Text(crate::agent_messaging::create_agent_reply_prompt(
            "alpha",
            "I reported 42.",
        )),
        true,
        Some(serde_json::json!({ "id": "r1", "from": "alpha", "message": "I reported 42." })),
        1,
    )
    .unwrap();
    let owed = crate::durable::custom_entry_draft(
        crate::agent_messaging::AGENT_REPLY_OWED_CUSTOM_TYPE,
        UserContent::Text(String::new()),
        false,
        Some(serde_json::json!({ "id": "r1", "replyTo": "root" })),
        1,
    )
    .unwrap();
    assert_eq!(
        [
            super::lines::entry_lines(&custom(reply)).unwrap(),
            super::lines::entry_lines(&custom(owed)).unwrap(),
        ],
        [vec![logged(Kind::Work, "[alpha] I reported 42.")], vec![]]
    );
}

/// A user's text longer than [`CAP`] is logged as several messages in a
/// row, never cut (§1).
#[test]
fn long_user_texts_are_logged_as_several_messages() {
    use eukhe_durable::types::{EntryId, EntryRecord};
    let text = format!("{}{}", "a".repeat(CAP), "b".repeat(7));
    let entry = EntryRecord {
        model: Some(vec![user(&text, 1)]),
        data: None,
        edits: None,
        kind: "pi.user".to_string(),
        id: EntryId::from_number(1),
        conversation_id: ROOT_CONVERSATION_ID,
        head: None,
        by_task_id: None,
    };
    assert_eq!(
        super::lines::entry_lines(&entry).unwrap(),
        vec![
            logged(Kind::User, &"a".repeat(CAP)),
            logged(Kind::User, &"b".repeat(7))
        ]
    );
}

/// Thoughts are shown but never logged, and a tool's output is clipped to
/// its head and tail, [`CAP`] characters in all, as one message (§1).
#[test]
fn thoughts_are_never_logged_and_tool_output_is_clipped() {
    use eukhe_ai::providers::faux::{faux_text, faux_thinking};
    use eukhe_durable::entries::{ASSISTANT_ENTRY, TOOL_RESULT_ENTRY};
    use eukhe_durable::types::{EntryId, EntryRecord};
    let entry = |kind: &str, message: Message| EntryRecord {
        model: Some(vec![message]),
        data: None,
        edits: None,
        kind: kind.to_string(),
        id: EntryId::from_number(1),
        conversation_id: ROOT_CONVERSATION_ID,
        head: None,
        by_task_id: None,
    };
    let serde_json::Value::Object(arguments) = serde_json::json!({ "id": 0 }) else {
        panic!("tool arguments are an object");
    };
    let said = entry(
        ASSISTANT_ENTRY.kind(),
        Message::Assistant(faux_assistant_message(
            vec![
                faux_thinking("a secret plan"),
                faux_text("on it"),
                faux_tool_call("date", arguments, Some("c1".to_string())),
                faux_thinking("more thoughts"),
                faux_text("done"),
            ],
            FauxAssistantMessageOptions::default(),
        )),
    );
    let output = format!("{}{}", "a".repeat(CAP), "b".repeat(CAP));
    let read = entry(
        TOOL_RESULT_ENTRY.kind(),
        serde_json::from_value(serde_json::json!({
            "role": "toolResult",
            "toolCallId": "c1",
            "toolName": "date",
            "content": [{ "type": "text", "text": output }],
            "isError": false,
            "timestamp": 1
        }))
        .unwrap(),
    );
    assert_eq!(
        [
            super::lines::entry_lines(&said).unwrap(),
            super::lines::entry_lines(&read).unwrap(),
        ],
        [
            vec![
                logged(Kind::Eukhe, "on it"),
                logged(Kind::Tool, r#"date {"id":0}"#),
                logged(Kind::Eukhe, "done"),
            ],
            vec![logged(Kind::Echo, &crate::memory::cap_text(&output))],
        ]
    );
}

/// The images a user message or a tool result carries are logged with
/// the message, so `zoom(id, 1)` gives them back (§5); the text keeps
/// `[image: mime]` in their place.
#[test]
fn images_ride_with_their_logged_message() {
    use eukhe_durable::entries::{TOOL_RESULT_ENTRY, USER_ENTRY};
    use eukhe_durable::types::{EntryId, EntryRecord};
    let image = ImageContent {
        data: "AAAA".to_string(),
        mime_type: "image/png".to_string(),
    };
    let entry = |kind: &str, message: Message| EntryRecord {
        model: Some(vec![message]),
        data: None,
        edits: None,
        kind: kind.to_string(),
        id: EntryId::from_number(1),
        conversation_id: ROOT_CONVERSATION_ID,
        head: None,
        by_task_id: None,
    };
    let said = entry(
        USER_ENTRY.kind(),
        Message::User(UserMessage {
            content: UserContent::Blocks(vec![
                UserContentBlock::Text(TextContent::new("look")),
                UserContentBlock::Image(image.clone()),
            ]),
            timestamp: 1,
        }),
    );
    let read = entry(
        TOOL_RESULT_ENTRY.kind(),
        serde_json::from_value(serde_json::json!({
            "role": "toolResult",
            "toolCallId": "c1",
            "toolName": "read",
            "content": [
                { "type": "text", "text": "a.png" },
                { "type": "image", "data": "AAAA", "mimeType": "image/png" }
            ],
            "isError": false,
            "timestamp": 1
        }))
        .unwrap(),
    );
    assert_eq!(
        [
            super::lines::entry_lines(&said).unwrap(),
            super::lines::entry_lines(&read).unwrap(),
        ],
        [
            vec![LogLine {
                kind: Kind::User,
                text: "look\n[image: image/png]".to_string(),
                images: vec![image.clone()],
            }],
            vec![LogLine {
                kind: Kind::Echo,
                text: "a.png\n[image: image/png]".to_string(),
                images: vec![image],
            }],
        ]
    );
}

/// The model's `zoom(id, 1)` gets the message whole with its images.
#[tokio::test]
async fn the_zoom_tool_gives_a_message_with_its_images() {
    let setup = Setup::new(MemoryRole::Root).await;
    setup
        .memory
        .append_keyed(
            Kind::User,
            "look\n[image: image/png]",
            vec![ImageContent {
                data: "AAAA".to_string(),
                mime_type: "image/png".to_string(),
            }],
            AppendKey {
                scope: "earlier".to_string(),
                seq: 0,
            },
        )
        .await
        .unwrap();
    let requests = Requests::default();
    setup.faux.set_responses(vec![
        requests.step(call("zoom", serde_json::json!({ "id": 0, "n": 1 }))),
        requests.step(answer("done")),
    ]);
    let session = setup
        .open(Arc::new(MemoryStorage::new()), Logging::On)
        .await;
    session.run(&setup.chat, "what did I show you?").await;
    let results: Vec<String> = requests
        .all()
        .last()
        .unwrap()
        .iter()
        .filter(|message| matches!(message, Message::ToolResult(_)))
        .map(describe)
        .collect();
    assert_eq!(
        results,
        vec!["toolResult:0+0|user: look\n[image: image/png]|[image image/png]".to_string()]
    );
    session.close(&setup).await;
}

/// `zoom("Name")` gives the whole chat of the subagent the conversation
/// spawned, by its name with or without the `child:` of its reports; its
/// steps are in its own session, never in the chat (§6).
#[tokio::test]
async fn zoom_by_name_gives_an_agents_whole_chat() {
    use crate::durable::children::{tx_put_row, ChildRow, ChildStatus};
    let setup = Setup::new(MemoryRole::Subagent).await;
    let requests = Requests::default();
    setup.faux.set_responses(vec![
        requests.step(call("date", serde_json::json!({ "id": 0 }))),
        requests.step(answer("found it")),
    ]);
    setup.memory.append(Kind::User, "earlier").await.unwrap();
    let child = setup.open(setup.jsonl().await, Logging::Off).await;
    child.run(&setup.chat, "find the bug").await;
    child.close(&setup).await;
    let date = setup.memory.date(0).await.unwrap();
    let parent = setup
        .open(Arc::new(MemoryStorage::new()), Logging::Off)
        .await;
    let row = ChildRow {
        task_id: 7,
        rlm_child_id: "sub-1".to_string(),
        session_id: "child-session".to_string(),
        session_name: "scout".to_string(),
        label: "find the bug".to_string(),
        started_at: 0.0,
        status: ChildStatus::Done,
        active_session_id: None,
        session_dir: Some(
            setup
                .dir
                .path()
                .join("session")
                .to_string_lossy()
                .into_owned(),
        ),
        model: None,
        answer_preview: None,
        error: None,
        failure: None,
        replied_since_task: false,
        deletion: None,
        settled: true,
        usage: None,
        progress: None,
        reporter: None,
        handback: None,
        phase: None,
        answer: None,
    };
    parent
        .harness
        .commit(
            move |tx| async move { tx_put_row(&tx, ROOT_CONVERSATION_ID, &row).await },
            cx(),
        )
        .await
        .unwrap();
    let mut chats = Vec::new();
    for name in ["child:scout", "scout", "child:nobody"] {
        chats.push(
            super::tools::agent_chat(&parent.harness, ROOT_CONVERSATION_ID, name, cx())
                .await
                .unwrap(),
        );
    }
    assert_eq!(
        (chats, chat_lines(&setup.chat_dir())),
        (
            vec![
                format!(
                    "user: find the bug\ntool: date {{\"id\":0}}\necho: {date}\neukhe: found it"
                ),
                format!(
                    "user: find the bug\ntool: date {{\"id\":0}}\necho: {date}\neukhe: found it"
                ),
                "No agent child:nobody.".to_string(),
            ],
            vec![(Kind::User, "earlier".to_string())],
        )
    );
    parent.close(&setup).await;
}

/// A message the user sends while a call runs reaches it between tool
/// calls, in the same call (its first message stays the pinned view), and
/// is logged as `user` where it came (§6).
#[tokio::test]
async fn a_message_sent_during_a_call_joins_it_between_tool_calls() {
    let setup = Setup::new(MemoryRole::Root).await;
    let requests = Requests::default();
    setup.faux.set_responses(vec![
        requests.step(call("hold", serde_json::json!({}))),
        requests.step(answer("done")),
    ]);
    let session = setup
        .open(Arc::new(MemoryStorage::new()), Logging::On)
        .await;
    let started = setup.started.notified();
    session.submit("hello").await;
    started.await;
    session.steer("also this").await;
    setup.release.notify_one();
    session.root.wait_for_idle(cx()).await.unwrap();
    setup.chat.flush().await.unwrap();
    let all = requests.described();
    assert_eq!(
        (
            all.len(),
            all[1][1] == all[0][1],
            all[1][2..].to_vec(),
            chat_lines(&setup.chat_dir()),
        ),
        (
            2,
            true,
            vec![
                "assistant:call hold".to_string(),
                "toolResult:held".to_string(),
                "user:also this".to_string(),
            ],
            vec![
                (Kind::User, "hello".to_string()),
                (Kind::Tool, "hold {}".to_string()),
                (Kind::Echo, "held".to_string()),
                (Kind::User, "also this".to_string()),
                (Kind::Eukhe, "done".to_string()),
            ],
        )
    );
    session.close(&setup).await;
}

/// A request transform that fails ends the turn as failed, with the
/// transform's error, and nothing goes to the model (H6.1). A failed hook
/// used to be reported and skipped, and the request went out with the raw
/// transcript in place of the view.
#[tokio::test]
async fn a_failed_transform_fails_the_turn_and_sends_nothing() {
    let setup = Setup::new(MemoryRole::Root).await;
    let requests = Requests::default();
    setup
        .faux
        .set_responses(vec![requests.step(answer("unseen"))]);
    let session = setup
        .open(Arc::new(MemoryStorage::new()), Logging::Off)
        .await;
    // The session's harness is closed: the request transform fails before
    // anything goes to the model.
    setup.cell.clear();
    let settled = session
        .root
        .submit(
            InputSubmissionDraft {
                request_id: None,
                content: UserContent::Text("hello".to_string()),
                when_busy: None,
                origin: InputOrigin::User,
                entry: None,
            },
            cx(),
        )
        .await
        .unwrap()
        .wait(cx())
        .await
        .unwrap();
    assert_eq!(
        (
            requests.described(),
            settled.state.reason(),
            settled
                .state
                .detail()
                .and_then(|detail| detail.as_str().map(str::to_owned)),
            lock(&setup.reports).clone(),
        ),
        (
            Vec::<Vec<String>>::new(),
            Some("model_error"),
            Some("A request hook failed: Harness is closed".to_string()),
            Vec::<String>::new(),
        )
    );
    session.harness.close(cx()).await.unwrap();
}
