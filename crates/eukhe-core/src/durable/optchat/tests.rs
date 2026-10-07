//! `eukhe.optchat` over a real Harness, a faux model, and a real chat
//! memory in a temp dir.

use std::path::Path;
use std::sync::{Arc, Mutex, PoisonError};

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
use eukhe_pi_ai::models::{create_models, CreateModelsOptions, Models};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_provider, faux_tool_call, FauxAssistantMessageOptions,
    FauxProviderHandle, FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_types::pi_ai::{
    AssistantContentBlock, CacheBreakpoint, ImageContent, Message, StopReason, SystemContent,
    SystemMessage, TextContent, UserContent, UserContentBlock, UserMessage,
};
use tokio::sync::Notify;

use super::docs::{decode, write, CallState, LoggedState, LOGGED_DOC};
use super::logger::LoggerHandle;
use super::request::request_messages;
use super::OptChat;
use crate::durable::{HarnessCell, TurnWait, TurnWaitSink};
use crate::memory::{
    AppendKey, Kind, Memory, MemoryRole, Summarizer, SummarizerFuture, CAP, DATE_TOOL_DESCRIPTION,
    ZOOM_TOOL_DESCRIPTION,
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
    fn complete(&self, _context: eukhe_types::ai::Context) -> SummarizerFuture {
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
    /// What the Harness reported.
    reports: Arc<Mutex<Vec<String>>>,
}

impl Setup {
    async fn new(role: MemoryRole) -> Setup {
        Setup::with_sink(role, None).await
    }

    async fn with_sink(role: MemoryRole, turn_wait: Option<TurnWaitSink>) -> Setup {
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
            cell.clone(),
            turn_wait,
        );
        let registry = create_registry();
        registry.install(chat.extension()).unwrap();
        let started = Arc::new(Notify::new());
        registry
            .install(define_extension(Extension {
                tools: vec![wait_tool(Arc::clone(&started))],
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
                JsonlStorageOptions { fsync: false },
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

/// The view as the call's first message shows it: one text piece here.
async fn view_text(memory: &Memory) -> String {
    let rendered = memory.render().await.unwrap();
    let pieces = rendered.pieces();
    assert_eq!(pieces.len(), 1, "a short view is one piece");
    pieces[0].clone()
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
    let zoomed = setup.memory.zoom(0, 1).await.unwrap();
    let after_first = chat_lines(&setup.chat_dir());
    let second_view = view_text(&setup.memory).await;
    session.run(&setup.chat, "again").await;
    let first_user = format!("user:{first_view}|hello");
    assert_eq!(
        (
            requests.described(),
            after_first,
            setup.chat.turn.lock().await.held()
        ),
        (
            vec![
                vec!["system".to_string(), first_user.clone()],
                vec![
                    "system".to_string(),
                    first_user,
                    "assistant:call zoom".to_string(),
                    format!("toolResult:{zoomed}"),
                ],
                vec!["system".to_string(), format!("user:{second_view}|again")],
            ],
            vec![
                (Kind::User, "earlier".to_string()),
                (Kind::User, "hello".to_string()),
                (Kind::Tool, r#"zoom {"id":0,"n":1}"#.to_string()),
                (Kind::Echo, zoomed),
                (Kind::Talk, "done".to_string()),
            ],
            false,
        )
    );
    // The first message of a run is byte-identical across its requests.
    let all = requests.all();
    assert_eq!(all[0][1], all[1][1]);
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
                    "properties": {
                        "id": { "type": "integer", "minimum": 0 },
                        "n": { "type": "integer", "minimum": 1 }
                    },
                    "required": ["id", "n"],
                    "additionalProperties": false
                }),
            ),
            (
                "date".to_string(),
                DATE_TOOL_DESCRIPTION.to_string(),
                serde_json::json!({
                    "type": "object",
                    "properties": { "id": { "type": "integer", "minimum": 0 } },
                    "required": ["id"],
                    "additionalProperties": false
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
    let zoomed = setup.memory.zoom(0, 1).await.unwrap();
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
            Kind::Talk
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
                vec!["system".to_string(), format!("user:{view}|task")],
                vec![
                    "system".to_string(),
                    format!("user:{view}|task"),
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

#[tokio::test]
async fn a_call_behind_another_windows_turn_reports_the_wait_until_granted() {
    let waits: Arc<Mutex<Vec<TurnWait>>> = Arc::default();
    let waiting = Arc::new(Notify::new());
    let sink: TurnWaitSink = {
        let waits = Arc::clone(&waits);
        let waiting = Arc::clone(&waiting);
        Arc::new(move |wait| {
            lock(&waits).push(wait);
            if wait == TurnWait::Waiting {
                waiting.notify_one();
            }
        })
    };
    let setup = Setup::with_sink(MemoryRole::Root, Some(sink)).await;
    let other_window = Memory::open(setup.chat_dir(), Arc::new(NoModel))
        .await
        .unwrap();
    let other_turn = other_window.acquire_turn().await.unwrap();
    let requests = Requests::default();
    setup
        .faux
        .set_responses(vec![requests.step(answer("done"))]);
    let session = setup
        .open(Arc::new(MemoryStorage::new()), Logging::On)
        .await;
    let shown = waiting.notified();
    session.submit("hello").await;
    shown.await;
    let before_grant = (requests.all().len(), lock(&waits).clone());
    other_turn.release().await.unwrap();
    session.root.wait_for_idle(cx()).await.unwrap();
    setup.chat.flush().await.unwrap();
    assert_eq!(
        (before_grant, requests.all().len(), lock(&waits).clone()),
        (
            (0, vec![TurnWait::Waiting]),
            1,
            vec![TurnWait::Waiting, TurnWait::Cleared]
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
/// first message; earlier messages dropped.
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
    let request = request_messages(&call, messages, 2, |message| *message == state);
    let Message::System(system) = &request[0] else {
        panic!("a system message leads");
    };
    assert_eq!(
        (
            system.content.clone(),
            request[1..].iter().map(describe).collect::<Vec<_>>(),
            request[1].clone()
        ),
        (
            SystemContent::Text("base\n\npatch".to_string()),
            vec![
                "user:<chat>\n0+1|a\n[cache]|1+1|b\n</chat>|first\n\nsecond|[image image/png]"
                    .to_string(),
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
                    UserContentBlock::Text(TextContent::new("first\n\nsecond")),
                    image,
                ]),
                timestamp: 7,
            }),
        )
    );
}

#[test]
fn tool_results_over_the_cap_keep_head_and_tail_and_images() {
    let image = UserContentBlock::Image(ImageContent {
        data: "AA==".to_string(),
        mime_type: "image/png".to_string(),
    });
    let long = "x".repeat(CAP + 10);
    let result = ToolExecutionResult {
        content: Some(vec![
            UserContentBlock::Text(TextContent::new(long.as_str())),
            image.clone(),
        ]),
        is_error: Some(true),
        ..ToolExecutionResult::default()
    };
    let short = ToolExecutionResult {
        content: Some(vec![UserContentBlock::Text(TextContent::new("short"))]),
        ..ToolExecutionResult::default()
    };
    assert_eq!(
        (super::tools::capped(&result), super::tools::capped(&short)),
        (
            Some(ToolExecutionResult {
                content: Some(vec![
                    UserContentBlock::Text(TextContent::new(crate::memory::cap_text(&long))),
                    image,
                ]),
                is_error: Some(true),
                ..ToolExecutionResult::default()
            }),
            None
        )
    );
}

#[test]
fn reports_delivered_as_input_are_logged_as_their_id_line() {
    use eukhe_durable::types::{EntryId, EntryRecord};
    let input = |text: &str| EntryRecord {
        model: Some(vec![user(text, 1)]),
        data: None,
        edits: None,
        kind: "pi.user".to_string(),
        id: EntryId::from_number(1),
        conversation_id: ROOT_CONVERSATION_ID,
        head: None,
        by_task_id: None,
    };
    let lines: Vec<_> = [
        "[child-exited: no-reply child:scout]\n\nLast assistant text: hi",
        "[child-failed child:scout]\n\nboom",
        "[agent-message from child:x]\n\nbody",
        "[goal: continuation] keep going",
        "plain words",
    ]
    .iter()
    .flat_map(|text| super::lines::entry_lines(&input(text)))
    .collect();
    assert_eq!(
        lines,
        vec![
            (
                Kind::User,
                "[child:scout] exited (no-reply)\nLast assistant text: hi".to_string()
            ),
            (Kind::User, "[child:scout] failed\nboom".to_string()),
            (Kind::User, "[child:x] body".to_string()),
            (Kind::User, "plain words".to_string()),
        ]
    );
}
