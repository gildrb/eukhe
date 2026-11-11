use std::path::Path;

use eukhe_ai::providers::faux_script::{
    create_faux_script_models, parse_faux_script, FauxScriptProvider,
};
use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::durable::{open_session, ModelRequest, SessionConfig, SessionStorage};

use super::*;
use crate::headless_terminal::HeadlessPrimary;
use crate::mode::{RuntimeConfig, SessionOptions};

/// A session on the scripted faux provider (the print harness's
/// `EUKHE_FAUX_SCRIPT` models without the environment), hosted as print
/// mode hosts it.
async fn faux_session(
    dir: &Path,
    script: &serde_json::Value,
    storage: SessionStorage,
) -> (EukheSession, FauxScriptProvider) {
    let script = parse_faux_script(&script.to_string()).expect("faux script");
    let model = script.model.id.clone();
    let (models, provider) = create_faux_script_models(script);
    let mut config = SessionConfig::new(
        dir.join("agent"),
        dir,
        "0198f000-0000-7000-8000-000000000000",
        storage,
    );
    config.models = Some(models);
    config.model = Some(ModelRequest {
        provider: Some("faux".to_owned()),
        pattern: model,
    });
    config.host = AppMode::Print.session_host();
    let session = open_session(config, &BACKGROUND_CONTEXT)
        .await
        .expect("open the faux session");
    (session, provider)
}

fn run_options(dir: &Path, prompts: &[&str]) -> RunOptions {
    RunOptions {
        app_mode: AppMode::Print,
        config: RuntimeConfig {
            cwd: dir.to_path_buf(),
            agent_dir: dir.join("agent"),
            ..RuntimeConfig::default()
        },
        session: SessionOptions::default(),
        messages: prompts[1..]
            .iter()
            .map(|&prompt| prompt.to_owned())
            .collect(),
        file_args: Vec::new(),
        daemon_socket: None,
        list_models: None,
        initial_message: prompts.first().map(|&prompt| prompt.to_owned()),
        initial_images: Vec::new(),
        verbose: false,
        offline: false,
        agents_view_requested: false,
        attach_agent: None,
    }
}

/// Run the prompt loop on a faux session, select the terminal result, and
/// close the session as print mode does.
async fn run_in(
    dir: &Path,
    storage: SessionStorage,
    script: &serde_json::Value,
    prompts: &[&str],
) -> (
    Option<String>,
    crate::headless_terminal::HeadlessTerminalResult,
    FauxScriptProvider,
) {
    let (session, provider) = faux_session(dir, script, storage).await;
    let opened = HeadlessSession {
        session: Arc::new(session),
        lease: None,
        session_id: "0198f000-0000-7000-8000-000000000000".to_owned(),
        cwd: dir.to_path_buf(),
        parent_session: None,
        wakes: eukhe_daemon::job_notices::HeadlessWakes::default(),
    };
    let conversation = opened.session.main();
    let cx = &*BACKGROUND_CONTEXT;
    let watch = RunWatch::start(&opened, &conversation, cx)
        .await
        .expect("the run watch starts");
    let ended = drive_prompts(
        &opened,
        &conversation,
        &watch,
        &run_options(dir, prompts),
        cx,
    )
    .await
    .expect("the prompt loop runs");
    let failure = match ended {
        PromptsEnd::Completed => None,
        PromptsEnd::CommandFailed(error) => Some(error.to_string()),
        PromptsEnd::GaveUp(work) => panic!("nothing runs in the background: {work:?}"),
    };
    let result = select_terminal_result(&conversation, cx)
        .await
        .expect("terminal selection");
    watch.finish().await;
    drop(conversation);
    let Ok(session) = Arc::try_unwrap(opened.session) else {
        panic!("the test holds the only session handle");
    };
    session.close(cx).await.expect("close");
    (failure, result, provider)
}

/// [`run_in`] on a memory session in a fresh directory.
async fn run(
    script: &serde_json::Value,
    prompts: &[&str],
) -> (
    Option<String>,
    crate::headless_terminal::HeadlessTerminalResult,
) {
    let dir = tempfile::TempDir::new().expect("tempdir");
    let (failure, result, _provider) =
        run_in(dir.path(), SessionStorage::Memory, script, prompts).await;
    (failure, result)
}

#[tokio::test]
async fn every_prompt_answers_in_order_and_the_last_answer_is_the_result() {
    let (failure, result) = run(
        &serde_json::json!({ "responses": ["first answer", "second answer"] }),
        &["one", "two"],
    )
    .await;
    assert_eq!(failure, None);
    let primary = result.primary.expect("a primary answer");
    assert_eq!(primary.failure(), None);
    assert_eq!(primary.stdout_text(), "second answer");
}

/// A print run sends nothing after its final answer, even when its turn
/// compacted: the compact-trigger review would start at the idle right
/// before the exit, which cancels its request after its prompt was paid
/// for (bench longmem: one main-model review per compaction, every one
/// cancelled). The overflow error compacts the turn, the summary and the
/// retried answer are the run's last scripted requests.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_print_run_sends_no_request_after_its_final_answer() {
    let dir = tempfile::TempDir::new().expect("tempdir");
    let agent_dir = dir.path().join("agent");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    // The keep window leaves the seed turn before the cut.
    std::fs::write(
        agent_dir.join("settings.json"),
        serde_json::json!({
            "compaction": { "enabled": true, "reserveTokens": 1, "keepRecentTokens": 10 }
        })
        .to_string(),
    )
    .expect("settings");
    let script = serde_json::json!({
        "responses": [
            {"text": "seed reply"},
            {
                "content": [{ "type": "text", "text": "" }],
                "stopReason": "error",
                "errorMessage": "prompt is too long: 213462 tokens > 200000 maximum",
            },
            {"text": "the summary"},
            {"text": "recovered reply"},
        ]
    });
    let seed = format!("seed turn {}", "x".repeat(48_000));
    let probe = format!("overflow probe {}", "x".repeat(48_000));
    let storage = SessionStorage::Jsonl {
        dir: dir.path().join("sessions").join("print"),
        fsync: false,
    };
    let (failure, result, provider) = run_in(dir.path(), storage, &script, &[&seed, &probe]).await;
    assert_eq!(failure, None);
    let primary = result.primary.expect("the recovered answer");
    assert_eq!(primary.stdout_text(), "recovered reply");
    // The session is closed: a request it started after the answer would
    // have been counted by now.
    assert_eq!(provider.call_count(), 4);
}

/// A reply that hit the output limit with room left in the window is the
/// run's answer (the stop Directors keep it, as omp keeps such a turn):
/// the truncated answer is the primary, the warning row that trails it is
/// reported with it and never taken for the result, and the run sends no
/// second request.
#[tokio::test]
async fn a_truncated_answer_is_the_result_and_its_warning_trails_it() {
    let dir = tempfile::TempDir::new().expect("tempdir");
    let script = serde_json::json!({
        "responses": [
            { "text": "Here is the whole plan: first", "stopReason": "length" },
            "unused",
        ]
    });
    let (failure, result, provider) =
        run_in(dir.path(), SessionStorage::Memory, &script, &["go"]).await;
    let primary = result.primary.expect("the truncated answer");
    assert_eq!(
        (
            failure,
            primary.stdout_text(),
            primary.kind(),
            primary.failure(),
            result.warnings,
            provider.call_count()
        ),
        (
            None,
            "Here is the whole plan: first".to_owned(),
            eukhe_bend::rules::headless::Primary::Answer,
            None,
            vec![
                "Response hit the faux/faux-1 output limit (8 tokens) and was truncated."
                    .to_owned()
            ],
            1
        )
    );
}

/// A reply that hit the output limit with text in a window that is
/// unknown (0, which counts as run out, as omp counts it) and no
/// compaction to make is dropped: omp removes the turn from its active
/// context and ends the run with no notice (`session-maintenance.ts`
/// :3412-3415, :3528-3533), so its print mode prints no result. The run
/// has no primary, no warning and no failure, and sends no second request.
#[tokio::test]
async fn a_dropped_truncated_reply_is_no_result_and_has_no_warning() {
    let dir = tempfile::TempDir::new().expect("tempdir");
    let script = serde_json::json!({
        "contextWindow": 0,
        "responses": [
            { "text": "Here is the whole plan: first", "stopReason": "length" },
            "unused",
        ]
    });
    let (failure, result, provider) =
        run_in(dir.path(), SessionStorage::Memory, &script, &["go"]).await;
    assert_eq!(
        (
            failure,
            result.primary,
            result.warnings,
            provider.call_count()
        ),
        (None, None, Vec::<String>::new(), 1)
    );
}

#[tokio::test]
async fn an_unscripted_request_fails_the_run_with_its_error() {
    let (failure, result) = run(&serde_json::json!({ "responses": [] }), &["hi"]).await;
    assert_eq!(failure, None);
    let primary = result.primary.expect("the failed assistant turn");
    assert!(
        matches!(primary, HeadlessPrimary::Assistant(_)),
        "{primary:?}"
    );
    let Some(RunFailure::Message(stderr)) = primary.failure() else {
        panic!("exit 1 with stderr text");
    };
    assert!(!stderr.is_empty());
}

#[tokio::test]
async fn a_failed_session_command_stops_the_prompt_loop() {
    let (failure, result) = run(
        &serde_json::json!({ "responses": ["never"] }),
        &["/autonomous status extra", "never asked"],
    )
    .await;
    let error = failure.expect("the command failed");
    assert!(!error.is_empty());
    // The later prompt never ran: the failure row is the terminal entry.
    match result.primary.expect("the failure row") {
        HeadlessPrimary::SlashCommandResult {
            content, success, ..
        } => {
            assert!(!success);
            assert_eq!(content, format!("Command failed: {error}"));
        }
        HeadlessPrimary::Assistant(message) => panic!("no model turn expected: {message:?}"),
    }
}

#[test]
fn the_session_header_carries_the_ts_fields_in_order() {
    let opened_cwd = std::path::PathBuf::from("/work/project");
    let header = header_for("0198f000-0000-7000-8000-000000000001", &opened_cwd, None);
    let keys: Vec<&str> = header
        .as_object()
        .expect("object")
        .keys()
        .map(String::as_str)
        .collect();
    assert_eq!(
        keys,
        ["type", "version", "id", "timestamp", "cwd", "rlmDepth"]
    );
    assert_eq!(header["type"], "session");
    assert_eq!(header["version"], 3);
    assert_eq!(header["cwd"], "/work/project");
    assert_eq!(header["rlmDepth"], 0);
    let forked = header_for(
        "0198f000-0000-7000-8000-000000000002",
        &opened_cwd,
        Some(Path::new("/sessions/source")),
    );
    assert_eq!(forked["parentSession"], "/sessions/source");
}

#[test]
fn image_prompts_carry_the_text_then_the_images() {
    assert_eq!(
        user_content("plain", Vec::new()),
        UserContent::Blocks(vec![UserContentBlock::Text(
            eukhe_types::pi_ai::TextContent::new("plain")
        )])
    );
    let image = ImageContent {
        data: "aGk=".to_owned(),
        mime_type: "image/png".to_owned(),
    };
    assert_eq!(
        user_content("look", vec![image.clone()]),
        UserContent::Blocks(vec![
            UserContentBlock::Text(eukhe_types::pi_ai::TextContent::new("look")),
            UserContentBlock::Image(image),
        ])
    );
}

// --- print-mode MCP wiring (TS `createAgentSessionServices` parity) ---

/// The print session's MCP manager serves a settings-declared server
/// through the `mcp.config` host request the kernel dispatches
/// (`rlm/mcp.py` resolution), and resolves its settings LIVE: a
/// settings rewrite reaches the next `refresh()` -- the re-resolver
/// the remote-catalog change subscription drives mid-session. The
/// `mcp.config` handler itself keeps the registration-time
/// integrations (the eukhe-core handler design, shared with the daemon
/// worker), so the pre-refresh handler still answers the old roster --
/// asserted here so the test states the real production behavior.
#[tokio::test]
async fn print_mode_mcp_manager_serves_settings_servers_and_resolves_live() {
    let home = tempfile::TempDir::new().unwrap();
    let cwd = home.path().to_path_buf();
    let agent_dir = home.path().join("agent");
    std::fs::create_dir_all(&agent_dir).unwrap();
    std::fs::write(
        agent_dir.join("settings.json"),
        serde_json::json!({
            "mcpServers": {
                "fixture-echo": {
                    "type": "stdio",
                    "command": "python3",
                    "args": ["echo.py"]
                }
            }
        })
        .to_string(),
    )
    .unwrap();
    let built_manager = crate::mcp_login::cli_mcp_manager(&cwd, &agent_dir);
    assert_eq!(
        built_manager.get_enabled_persistent_generic_servers(),
        vec!["fixture-echo".to_string()]
    );
    let manager = std::sync::Arc::new(std::sync::Mutex::new(built_manager));
    // The kernel's config host request serves the declared server with
    // the declared stdio config (registration-time integrations).
    let mut handlers = eukhe_core::kernel::shared::HostRequestHandlers::default();
    eukhe_core::mcp::McpManager::register_host_handlers(&manager, &mut handlers);
    let config = handlers.get("mcp.config").unwrap().clone();
    let result = config(eukhe_core::kernel::shared::HostRequestPayload {
        data: serde_json::json!({ "server": "fixture-echo" }),
        cell_source_code: None,
    })
    .await
    .unwrap();
    assert_eq!(result["type"], "stdio");
    assert_eq!(result["command"], "python3");
    assert_eq!(result["args"], serde_json::json!(["echo.py"]));
    // A settings rewrite reaches the same manager on the next refresh:
    // the closures re-read settings per resolution.
    std::fs::write(
        agent_dir.join("settings.json"),
        serde_json::json!({
            "mcpServers": {
                "second-echo": {
                    "type": "stdio",
                    "command": "node",
                    "args": ["echo.mjs"]
                }
            }
        })
        .to_string(),
    )
    .unwrap();
    {
        let mut manager = manager.lock().unwrap();
        manager.refresh();
        assert_eq!(
            manager.get_enabled_persistent_generic_servers(),
            vec!["second-echo".to_string()]
        );
    }
    // The already-registered handler keeps its registration-time
    // integrations -- the registration shape a live session dispatches.
    let result = config(eukhe_core::kernel::shared::HostRequestPayload {
        data: serde_json::json!({ "server": "fixture-echo" }),
        cell_source_code: None,
    })
    .await
    .unwrap();
    assert_eq!(
        result["command"], "python3",
        "the registered handler serves its registration-time integrations"
    );
    let missing = config(eukhe_core::kernel::shared::HostRequestPayload {
        data: serde_json::json!({ "server": "second-echo" }),
        cell_source_code: None,
    })
    .await
    .unwrap();
    assert!(
        missing.as_object().unwrap().is_empty(),
        "the pre-refresh handler does not know the new server"
    );
}

/// Local service-catalog sources (`mcpCatalogSources`) reach the print
/// manager's catalog resolution (TS `getCatalogSources`): the declared
/// file's entry surfaces as a local descriptor, and dropping the
/// declaration withdraws it on the next resolve -- the same live
/// settings read as the user-server closure.
#[test]
fn print_mode_mcp_manager_resolves_declared_catalog_sources() {
    let home = tempfile::TempDir::new().unwrap();
    let agent_dir = home.path().join("agent");
    std::fs::create_dir_all(&agent_dir).unwrap();
    let catalog = home.path().join("local-catalog.json");
    std::fs::write(
        &catalog,
        serde_json::json!({
            "version": 1,
            "entries": [{
                "server": "my-local", "service": "my-local", "label": "My Local",
                "url": "https://my-local.example/mcp", "aliases": [],
                "transport": { "type": "http", "url": "https://my-local.example/mcp" },
                "auth": { "strategy": "oauth", "clientRegistration": "dynamic" },
                "setup": { "status": "ready" },
                "verification": { "status": "unverified" },
                "legacyBuiltin": false,
                "provenance": [{ "source": "user" }]
            }]
        })
        .to_string(),
    )
    .unwrap();
    let settings = |sources: &[&str]| {
        serde_json::json!({
            "mcpCatalogSources": sources
                .iter()
                .map(std::string::ToString::to_string)
                .collect::<Vec<_>>()
        })
        .to_string()
    };
    std::fs::write(
        agent_dir.join("settings.json"),
        settings(&[&catalog.display().to_string()]),
    )
    .unwrap();
    let mut manager = crate::mcp_login::cli_mcp_manager(home.path(), &agent_dir);
    let my_local = manager
        .service_descriptors()
        .iter()
        .find(|service| service.service_id == "my-local")
        .expect("declared source entry resolved");
    assert!(my_local.local_source);
    // Live: dropping the declaration withdraws the entry on refresh.
    std::fs::write(agent_dir.join("settings.json"), settings(&[])).unwrap();
    manager.refresh();
    assert!(
        !manager
            .service_descriptors()
            .iter()
            .any(|service| service.service_id == "my-local"),
        "the dropped source no longer resolves"
    );
}

/// Runtime shutdown cancels the task blocking a pending writer; the print
/// lease must stay held until that blocking writer finishes, on the
/// success, error, and unwinding paths alike.
#[test]
fn print_lease_outlives_runtime_writers_on_every_return_path() {
    #[derive(Clone, Copy)]
    enum Outcome {
        Success,
        Error,
        Panic,
    }
    struct Fixture {
        session_path: std::path::PathBuf,
        agent_dir: std::path::PathBuf,
        outcome: Outcome,
    }
    struct UnblockWriter(std::sync::mpsc::Sender<()>);
    impl Drop for UnblockWriter {
        fn drop(&mut self) {
            let _ = self.0.send(());
        }
    }
    for outcome in [Outcome::Success, Outcome::Error, Outcome::Panic] {
        let home = tempfile::TempDir::new().unwrap();
        let fixture = Fixture {
            session_path: home.path().join("session.jsonl"),
            agent_dir: home.path().join("agent"),
            outcome,
        };
        let held_at_write = Arc::new(std::sync::atomic::AtomicBool::new(false));
        let writer_observation = Arc::clone(&held_at_write);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            with_print_runtime(&fixture, |fixture, lease| {
                Box::pin(async move {
                    *lease = Some(
                        eukhe_daemon::lease::acquire_runtime_session_lease(
                            &fixture.session_path,
                            &fixture.agent_dir,
                        )
                        .unwrap(),
                    );
                    // An async task parked forever: only the runtime drop
                    // cancels it, and its drop unblocks the writer.
                    let (cancel_tx, cancel_rx) = std::sync::mpsc::channel();
                    let (ready_tx, ready_rx) = tokio::sync::oneshot::channel();
                    tokio::spawn(async move {
                        let _unblock = UnblockWriter(cancel_tx);
                        let _ = ready_tx.send(());
                        std::future::pending::<()>().await;
                    });
                    ready_rx.await.unwrap();
                    let session_path = fixture.session_path.clone();
                    let agent_dir = fixture.agent_dir.clone();
                    let (writer_ready_tx, writer_ready_rx) = tokio::sync::oneshot::channel();
                    tokio::task::spawn_blocking(move || {
                        let _ = writer_ready_tx.send(());
                        cancel_rx.recv().unwrap();
                        writer_observation.store(
                            eukhe_daemon::lease::live_lease_owner(&agent_dir, &session_path)
                                .is_some(),
                            std::sync::atomic::Ordering::SeqCst,
                        );
                        std::fs::write(&session_path, "writer settled\n").unwrap();
                    });
                    writer_ready_rx.await.unwrap();
                    match fixture.outcome {
                        Outcome::Success => Ok(0),
                        Outcome::Error => Err(HeadlessModeError::Runtime(std::io::Error::other(
                            "failed after lease acquisition",
                        ))),
                        Outcome::Panic => panic!("unwind after lease acquisition"),
                    }
                })
            })
        }));
        match outcome {
            Outcome::Success => {
                assert_eq!(result.unwrap().map_err(|error| error.to_string()), Ok(0));
            }
            Outcome::Error => assert_eq!(
                result.unwrap().map_err(|error| error.to_string()),
                Err("failed after lease acquisition".to_string())
            ),
            Outcome::Panic => assert!(result.is_err()),
        }
        assert!(held_at_write.load(std::sync::atomic::Ordering::SeqCst));
        assert_eq!(
            std::fs::read_to_string(&fixture.session_path).unwrap(),
            "writer settled\n"
        );
        assert!(
            eukhe_daemon::lease::live_lease_owner(&fixture.agent_dir, &fixture.session_path)
                .is_none()
        );
    }
}

fn summary_message(summary: &str) -> eukhe_types::session::AgentMessage {
    eukhe_types::session::AgentMessage::BranchSummary(eukhe_types::session::BranchSummaryMessage {
        summary: summary.to_owned(),
        from_id: "e1".to_owned(),
        timestamp: 7,
    })
}

fn line(event: &SessionEvent) -> serde_json::Value {
    serde_json::from_str(&json_line(event).expect("serializes")).expect("one JSON line")
}

/// A json-mode `message_update` is its change alone (omp `printableEvent`):
/// the accumulated partial never rides it, whatever its size.
#[test]
fn json_message_update_carries_only_the_change() {
    let partial = summary_message(&"x".repeat(64 * 1024));
    for (update, wire) in [
        (StreamUpdate::Start, serde_json::json!({ "type": "start" })),
        (
            StreamUpdate::TextStart,
            serde_json::json!({ "type": "text_start" }),
        ),
        (
            StreamUpdate::TextDelta {
                delta: "ab".to_owned(),
            },
            serde_json::json!({ "type": "text_delta", "delta": "ab" }),
        ),
        (
            StreamUpdate::TextEnd,
            serde_json::json!({ "type": "text_end" }),
        ),
        (
            StreamUpdate::ThinkingStart,
            serde_json::json!({ "type": "thinking_start" }),
        ),
        (
            StreamUpdate::ThinkingDelta {
                delta: "hm".to_owned(),
            },
            serde_json::json!({ "type": "thinking_delta", "delta": "hm" }),
        ),
        (
            StreamUpdate::ThinkingEnd,
            serde_json::json!({ "type": "thinking_end" }),
        ),
        (
            StreamUpdate::ToolcallStart,
            serde_json::json!({ "type": "toolcall_start" }),
        ),
        (
            StreamUpdate::ToolcallDelta {
                delta: "{\"a\"".to_owned(),
            },
            serde_json::json!({ "type": "toolcall_delta", "delta": "{\"a\"" }),
        ),
        (
            StreamUpdate::ToolcallEnd,
            serde_json::json!({ "type": "toolcall_end" }),
        ),
    ] {
        let event = SessionEvent::MessageUpdate {
            message: partial.clone(),
            assistant_message_event: update,
        };
        assert_eq!(
            json_line(&event).expect("serializes"),
            serde_json::json!({ "type": "message_update", "assistantMessageEvent": wire })
                .to_string()
        );
    }
}

/// A whole-message replacement's change is the message itself, so it keeps
/// it; every other frame (the settled `message_end` included) is the
/// session event's own form.
#[test]
fn json_message_replacement_and_end_carry_the_message() {
    let message = summary_message("replaced");
    let replaced = SessionEvent::MessageUpdate {
        message: message.clone(),
        assistant_message_event: StreamUpdate::Message,
    };
    assert_eq!(line(&replaced), serde_json::to_value(&replaced).unwrap());
    assert_eq!(line(&replaced)["message"]["summary"], "replaced");
    let end = SessionEvent::MessageEnd { message };
    assert_eq!(line(&end), serde_json::to_value(&end).unwrap());
    assert_eq!(line(&end)["message"]["summary"], "replaced");
}
