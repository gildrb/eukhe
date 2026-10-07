use std::path::Path;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::durable::{open_session, ModelRequest, SessionConfig, SessionStorage};
use eukhe_pi_ai::providers::faux_script::{create_faux_script_models, parse_faux_script};

use super::*;
use crate::headless_terminal::HeadlessPrimary;
use crate::mode::{RuntimeConfig, SessionOptions};

/// A memory session on the scripted faux provider (the print harness's
/// `EUKHE_FAUX_SCRIPT` models without the environment).
async fn faux_session(dir: &Path, script: &serde_json::Value) -> EukheSession {
    let script = parse_faux_script(&script.to_string()).expect("faux script");
    let model = script.model.id.clone();
    let (models, _provider) = create_faux_script_models(script);
    let mut config = SessionConfig::new(
        dir.join("agent"),
        dir,
        "0198f000-0000-7000-8000-000000000000",
        SessionStorage::Memory,
    );
    config.models = Some(models);
    config.model = Some(ModelRequest {
        provider: Some("faux".to_owned()),
        pattern: model,
    });
    open_session(config, &BACKGROUND_CONTEXT)
        .await
        .expect("open the faux session")
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

/// Run the prompt loop on a faux session and select the terminal result.
async fn run(
    script: &serde_json::Value,
    prompts: &[&str],
) -> (
    Option<String>,
    crate::headless_terminal::HeadlessTerminalResult,
) {
    let dir = tempfile::TempDir::new().expect("tempdir");
    let session = faux_session(dir.path(), script).await;
    let conversation = session.main();
    let cx = &*BACKGROUND_CONTEXT;
    let failure = drive_prompts(
        &session,
        &conversation,
        &run_options(dir.path(), prompts),
        cx,
    )
    .await
    .expect("the prompt loop runs");
    let result = select_terminal_result(&conversation, cx)
        .await
        .expect("terminal selection");
    session.close(cx).await.expect("close");
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

#[tokio::test]
async fn an_unscripted_request_fails_the_run_with_its_error() {
    let (failure, result) = run(&serde_json::json!({ "responses": [] }), &["hi"]).await;
    assert_eq!(failure, None);
    let primary = result.primary.expect("the failed assistant turn");
    assert!(
        matches!(primary, HeadlessPrimary::Assistant(_)),
        "{primary:?}"
    );
    let stderr = primary.failure().expect("exit 1").expect("stderr text");
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
        UserContent::Text("plain".to_owned())
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
