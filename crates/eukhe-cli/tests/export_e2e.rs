// The Tier-C/D ruling (fleet-uniform, 2026-09-28): stack-resident futures
// by design on hot paths (boxing 130 fns is allocation-churn with zero
// correctness gain); the fn-length threshold is a style gate, not
// correctness (the harness fns are intentionally linear); 64-bit targets -
// the narrowing sits at OS/protocol boundaries where the values are
// bounded (pid syscalls, epoch/elapsed milliseconds, calendar math,
// guarded parses), and checked conversions would add panic paths where
// silent wrap was deliberate (the one genuinely-suspect family, args.rs's
// parse_positive_u32 lacking its u32::MAX bound, is flagged in the lane
// dossier for the conductor).
#![allow(
    clippy::large_futures,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::cast_precision_loss
)]

//! End-to-end verifier for the TUI export command: a scripted daemon session
//! driven headlessly — `/export` (HTML and JSONL) writes the file and
//! reports the TS success row.

use std::path::Path;
use std::time::Duration;

use eukhe_types::daemon::DaemonCommand;

#[path = "support/eukhe.rs"]
mod eukhe;
#[path = "../../eukhe-daemon/tests/support/process.rs"]
mod process;
use eukhe::{daemon_mode_args, eukhe_command, scrub_provider_keys};
use process::Daemon;

struct Supervisor(Daemon);

/// Stop by protocol; the inner `Daemon` guard then stops the supervisor and
/// its workers.
impl Drop for Supervisor {
    fn drop(&mut self) {
        graceful_shutdown(&self.0.socket);
        let _ = std::fs::remove_file(&self.0.socket);
    }
}

fn graceful_shutdown(socket: &Path) {
    use std::io::{BufRead, BufReader, Write};
    use std::os::unix::net::UnixStream;
    let Ok(stream) = UnixStream::connect(socket) else {
        return;
    };
    let Ok(write_half) = stream.try_clone() else {
        return;
    };
    let mut reader = BufReader::new(stream);
    let mut writer = write_half;
    let mut hello = String::new();
    let _ = reader.read_line(&mut hello); // daemon_hello
    let command = serde_json::json!({
        "type": "command",
        "id": "test-shutdown",
        "protocol": { "name": "eukhe.daemon", "version": 7 },
        "command": { "type": "shutdown" },
    });
    let mut line = serde_json::to_string(&command).expect("serialize");
    line.push('\n');
    if writer.write_all(line.as_bytes()).is_err() {
        return;
    }
    let _ = writer.flush();
    let _ = reader
        .get_ref()
        .set_read_timeout(Some(Duration::from_secs(5)));
    let mut response = String::new();
    let _ = reader.read_line(&mut response);
}

fn spawn_supervisor(dir: &Path) -> Supervisor {
    let socket = dir.join("daemon.sock");
    let agent_dir = dir.join("agent");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    let mut command = eukhe_command();
    daemon_mode_args(&mut command, &socket, &agent_dir);
    scrub_provider_keys(&mut command).env_remove("PRIME_TEAM_ID");
    Supervisor(Daemon::spawn_bound(
        &mut command,
        &socket,
        Duration::from_secs(15),
    ))
}

#[tokio::test]
async fn tui_export_surface() {
    use base64::Engine as _;
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let supervisor = spawn_supervisor(dir.path());

    // A live scripted session: one prompt, one scripted answer.
    // The faux engine (`engine: "faux"`) drives the real agent engine, so
    // the export embeds the real session's tools section.
    let script = serde_json::json!({ "engine": "faux", "responses": [
        { "text": "hello from scripted" },
    ] });
    let script_path = dir.path().join("script.json");
    std::fs::write(&script_path, script.to_string()).expect("write script");
    let (client, _events) = eukhe_tui::daemon_client::DaemonClient::connect(&supervisor.0.socket)
        .await
        .expect("connect supervisor");
    let data = client
        .request_ok(DaemonCommand::Create {
            id: None,
            session_path: None,
            continue_recent: None,
            no_session: None,
            name: None,
            config: Some(serde_json::json!({
                "cwd": dir.path().display().to_string(),
                "sessionDir": session_dir.display().to_string(),
                "script": script_path.display().to_string(),
            })),
            runtime_metadata: None,
            lifecycle: None,
            env: None,
            launch_env: None,
            rest: serde_json::Map::default(),
        })
        .await
        .expect("create session");
    client.close();
    let session_id = data
        .get("activeSessionId")
        .or_else(|| data.get("id"))
        .and_then(serde_json::Value::as_str)
        .expect("session id")
        .to_string();

    let options = eukhe_tui::interactive::InteractiveOptions {
        models: None,
        socket_path: supervisor.0.socket.clone(),
        cwd: dir.path().to_path_buf(),
        session_dir: Some(session_dir.clone()),
        script_path: Some(script_path.clone()),
        model_selection: eukhe_tui::interactive::ModelSelection::default(),
        model_catalog: Vec::new(),
        model_configured_providers: std::collections::HashSet::default(),
        model_recent_models: Vec::new(),
        default_thinking_level: None,
        no_session: false,
        session: eukhe_tui::interactive::SessionSelection::Attach(session_id.clone()),
        show_images: false,
        screen_mode: eukhe_tui::screen_mode::ScreenMode::Inline,
        initial_message: None,
        theme: "eukhe".to_string(),
        code_block_indent: "  ".to_string(),
        tree_filter_mode: String::new(),
        branch_summary_skip_prompt: false,
        version: "0.0.0".to_string(),
        onboarding: None,
        client_auth: None,
        provider_auth: None,
        keybindings: eukhe_tui::keybindings::KeybindingsManager::new(),
        session_rlm_depth: None,
        prompt_stash: std::sync::Arc::default(),
        session_has_children: false,
        restore_dock_focus: false,
        client_settings: None,
    };
    let html_out = dir.path().join("export.html");
    let jsonl_out = dir.path().join("branch.jsonl");
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            eukhe_tui::interactive::HeadlessStep::Submit("say hi".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
            eukhe_tui::interactive::HeadlessStep::Submit(format!("/export {}", html_out.display())),
            eukhe_tui::interactive::HeadlessStep::Submit(format!(
                "/export {}",
                jsonl_out.display()
            )),
        ],
        width: 100,
        height: 30,
    };
    let outcome = eukhe_tui::interactive::run_interactive(
        options,
        eukhe_tui::interactive::UiMode::Headless(plan),
    )
    .await
    .expect("interactive run");

    let rendered = outcome.frames.join("\n");

    // The exported HTML: the TS success row, the standalone viewer file,
    // and the session data carrying the fixture turn.
    assert!(
        rendered.contains(&format!("Session exported to: {}", html_out.display())),
        "export success row missing:\n{rendered}"
    );
    let html = std::fs::read_to_string(&html_out).expect("exported html");
    assert!(html.contains("Session Export"), "template scaffold");
    assert!(html.contains("--accent: #7c6faf;"), "theme vars embedded");
    let marker = "session-data\" type=\"application/json\">";
    let start = html.find(marker).expect("session data element");
    let blob = &html[start + marker.len()..];
    let blob = blob.split('<').next().expect("script close");
    let decoded = base64::engine::general_purpose::STANDARD
        .decode(blob.trim())
        .expect("base64 session data");
    let data: serde_json::Value = serde_json::from_slice(&decoded).expect("session data");
    assert_eq!(data["header"]["type"], "session");
    let entries = data["entries"].as_array().expect("entries");
    // The faux engine normalizes the user message into content blocks
    // (the plain string form stays valid for scripted-harness sessions).
    let user_turn_present = |entry: &serde_json::Value| {
        entry["message"]["role"] == "user"
            && (entry["message"]["content"] == "say hi"
                || entry["message"]["content"]
                    .as_array()
                    .is_some_and(|blocks| blocks.iter().any(|block| block["text"] == "say hi")))
    };
    assert!(
        entries.iter().any(user_turn_present),
        "user message in export: {data}"
    );
    // The tools section: the session's registered tool contracts (TS
    // `state.tools` in the live-session export).
    let tools = data["tools"].as_array().expect("tools section");
    assert!(
        tools.iter().any(|tool| tool["name"] == "ipython"
            && tool["description"].is_string()
            && tool["parameters"].is_object()),
        "ipython contract in export tools: {data}"
    );
    // No custom tool ran: the pre-render section is omitted, not null.
    assert!(
        data.get("renderedTools").is_none(),
        "renderedTools omitted without custom-tool renders: {data}"
    );

    // The JSONL branch export: the success row plus a linear session file
    // starting with the header line.
    assert!(
        rendered.contains(&format!("Session exported to: {}", jsonl_out.display())),
        "jsonl export row missing:\n{rendered}"
    );
    let jsonl = std::fs::read_to_string(&jsonl_out).expect("exported jsonl");
    let first: serde_json::Value =
        serde_json::from_str(jsonl.lines().next().expect("header line")).expect("header");
    assert_eq!(first["type"], "session");
    assert!(
        jsonl.contains("say hi"),
        "branch export carries the turn:\n{jsonl}"
    );
}
