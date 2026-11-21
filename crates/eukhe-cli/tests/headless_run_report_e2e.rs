//! Headless end-of-run report (spec I6): the real binary, an isolated
//! HOME, and the scripted faux provider (`EUKHE_FAUX_SCRIPT`). A `bash`
//! step that talks to a host runs unasked; when the run ends its report
//! goes to stderr in both output modes, and `--mode json` also prints it
//! as one `run_report` event after the run's `agent_end`.

use std::io::{Read, Write};
use std::net::TcpListener;
use std::path::Path;

use serde_json::{json, Value};

#[path = "support/eukhe.rs"]
mod eukhe;
use eukhe::eukhe_command;

/// A host on a loopback port that answers every request `200 OK`.
fn host() -> u16 {
    let listener = TcpListener::bind("127.0.0.1:0").expect("the host");
    let port = listener.local_addr().expect("the host's port").port();
    std::thread::spawn(move || {
        for stream in listener.incoming() {
            let Ok(mut stream) = stream else { continue };
            let mut request = [0_u8; 4096];
            let _ = stream.read(&mut request);
            let _ = stream.write_all(b"HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nok");
        }
    });
    port
}

/// One `bash` call of `command`, then the answer.
fn script(command: &str) -> Value {
    json!({ "responses": [
        { "content": [{ "type": "toolCall", "name": "bash", "id": "call-1",
            "arguments": { "script": command } }],
          "stopReason": "toolUse" },
        { "content": [{ "type": "text", "text": "pinged" }], "stopReason": "stop" },
    ] })
}

fn print_command(home: &Path, args: &[&str], script: &Value) -> std::process::Command {
    let mut command = eukhe_command();
    command
        .args(args)
        .env("HOME", home)
        .env("EUKHE_CODING_AGENT_DIR", home.join("agent"))
        .env("EUKHE_DAEMON_SOCKET", home.join("daemon.sock"))
        .env("EUKHE_FAUX_SCRIPT", script.to_string())
        .env("EUKHE_OFFLINE", "1")
        .env_remove("EUKHE_SESSION_DIR")
        .env_remove("EUKHE_CODING_AGENT_SESSION_DIR")
        .env_remove("RLM_DEPTH")
        .current_dir(home);
    command
}

fn home() -> tempfile::TempDir {
    let home = tempfile::TempDir::new().unwrap();
    std::fs::create_dir_all(home.path().join("agent")).unwrap();
    home
}

#[test]
fn the_run_report_goes_to_stderr_and_the_json_stream() {
    let port = host();
    let command = format!("curl -s http://127.0.0.1:{port}/headless");
    let report = format!("Irreversible effects ran this run:\n- e1 {command} (net)");

    let text_home = home();
    let text = print_command(
        text_home.path(),
        &["-p", "Ping the host."],
        &script(&command),
    )
    .output()
    .expect("binary present");
    let text_stderr = String::from_utf8_lossy(&text.stderr);

    let json_home = home();
    let json_run = print_command(
        json_home.path(),
        &["--mode", "json", "-p", "Ping the host."],
        &script(&command),
    )
    .output()
    .expect("binary present");
    let json_stderr = String::from_utf8_lossy(&json_run.stderr);
    let events: Vec<Value> = String::from_utf8_lossy(&json_run.stdout)
        .lines()
        .map(serde_json::from_str)
        .collect::<Result<_, _>>()
        .unwrap();
    let agent_end = events
        .iter()
        .rposition(|event| event["type"] == "agent_end")
        .expect("the run's agent_end");
    // Each report with whether it follows the run's `agent_end`.
    let mut reports: Vec<(bool, Value)> = events
        .iter()
        .enumerate()
        .filter(|(_, event)| event["type"] == "run_report")
        .map(|(at, event)| (at > agent_end, event.clone()))
        .collect();
    let session = reports
        .first()
        .and_then(|(_, report)| report["ran"][0]["sessionId"].as_str())
        .unwrap_or_default()
        .to_owned();
    for (_, report) in &mut reports {
        report["ran"][0]["atMs"] = Value::Null;
    }
    assert_eq!(
        (
            text.status.code(),
            text_stderr.contains(&report),
            json_run.status.code(),
            json_stderr.contains(&report),
            reports,
        ),
        (
            Some(0),
            true,
            Some(0),
            true,
            vec![(
                true,
                json!({
                    "type": "run_report",
                    "ran": [{
                        "id": "e1",
                        "key": format!("{session}:call-1:0"),
                        "run": 1,
                        "kind": "shellStep",
                        "command": command,
                        "classes": ["net"],
                        "sessionId": session,
                        "atMs": null,
                    }],
                    "unknown": [],
                })
            )],
        ),
        "text stderr: {text_stderr}\njson stderr: {json_stderr}"
    );
}
