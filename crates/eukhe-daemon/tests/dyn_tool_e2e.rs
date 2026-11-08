//! The tool surface end to end: a daemon session over
//! the real kernel (scripted faux provider) with a settings-declared stdio
//! MCP server. Over two turns the session's requests all carry the roster it
//! opened with, while the server's `echo` tool, never in the roster, is
//! listed and called through `dyn`, and `report_issue` stores a row.

use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use serde_json::{json, Value};

#[path = "support/daemon.rs"]
mod daemon;
#[path = "support/process.rs"]
mod process;
use daemon::supervisor_command;
use process::Daemon;

/// JSONL supervisor client (command envelopes, id-matched responses).
struct Client {
    reader: BufReader<UnixStream>,
    writer: UnixStream,
}

impl Client {
    fn connect(socket: &Path) -> (Self, Value) {
        let stream = UnixStream::connect(socket).expect("connect supervisor");
        let writer = stream.try_clone().expect("clone socket");
        let mut client = Client {
            reader: BufReader::new(stream),
            writer,
        };
        let hello = client.read_line();
        (client, hello)
    }

    fn command(&mut self, id: &str, command: &Value) -> Value {
        let mut line = serde_json::to_string(&json!({
            "type": "command",
            "id": id,
            "protocol": { "name": "eukhe.daemon", "version": 7 },
            "command": command,
        }))
        .expect("serialize command");
        line.push('\n');
        self.writer.write_all(line.as_bytes()).expect("send");
        self.writer.flush().expect("flush");
        let deadline = Instant::now() + Duration::from_mins(4);
        loop {
            assert!(Instant::now() < deadline, "no response for id {id}");
            let line = self.read_line();
            if line.get("id").and_then(Value::as_str) == Some(id) {
                assert_eq!(line["success"], true, "{id} failed: {line}");
                return line;
            }
        }
    }

    fn read_line(&mut self) -> Value {
        let mut line = String::new();
        let deadline = Instant::now() + Duration::from_mins(2);
        self.reader
            .get_mut()
            .set_read_timeout(Some(Duration::from_millis(100)))
            .expect("set timeout");
        loop {
            match self.reader.read_line(&mut line) {
                Ok(0) => panic!("supervisor closed the connection"),
                Ok(_) if line.trim().is_empty() => line.clear(),
                Ok(_) => return serde_json::from_str(line.trim()).expect("parse response line"),
                Err(error) => {
                    assert!(
                        Instant::now() < deadline,
                        "timed out waiting for supervisor line: {error}"
                    );
                }
            }
        }
    }
}

fn dyn_call(arguments: &Value) -> Value {
    json!({ "content": [{ "type": "toolCall", "name": "dyn", "arguments": arguments }] })
}

/// Every line of every file under `dir`.
fn lines_under(dir: &Path) -> Vec<String> {
    let mut lines = Vec::new();
    for entry in std::fs::read_dir(dir).expect("read dir").flatten() {
        let path = entry.path();
        if path.is_dir() {
            lines.extend(lines_under(&path));
        } else if let Ok(text) = std::fs::read_to_string(&path) {
            lines.extend(text.lines().map(str::to_owned));
        }
    }
    lines
}

#[test]
// One scenario, read top to bottom.
#[allow(clippy::too_many_lines)]
fn the_roster_stays_fixed_while_an_mcp_tool_is_called_through_dyn() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let sessions_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&sessions_dir).expect("sessions dir");
    let fixture = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("mcp_echo_server.py");
    std::fs::write(
        agent_dir.join("settings.json"),
        json!({
            "mcpServers": {
                "fixture-echo": {
                    "type": "stdio",
                    "command": "python3",
                    "args": [fixture.to_string_lossy()],
                },
            },
        })
        .to_string(),
    )
    .expect("write settings.json");
    let script = dir.path().join("faux.json");
    std::fs::write(
        &script,
        json!({
            "engine": "faux",
            "responses": [
                dyn_call(&json!({})),
                { "text": "listed" },
                dyn_call(&json!({
                    "name": "mcp/fixture-echo/echo",
                    "arguments": { "message": "hello through dyn" },
                })),
                dyn_call(&json!({
                    "name": "report_issue",
                    "arguments": { "tool": "mcp/fixture-echo/echo", "description": "smoke report" },
                })),
                { "text": "done" },
            ],
        })
        .to_string(),
    )
    .expect("write faux script");

    let socket = dir.path().join("dyn.sock");
    let _daemon = Daemon::spawn_listening(
        supervisor_command(&socket, &agent_dir)
            .env("EUKHE_CODING_AGENT_DIR", &agent_dir)
            .env_remove("PRIME_API_KEY")
            .env(
                eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
                "15000",
            ),
        &socket,
        Duration::from_secs(15),
    );
    let (mut client, hello) = Client::connect(&socket);
    assert_eq!(hello["type"], "daemon_hello");
    let created = client.command(
        "c1",
        &json!({
            "type": "create",
            "config": {
                "cwd": dir.path().to_string_lossy(),
                "sessionDir": sessions_dir.to_string_lossy(),
                "script": script.to_string_lossy(),
            },
        }),
    );
    let session = created["data"]["activeSessionId"]
        .as_str()
        .or_else(|| created["data"]["id"].as_str())
        .expect("active session id")
        .to_owned();
    for (turn, prompt) in [("1", "list the tools"), ("2", "use the echo tool")] {
        client.command(
            &format!("p{turn}"),
            &json!({ "type": "prompt", "activeSessionId": session, "message": prompt }),
        );
        client.command(
            &format!("w{turn}"),
            &json!({ "type": "wait_for_idle", "activeSessionId": session }),
        );
    }
    let messages = client.command(
        "m1",
        &json!({ "type": "get_messages", "activeSessionId": session }),
    );
    let results: Vec<String> = messages["data"]["messages"]
        .as_array()
        .expect("messages")
        .iter()
        .filter(|message| message["role"] == "toolResult")
        .map(|message| match &message["content"] {
            Value::String(text) => text.clone(),
            Value::Array(blocks) => blocks
                .iter()
                .filter_map(|block| block["text"].as_str())
                .collect::<Vec<_>>()
                .join("\n"),
            other => other.to_string(),
        })
        .collect();
    println!("dyn results: {results:#?}");

    // The stored transcript: the tool loadout entries, and the issue row.
    let stored = lines_under(&sessions_dir);
    let loadouts: Vec<&String> = stored
        .iter()
        .filter(|line| line.contains("\"toolsAdded\"") || line.contains("\"toolsRemoved\""))
        .collect();
    let issues = stored
        .iter()
        .filter(|line| line.contains("eukhe.tool_issue"))
        .count();
    println!("loadout entries: {}", loadouts.len());
    println!("issue rows: {issues}");
    assert_eq!(
        (
            results.len(),
            results[0].contains("mcp/fixture-echo/echo: Echoes the message argument back."),
            results[1].contains("hello through dyn"),
            results[2].clone(),
            loadouts.len(),
            loadouts
                .iter()
                .any(|line| line.contains("\"toolsRemoved\"")),
            issues > 0,
        ),
        (
            3,
            true,
            true,
            "Recorded the issue with mcp/fixture-echo/echo; the user sees it in the session."
                .to_owned(),
            1,
            false,
            true,
        ),
        "results: {results:#?}"
    );
}
