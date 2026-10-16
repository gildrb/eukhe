//! End-to-end verifier for the `/model` picker's catalog surface: the
//! daemon's `get_model_catalog` command must serve the local registry
//! snapshot (the built-in catalog plus models.json, with the providers
//! that have configured auth).
use std::io::{BufRead, BufReader, Write};
use std::path::Path;
use std::time::{Duration, Instant};

use serde_json::{json, Value};

#[path = "support/daemon.rs"]
mod daemon;
#[path = "support/process.rs"]
mod process;
use daemon::supervisor_command;
use process::Daemon;

fn spawn_supervisor(socket: &Path, agent_dir: &Path) -> Daemon {
    std::fs::create_dir_all(agent_dir).expect("agent dir");
    Daemon::spawn_bound(
        supervisor_command(socket, agent_dir)
            .env_remove("PRIME_API_KEY")
            .env_remove("EUKHE_CODING_AGENT_DIR"),
        socket,
        Duration::from_secs(10),
    )
}

struct Client {
    reader: BufReader<std::os::unix::net::UnixStream>,
    writer: std::os::unix::net::UnixStream,
}

impl Client {
    fn connect(socket: &Path) -> Client {
        let stream = std::os::unix::net::UnixStream::connect(socket).expect("connect");
        let writer = stream.try_clone().expect("clone");
        let mut client = Client {
            reader: BufReader::new(stream),
            writer,
        };
        let hello = client.read_line();
        assert_eq!(hello["type"], "daemon_hello");
        client
    }

    fn read_line(&mut self) -> Value {
        let mut line = String::new();
        let deadline = Instant::now() + Duration::from_mins(1);
        self.reader
            .get_mut()
            .set_read_timeout(Some(Duration::from_millis(100)))
            .expect("timeout");
        loop {
            match self.reader.read_line(&mut line) {
                Ok(0) => panic!("supervisor closed the connection"),
                Ok(_) if line.trim().is_empty() => line.clear(),
                Ok(_) => return serde_json::from_str(line.trim()).expect("parse line"),
                Err(error) => {
                    assert!(
                        Instant::now() < deadline,
                        "timed out waiting for supervisor line: {error}"
                    );
                }
            }
        }
    }

    fn request(&mut self, id: &str, command: &Value) -> Value {
        let envelope = json!({
            "type": "command",
            "id": id,
            "protocol": { "name": "eukhe.daemon", "version": 7 },
            "command": command,
        });
        let mut line = serde_json::to_string(&envelope).expect("serialize");
        line.push('\n');
        self.writer
            .write_all(line.as_bytes())
            .unwrap_or_else(|error| panic!("write command {id}: {error}"));
        let deadline = Instant::now() + Duration::from_mins(2);
        loop {
            assert!(Instant::now() < deadline, "no response for id {id}");
            let line = self.read_line();
            if line.get("id").and_then(Value::as_str) == Some(id) {
                return line;
            }
        }
    }
}

fn write_models_json(agent_dir: &Path, base_url: &str) {
    std::fs::create_dir_all(agent_dir).expect("agent dir");
    let models = json!({
        "providers": {
            "prime-inference": {
                "api": "openai-completions",
                "baseUrl": base_url,
                "apiKey": "sk-catalog-e2e",
                "models": [
                    {
                        "id": "mock-1",
                        "name": "Mock 1",
                        "api": "openai-completions",
                        "baseUrl": base_url,
                        "contextWindow": 128_000,
                        "maxTokens": 4096,
                    }
                ]
            }
        }
    });
    std::fs::write(
        agent_dir.join("models.json"),
        serde_json::to_string_pretty(&models).expect("serialize models.json"),
    )
    .expect("write models.json");
}

#[test]
fn daemon_serves_the_local_catalog() {
    let temp = tempfile::Builder::new()
        .prefix("pa-model-catalog-")
        .tempdir()
        .expect("temp dir");
    let dir = temp.path();
    let agent_dir = dir.join("agent");
    let socket = dir.join("daemon.sock");
    // No auth beyond the models.json key: no provider credentials.
    write_models_json(&agent_dir, "http://127.0.0.1:9/v1");
    let supervisor = spawn_supervisor(&socket, &agent_dir);
    let mut client = Client::connect(&socket);
    let session_dir = agent_dir.join("sessions");
    let created = client.request(
        "create-1",
        &json!({
            "type": "create",
            "config": {
                "cwd": dir.to_string_lossy(),
                "sessionDir": session_dir.to_string_lossy(),
                "noSession": true,
                "name": "catalog",
            },
        }),
    );
    assert!(created["success"].as_bool().unwrap_or(false), "{created}");
    let session_id = created["data"]["id"]
        .as_str()
        .or_else(|| created["data"]["sessionId"].as_str())
        .expect("session id")
        .to_string();

    // get_model_catalog: the full catalog with the configured providers.
    let response = client.request(
        "catalog-1",
        &json!({ "type": "get_model_catalog", "activeSessionId": session_id }),
    );
    assert!(response["success"].as_bool().unwrap_or(false), "{response}");
    let data = &response["data"];
    let models = data["models"].as_array().expect("models array");
    assert!(
        models.len() > 100,
        "the built-in catalog must serve (got {} models)",
        models.len()
    );
    // The models.json custom model is part of the catalog.
    assert!(models
        .iter()
        .any(|model| model["id"] == "mock-1" && model["provider"] == "prime-inference"));
    // A bundled public prime-inference model is present with its catalog
    // fields (name, cost, context window).
    let fable = models
        .iter()
        .find(|model| {
            model["id"] == "anthropic/claude-fable-5" && model["provider"] == "prime-inference"
        })
        .expect("a bundled featured model");
    assert_eq!(fable["name"], "Claude Fable 5");
    assert_eq!(fable["cost"]["input"], 10);
    assert_eq!(fable["contextWindow"], 1_000_000);
    // The configured providers: prime-inference (the models.json key) and
    // nothing else — no ambient credentials authorize other providers.
    let providers: Vec<&str> = data["configuredProviders"]
        .as_array()
        .expect("configuredProviders array")
        .iter()
        .filter_map(Value::as_str)
        .collect();
    assert_eq!(providers, vec!["prime-inference"]);
    // Private Prime Inference models stay out unless models.json declares
    // them.
    assert!(models.iter().all(|model| !model["id"]
        .as_str()
        .unwrap_or_default()
        .starts_with("internal/")));
    drop(client);
    drop(supervisor);
}
