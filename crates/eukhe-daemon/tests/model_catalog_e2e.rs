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

/// Each test supervises a daemon and a session worker; serializing them
/// keeps the harness out of parallel-spawn resource races.
static DAEMON_E2E: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// Spawn the supervisor with `package_dir` as the install's package
/// directory: the bundled catalog it holds (if any) is the bundle the
/// built-in catalog reads, never one beside the test binary.
fn spawn_supervisor(socket: &Path, agent_dir: &Path, package_dir: &Path) -> Daemon {
    std::fs::create_dir_all(agent_dir).expect("agent dir");
    std::fs::create_dir_all(package_dir).expect("package dir");
    Daemon::spawn_bound(
        supervisor_command(socket, agent_dir)
            .env_remove("PRIME_API_KEY")
            .env_remove("ANTHROPIC_API_KEY")
            .env_remove("EUKHE_CODING_AGENT_DIR")
            .env("EUKHE_PACKAGE_DIR", package_dir),
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

/// Create a session and answer its `get_model_catalog` data: the full
/// catalog with the configured providers.
fn served_catalog(client: &mut Client, dir: &Path, agent_dir: &Path) -> Value {
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
    let response = client.request(
        "catalog-1",
        &json!({ "type": "get_model_catalog", "activeSessionId": session_id }),
    );
    assert!(response["success"].as_bool().unwrap_or(false), "{response}");
    response["data"].clone()
}

/// The catalog fields of a model object, for whole-object comparison.
fn catalog_fields(model: &Value) -> Value {
    let fields = [
        "provider",
        "id",
        "name",
        "api",
        "baseUrl",
        "reasoning",
        "input",
        "cost",
        "contextWindow",
        "maxTokens",
    ];
    fields
        .iter()
        .map(|field| ((*field).to_string(), model[*field].clone()))
        .collect::<serde_json::Map<String, Value>>()
        .into()
}

/// The pinned catalog snapshot (the eukhe-models parity fixture) has no
/// Claude Haiku 5.5; the compiled catalog has it. With that snapshot as
/// the install's bundled catalog, the `/model` list of an Anthropic login
/// still has the model, as the compiled catalog defines it.
#[test]
fn a_bundle_without_a_compiled_model_still_lists_it() {
    let _serial = DAEMON_E2E
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let temp = tempfile::Builder::new()
        .prefix("pa-model-catalog-")
        .tempdir()
        .expect("temp dir");
    let dir = temp.path();
    let agent_dir = dir.join("agent");
    let package_dir = dir.join("package");
    let socket = dir.join("daemon.sock");
    std::fs::create_dir_all(&package_dir).expect("package dir");
    std::fs::write(
        package_dir.join("models.bundled.json"),
        include_str!("../../eukhe-models/tests/fixtures/catalog.v1.json"),
    )
    .expect("write the bundled catalog");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    std::fs::write(
        agent_dir.join("auth.json"),
        json!({ "anthropic": { "type": "api_key", "key": "sk-ant-catalog-e2e" } }).to_string(),
    )
    .expect("write auth.json");
    let supervisor = spawn_supervisor(&socket, &agent_dir, &package_dir);
    let mut client = Client::connect(&socket);
    let data = served_catalog(&mut client, dir, &agent_dir);
    let haiku = data["models"]
        .as_array()
        .expect("models array")
        .iter()
        .find(|model| model["provider"] == "anthropic" && model["id"] == "claude-haiku-5-5")
        .map(catalog_fields);
    let mut compiled = serde_json::to_value(
        eukhe_ai::providers::anthropic_models::ANTHROPIC_MODELS
            .get("claude-haiku-5-5")
            .expect("the compiled Claude Haiku 5.5"),
    )
    .expect("serialize the compiled model");
    // The registry model has no pricing tiers.
    compiled["cost"]
        .as_object_mut()
        .expect("the compiled cost")
        .remove("tiers");
    assert_eq!(haiku, Some(catalog_fields(&compiled)));
    assert_eq!(data["configuredProviders"], json!(["anthropic"]));
    drop(client);
    drop(supervisor);
}

#[test]
fn daemon_serves_the_local_catalog() {
    let _serial = DAEMON_E2E
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let temp = tempfile::Builder::new()
        .prefix("pa-model-catalog-")
        .tempdir()
        .expect("temp dir");
    let dir = temp.path();
    let agent_dir = dir.join("agent");
    let socket = dir.join("daemon.sock");
    // No auth beyond the models.json key: no provider credentials.
    write_models_json(&agent_dir, "http://127.0.0.1:9/v1");
    // An install without a bundled catalog: the compiled catalog serves.
    let supervisor = spawn_supervisor(&socket, &agent_dir, &dir.join("package"));
    let mut client = Client::connect(&socket);
    let data = served_catalog(&mut client, dir, &agent_dir);
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
    // Every model object carries the levels and tiers it offers, read from
    // the eukhe-ai quirks rulebook (the `CatalogModel` shape).
    for model in models {
        let entry: eukhe_types::ai::CatalogModel =
            serde_json::from_value(model.clone()).expect("a catalog model");
        assert_eq!(
            (entry.thinking_levels, entry.service_tiers),
            (
                eukhe_ai::models::registry_thinking_levels(&entry.model),
                eukhe_ai::quirks::service_tiers((&entry.model).into()),
            ),
            "{}/{}",
            entry.model.provider,
            entry.model.id
        );
    }
    // The non-reasoning models.json model offers "off" only.
    let mock = models
        .iter()
        .find(|model| model["id"] == "mock-1" && model["provider"] == "prime-inference")
        .expect("the models.json model");
    assert_eq!(mock["thinkingLevels"], json!(["off"]));
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
