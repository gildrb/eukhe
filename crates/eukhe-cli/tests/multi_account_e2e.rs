//! Several accounts of one provider, end to end: the real binary in
//! headless print mode, an isolated HOME, and a local mock provider that
//! answers the first account's key with a usage limit (429) and the second
//! account's key with an answer. The run goes on with the second account
//! of the same provider and model, its report names the switch, and the
//! first account's limit is stored on it.

use std::fmt::Write as _;
use std::io::{BufRead, BufReader, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::path::Path;
use std::sync::{Arc, Mutex};

use serde_json::{json, Value};

#[path = "support/eukhe.rs"]
mod eukhe;
use eukhe::eukhe_command;

const FIRST_KEY: &str = "sk-first-aaaaaa";
const SECOND_KEY: &str = "sk-second-bbbbbb";

/// A local OpenAI-style chat server: a request with [`FIRST_KEY`] gets a
/// usage limit for an hour, any other an answer. It records the key of
/// each completion request.
struct MockProvider {
    port: u16,
    keys: Arc<Mutex<Vec<String>>>,
}

impl MockProvider {
    fn start() -> Self {
        let listener = TcpListener::bind("127.0.0.1:0").expect("bind mock provider");
        let port = listener.local_addr().expect("mock addr").port();
        let keys = Arc::new(Mutex::new(Vec::new()));
        let seen = Arc::clone(&keys);
        std::thread::spawn(move || {
            for stream in listener.incoming() {
                let Ok(stream) = stream else { return };
                let _ = serve(stream, &seen);
            }
        });
        Self { port, keys }
    }

    fn keys(&self) -> Vec<String> {
        self.keys.lock().expect("mock lock").clone()
    }
}

fn chunk(delta: &Value, finish_reason: Option<&str>) -> String {
    json!({
        "id": "chatcmpl-test",
        "object": "chat.completion.chunk",
        "created": 1_750_000_000,
        "model": "mock-1",
        "choices": [{"index": 0, "delta": delta, "finish_reason": finish_reason}],
    })
    .to_string()
}

fn serve(mut stream: TcpStream, keys: &Arc<Mutex<Vec<String>>>) -> std::io::Result<()> {
    let mut reader = BufReader::new(stream.try_clone()?);
    let mut head = String::new();
    loop {
        let mut line = String::new();
        if reader.read_line(&mut line)? == 0 {
            return Ok(());
        }
        head.push_str(&line);
        if line == "\r\n" {
            break;
        }
    }
    // Only the completion calls (POST) are the run's.
    if !head.starts_with("POST ") {
        return stream.write_all(
            b"HTTP/1.1 404 Not Found\r\nContent-Length: 0\r\nConnection: close\r\n\r\n",
        );
    }
    let mut content_length = 0usize;
    let mut key = String::new();
    for line in head.lines() {
        let lower = line.to_ascii_lowercase();
        if let Some(value) = lower.strip_prefix("content-length:") {
            content_length = value.trim().parse().unwrap_or_default();
        }
        if lower.starts_with("authorization:") {
            key = line
                .split_once("Bearer ")
                .map(|(_, key)| key.trim().to_owned())
                .unwrap_or_default();
        }
    }
    let mut body = vec![0u8; content_length];
    reader.read_exact(&mut body)?;
    keys.lock().expect("mock lock").push(key.clone());
    if key == FIRST_KEY {
        let body = json!({
            "error": {
                "message": "You exceeded your current quota",
                "type": "rate_limit_exceeded",
                "code": "rate_limit_exceeded"
            }
        })
        .to_string();
        return stream.write_all(
            format!(
                "HTTP/1.1 429 Too Many Requests\r\nContent-Type: application/json\r\nRetry-After: 3600\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{body}",
                body.len()
            )
            .as_bytes(),
        );
    }
    let mut payload = String::new();
    for data in [
        chunk(
            &json!({"role": "assistant", "content": "answer from the second account"}),
            None,
        ),
        chunk(&json!({}), Some("stop")),
    ] {
        write!(payload, "data: {data}\n\n").expect("write to String");
    }
    payload.push_str("data: [DONE]\n\n");
    stream.write_all(
        format!(
            "HTTP/1.1 200 OK\r\nContent-Type: text/event-stream\r\nConnection: close\r\n\r\n{payload}"
        )
        .as_bytes(),
    )
}

/// An agent dir whose `models.json` serves `mock/mock-1` at `port` and
/// whose `auth.json` holds two accounts of `mock`: the first account's key,
/// then the second's. A custom provider needs its own `apiKey`; the stored
/// accounts come before it.
fn agent_dir(root: &Path, port: u16) -> std::path::PathBuf {
    let agent = root.join("agent");
    std::fs::create_dir_all(&agent).expect("agent dir");
    std::fs::write(
        agent.join("models.json"),
        json!({ "providers": { "mock": {
            "baseUrl": format!("http://127.0.0.1:{port}/v1"),
            "apiKey": "sk-models-json-unused",
            "api": "openai-completions",
            "models": [ { "id": "mock-1", "name": "Mock 1" } ]
        } } })
        .to_string(),
    )
    .expect("models.json");
    std::fs::write(
        agent.join("auth.json"),
        json!({ "mock": { "accounts": [
            { "type": "api_key", "key": FIRST_KEY, "identity": "key ...aaaaaa" },
            { "type": "api_key", "key": SECOND_KEY, "identity": "key ...bbbbbb" },
        ] } })
        .to_string(),
    )
    .expect("auth.json");
    agent
}

#[test]
fn a_usage_limit_moves_the_run_to_the_second_account_and_reports_it() {
    let provider = MockProvider::start();
    let root = tempfile::tempdir().expect("temp dir");
    let agent = agent_dir(root.path(), provider.port);
    let output = eukhe_command()
        .args(["-p", "--model", "mock/mock-1", "say something"])
        .env("HOME", root.path())
        .env("EUKHE_AGENT_DIR", &agent)
        .env("EUKHE_CODING_AGENT_DIR", &agent)
        .env_remove("RLM_DEPTH")
        .current_dir(root.path())
        .output()
        .expect("run eukhe");
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    let switch = stderr
        .lines()
        .find(|line| line.starts_with("eukhe: switched to account "))
        .map(|line| {
            line.split(" holds until ")
                .next()
                .unwrap_or_default()
                .to_owned()
        });
    let stored: Value =
        serde_json::from_str(&std::fs::read_to_string(agent.join("auth.json")).expect("auth.json"))
            .expect("auth.json parses");
    let limited = stored["mock"]["accounts"]
        .as_array()
        .expect("accounts")
        .iter()
        .map(|account| account["limitedUntil"].is_u64())
        .collect::<Vec<bool>>();
    assert_eq!(
        (
            output.status.code(),
            String::from_utf8_lossy(&output.stdout).into_owned(),
            switch,
            provider.keys(),
            limited,
        ),
        (
            Some(0),
            "answer from the second account\n".to_owned(),
            Some(
                "eukhe: switched to account key ...bbbbbb: the usage limit of key ...aaaaaa"
                    .to_owned()
            ),
            vec![FIRST_KEY.to_owned(), SECOND_KEY.to_owned()],
            vec![true, false],
        ),
        "stderr: {stderr}"
    );
}
