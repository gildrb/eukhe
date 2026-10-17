//! `eukhe provider caps|models` against a custom `llama-cpp` provider in an
//! isolated agent dir, its server a local mock: `caps` sends nothing,
//! `models` sends exactly one `GET /v1/models` to the configured base URL.

use std::io::{BufRead, BufReader, Write};
use std::net::TcpListener;
use std::path::Path;
use std::process::{Command, Output};
use std::sync::{Arc, Mutex};

const LISTING: &str =
    r#"{"object":"list","data":[{"id":"qwen3-8b","object":"model","owned_by":"llamacpp"}]}"#;

/// A local HTTP server answering every request with [`LISTING`]; it
/// records each request line.
struct MockServer {
    port: u16,
    requests: Arc<Mutex<Vec<String>>>,
}

impl MockServer {
    fn start() -> Self {
        let listener = TcpListener::bind("127.0.0.1:0").expect("bind mock server");
        let port = listener.local_addr().expect("mock addr").port();
        let requests = Arc::new(Mutex::new(Vec::new()));
        let seen = Arc::clone(&requests);
        std::thread::spawn(move || {
            for stream in listener.incoming() {
                let Ok(mut stream) = stream else { return };
                let mut reader = BufReader::new(stream.try_clone().expect("clone stream"));
                let mut request_line = String::new();
                if reader.read_line(&mut request_line).is_err() {
                    continue;
                }
                let mut header = String::new();
                while reader.read_line(&mut header).is_ok_and(|read| read > 2) {
                    header.clear();
                }
                seen.lock()
                    .expect("requests lock")
                    .push(request_line.trim_end().to_string());
                let response = format!(
                    "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{LISTING}",
                    LISTING.len()
                );
                let _ = stream.write_all(response.as_bytes());
            }
        });
        Self { port, requests }
    }

    fn requests(&self) -> Vec<String> {
        self.requests.lock().expect("requests lock").clone()
    }
}

/// An agent dir whose `models.json` configures `llama-cpp` at `port`.
fn agent_dir(root: &Path, port: u16) -> std::path::PathBuf {
    let agent = root.join("agent");
    std::fs::create_dir_all(&agent).expect("agent dir");
    std::fs::write(
        agent.join("models.json"),
        format!(
            r#"{{ "providers": {{
                "llama-cpp": {{
                    "baseUrl": "http://127.0.0.1:{port}/v1", "apiKey": "none",
                    "api": "openai-completions",
                    "models": [ {{ "id": "qwen3-8b", "name": "Qwen3 8B" }} ]
                }}
            }} }}"#
        ),
    )
    .expect("models.json");
    agent
}

/// Run `eukhe <args>` with only the isolated home and agent dir in its
/// environment (no ambient provider keys).
fn eukhe(root: &Path, agent: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_eukhe"))
        .args(args)
        .env_clear()
        .env("HOME", root)
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env("EUKHE_CODING_AGENT_DIR", agent)
        .output()
        .expect("run eukhe")
}

#[test]
fn provider_caps_prints_the_rulebook_and_sends_nothing() {
    let server = MockServer::start();
    let root = tempfile::tempdir().expect("temp dir");
    let agent = agent_dir(root.path(), server.port);
    let output = eukhe(root.path(), &agent, &["provider", "caps", "llama-cpp"]);
    assert_eq!(
        (
            output.status.code(),
            String::from_utf8_lossy(&output.stdout).into_owned(),
            String::from_utf8_lossy(&output.stderr).into_owned(),
        ),
        (
            Some(0),
            format!(
                "llama-cpp  openai-completions  http://127.0.0.1:{}/v1\n\
                 \x20 count_tokens    llama-cpp: POST /apply-template, POST /tokenize\n\
                 \x20 list_models     openai: GET /v1/models\n\
                 \x20 embed           openai: POST /v1/embeddings\n\
                 \x20 generate_image  unsupported\n\
                 \x20 tokenize        llama-cpp: POST /tokenize\n\
                 \x20 usage           unsupported\n\
                 \x20 web_search      unsupported\n\
                 \x20 compact         unsupported\n",
                server.port
            ),
            String::new(),
        )
    );
    assert_eq!(server.requests(), Vec::<String>::new());
}

#[test]
fn provider_caps_rejects_an_unknown_provider() {
    let server = MockServer::start();
    let root = tempfile::tempdir().expect("temp dir");
    let agent = agent_dir(root.path(), server.port);
    let output = eukhe(
        root.path(),
        &agent,
        &["provider", "caps", "no-such-provider"],
    );
    assert_eq!(
        (
            output.status.code(),
            String::from_utf8_lossy(&output.stdout).into_owned(),
            String::from_utf8_lossy(&output.stderr).into_owned(),
        ),
        (
            Some(1),
            String::new(),
            "Error: Unknown provider: no-such-provider\n".to_string(),
        )
    );
}

#[test]
fn provider_models_lists_the_mock_servers_models() {
    let server = MockServer::start();
    let root = tempfile::tempdir().expect("temp dir");
    let agent = agent_dir(root.path(), server.port);
    let output = eukhe(root.path(), &agent, &["provider", "models", "llama-cpp"]);
    assert_eq!(
        (
            output.status.code(),
            String::from_utf8_lossy(&output.stdout).into_owned(),
            String::from_utf8_lossy(&output.stderr).into_owned(),
        ),
        (
            Some(0),
            "id        name  context  max-out\nqwen3-8b  -     -        -\n".to_string(),
            String::new(),
        )
    );
    assert_eq!(
        server.requests(),
        vec!["GET /v1/models HTTP/1.1".to_string()]
    );
}
