//! Detached-cell wake e2e (cause 1 of the stuck-session audit; ADR 0010):
//! a real daemon, a real kernel on this checkout's runtime, a mock
//! provider. The model runs a cell that sleeps past the runtime's blocking
//! budget. The cell must not hold the turn: its call settles `detached`,
//! the turn ends while the cell still runs, and the cell's end wakes the
//! idle session with the `[job-settled ...]` report carrying its output.

// Stack-resident futures by design; see readoption_wake_e2e.rs.
#![allow(clippy::large_futures)]
use std::fmt::Write as _;
use std::io::{BufRead, BufReader, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use serde_json::{json, Value};

#[path = "support/daemon.rs"]
mod daemon;
#[path = "support/process.rs"]
mod process;
use daemon::kernel_runtime::kernel_python;
use daemon::supervisor_args;
use process::Daemon;

/// The runtime's blocking budget in this test.
const BUDGET_MS: u64 = 2_000;
/// The cell sleeps the budget plus five seconds. Its done marker is built
/// at run time, so only its output (never its source) carries it.
const CELL: &str =
    "import time\nprint('cell started', flush=True)\ntime.sleep(7)\nprint('CELL' + '_DONE')";

fn spawn_daemon(socket: &Path, agent_dir: &Path, kernel_python: &Path) -> Daemon {
    Daemon::spawn_bound(
        supervisor_args(
            &mut Command::new(env!("CARGO_BIN_EXE_eukhe-daemon")),
            socket,
            agent_dir,
        )
        .env_remove("PRIME_API_KEY")
        .env("EUKHE_CODING_AGENT_DIR", agent_dir)
        .env("EUKHE_KERNEL_PYTHON", kernel_python)
        // A supervisor killed at teardown must not leak its session worker.
        .env(
            eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
            "20000",
        ),
        socket,
        Duration::from_secs(15),
    )
}

/// The sequential mock provider: the cell's tool call, the reply that
/// ends the turn, then the woken turn's reply for every later request.
fn spawn_mock(next: &'static AtomicUsize) -> String {
    let listener = TcpListener::bind("127.0.0.1:0").expect("bind mock");
    let url = format!(
        "http://127.0.0.1:{}/v1",
        listener.local_addr().expect("mock address").port()
    );
    std::thread::spawn(move || {
        for stream in listener.incoming() {
            let Ok(stream) = stream else { continue };
            std::thread::spawn(move || {
                let _ = serve(stream, next);
            });
        }
    });
    url
}

fn chunk(delta: &Value, finish_reason: Option<&str>) -> String {
    json!({
        "id": "chatcmpl-detach",
        "object": "chat.completion.chunk",
        "created": 1_750_000_000,
        "model": "mock-1",
        "choices": [{"index": 0, "delta": delta, "finish_reason": finish_reason}],
    })
    .to_string()
}

fn reply(text: &str) -> [String; 2] {
    [
        chunk(&json!({"role": "assistant", "content": text}), None),
        chunk(&json!({}), Some("stop")),
    ]
}

fn serve(mut stream: TcpStream, next: &AtomicUsize) -> std::io::Result<()> {
    let mut reader = BufReader::new(stream.try_clone()?);
    let mut content_length = 0usize;
    loop {
        let mut line = String::new();
        if reader.read_line(&mut line)? == 0 {
            return Ok(());
        }
        if line == "\r\n" {
            break;
        }
        if let Some(value) = line.to_ascii_lowercase().strip_prefix("content-length:") {
            content_length = value.trim().parse().unwrap_or_default();
        }
    }
    let mut body = vec![0u8; content_length];
    reader.read_exact(&mut body)?;
    let data = match next.fetch_add(1, Ordering::SeqCst) {
        0 => [
            chunk(
                &json!({
                    "role": "assistant",
                    "content": "",
                    "tool_calls": [{
                        "index": 0,
                        "id": "call-detach-1",
                        "type": "function",
                        "function": {
                            "name": "ipython",
                            "arguments": json!({ "code": CELL }).to_string(),
                        }
                    }]
                }),
                None,
            ),
            chunk(&json!({}), Some("tool_calls")),
        ],
        1 => reply("the cell runs on as a job"),
        _ => reply("woken by the settled job"),
    };
    let mut payload = String::new();
    for data in data {
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

struct Client {
    reader: BufReader<UnixStream>,
    writer: UnixStream,
}

impl Client {
    fn connect(socket: &Path) -> Client {
        let stream = UnixStream::connect(socket).expect("connect");
        let writer = stream.try_clone().expect("clone");
        let mut client = Client {
            reader: BufReader::new(stream),
            writer,
        };
        assert_eq!(client.read_line()["type"], "daemon_hello");
        client
    }

    fn read_line(&mut self) -> Value {
        let mut line = String::new();
        let deadline = Instant::now() + Duration::from_mins(2);
        self.reader
            .get_mut()
            .set_read_timeout(Some(Duration::from_millis(100)))
            .expect("timeout");
        loop {
            match self.reader.read_line(&mut line) {
                Ok(0) => panic!("supervisor closed the connection"),
                Ok(_) if line.trim().is_empty() => line.clear(),
                Ok(_) => return serde_json::from_str(line.trim()).expect("parse line"),
                Err(error) => assert!(
                    Instant::now() < deadline,
                    "timed out waiting for supervisor line: {error}"
                ),
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

    fn messages(&mut self, active_session_id: &str) -> String {
        let response = self.request(
            "gm",
            &json!({ "type": "get_messages", "activeSessionId": active_session_id }),
        );
        assert_eq!(response["success"], true, "get_messages failed: {response}");
        serde_json::to_string(&response["data"]).expect("messages json")
    }
}

fn wait_until<T>(deadline: Duration, mut probe: impl FnMut() -> Option<T>) -> T {
    let deadline = Instant::now() + deadline;
    loop {
        if let Some(value) = probe() {
            return value;
        }
        assert!(Instant::now() < deadline, "condition never became true");
        std::thread::sleep(Duration::from_millis(100));
    }
}

fn write_agent_config(agent_dir: &Path, url: &str) {
    std::fs::create_dir_all(agent_dir.join("sessions")).expect("sessions dir");
    std::fs::write(
        agent_dir.join("models.json"),
        json!({
            "providers": {
                "prime-inference": {
                    "api": "openai-completions",
                    "baseUrl": url,
                    "apiKey": "sk-detach",
                    "models": [{
                        "id": "mock-1",
                        "name": "Mock 1",
                        "api": "openai-completions",
                        "contextWindow": 128_000,
                        "maxTokens": 4096
                    }]
                }
            }
        })
        .to_string(),
    )
    .expect("write models.json");
    std::fs::write(
        agent_dir.join("settings.json"),
        json!({ "toolBlockingBudgetMs": BUDGET_MS }).to_string(),
    )
    .expect("write settings.json");
}

#[test]
fn a_cell_past_the_blocking_budget_ends_the_turn_and_its_end_wakes_the_session() {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let kernel_python = kernel_python();
    let root = tempfile::TempDir::new().expect("temp dir");
    let dir: PathBuf = root.path().to_path_buf();
    let agent_dir = dir.join("agent");
    let socket = dir.join("daemon.sock");
    write_agent_config(&agent_dir, &spawn_mock(&NEXT));

    let _supervisor = spawn_daemon(&socket, &agent_dir, &kernel_python);
    let mut client = Client::connect(&socket);
    let created = client.request(
        "c1",
        &json!({
            "type": "create",
            "name": "detach-lane",
            "config": {
                "cwd": dir.to_string_lossy(),
                "sessionDir": agent_dir.join("sessions").to_string_lossy(),
                "provider": "prime-inference",
                "model": "mock-1",
            },
        }),
    );
    assert_eq!(created["success"], true, "create failed: {created}");
    let active_id = created["data"]["id"]
        .as_str()
        .or_else(|| created["data"]["activeSessionId"].as_str())
        .expect("active session id")
        .to_string();

    let turn = client.request(
        "p1",
        &json!({
            "type": "prompt_and_wait",
            "activeSessionId": active_id,
            "message": "run the long cell",
        }),
    );
    assert_eq!(turn["success"], true, "the turn failed: {turn}");
    // THE REGRESSION: the turn ended while the cell still ran. A cell that
    // holds its turn ends it only after printing CELL_DONE.
    let after_turn = client.messages(&active_id);
    assert!(
        after_turn.contains("the cell runs on as a job"),
        "the turn did not end: {after_turn}"
    );
    assert!(
        after_turn.contains("settled as job cell-") && !after_turn.contains("CELL_DONE"),
        "the cell held the turn to its end: {after_turn}"
    );

    // The cell's end settles its job, and the job-settled report wakes the
    // idle session into a turn that runs to its reply.
    let woken = wait_until(Duration::from_mins(1), || {
        let messages = client.messages(&active_id);
        messages
            .contains("woken by the settled job")
            .then_some(messages)
    });
    assert!(
        woken.contains("[job-settled job:cell-") && woken.contains("status:ok"),
        "the job-settled report never landed: {woken}"
    );
    assert!(
        woken.contains("CELL_DONE"),
        "the report lacks the cell's output: {woken}"
    );

    client.request(
        "k1",
        &json!({ "type": "kill", "activeSessionId": active_id }),
    );
}
