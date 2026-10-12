//! End-to-end verifier for daemon-wide provider admission
//! (`providerMaxInFlight`): two live subagent sessions, each in its own
//! worker process, prompt one OpenAI-compatible mock whose provider is
//! limited to one request in flight. The supervisor's admission registry
//! must hold the second session's model request until the first one
//! finished: the mock never sees two requests at once, and the waiting
//! session's roster summary reads `admission: queued` while it waits, then
//! `generating` once its request holds the slot.
//!
//! The two sessions are subagents of one idle root: root sessions of one
//! agent dir share the chat's root-turn lease, so two root turns never
//! overlap and could not race for a provider slot.

use std::fmt::Write as _;
use std::io::{BufRead, BufReader, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::process::{Child, Stdio};
use std::sync::{Arc, Condvar, Mutex, MutexGuard, PoisonError};
use std::time::{Duration, Instant};

use eukhe_core::durable::children::{
    RlmChildIdentity, RlmChildPromptRequest, RlmChildSpawnRequest, RlmSubagentHost,
};
use eukhe_daemon::rlm_children::{ParentIdentity, SupervisorChildSessions};
use eukhe_daemon::supervisor_link::SupervisorLink;
use serde_json::{json, Value};

#[path = "support/daemon.rs"]
mod daemon;
use daemon::daemon_command;

/// The limited provider's id.
const PROVIDER: &str = "prime-inference";

/// The two subagents' child ids.
const FIRST: &str = "sub-first";
const SECOND: &str = "sub-second";

struct Supervisor {
    child: Child,
}

impl Drop for Supervisor {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// What the mock provider has seen of the sessions' model requests.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
struct MockCounts {
    /// Requests that reached the mock.
    arrived: usize,
    /// Requests the mock is holding unanswered.
    in_flight: usize,
    /// The most requests ever held at once.
    peak_in_flight: usize,
}

#[derive(Default)]
struct MockState {
    counts: MockCounts,
    /// Requests `1..=released` (in arrival order) may be answered.
    released: usize,
}

/// A mock OpenAI-completions provider that holds every session request
/// unanswered until the test releases it, counting how many it holds at
/// once. The chat-memory compactor's requests (routed under `/memory`)
/// are answered at once and never counted.
struct GatedMock {
    state: Arc<(Mutex<MockState>, Condvar)>,
    port: u16,
}

impl GatedMock {
    fn start() -> GatedMock {
        let state = Arc::new((Mutex::new(MockState::default()), Condvar::new()));
        let listener = TcpListener::bind("127.0.0.1:0").expect("bind mock");
        let port = listener.local_addr().expect("mock addr").port();
        let state_for_thread = Arc::clone(&state);
        std::thread::spawn(move || {
            for stream in listener.incoming() {
                let Ok(stream) = stream else { continue };
                let state = Arc::clone(&state_for_thread);
                std::thread::spawn(move || {
                    let _ = serve(stream, &state);
                });
            }
        });
        GatedMock { state, port }
    }

    fn url(&self) -> String {
        format!("http://127.0.0.1:{}/v1", self.port)
    }

    fn lock(&self) -> MutexGuard<'_, MockState> {
        self.state.0.lock().unwrap_or_else(PoisonError::into_inner)
    }

    fn counts(&self) -> MockCounts {
        self.lock().counts
    }

    /// Let the first `count` requests be answered.
    fn release(&self, count: usize) {
        self.lock().released = count;
        self.state.1.notify_all();
    }

    /// Block until `count` requests reached the mock.
    fn wait_arrived(&self, count: usize) {
        let deadline = Instant::now() + Duration::from_mins(1);
        let mut state = self.lock();
        while state.counts.arrived < count {
            let left = deadline.saturating_duration_since(Instant::now());
            assert!(
                !left.is_zero(),
                "only {} of {count} requests arrived",
                state.counts.arrived
            );
            state = self
                .state
                .1
                .wait_timeout(state, left)
                .unwrap_or_else(PoisonError::into_inner)
                .0;
        }
    }
}

fn serve(mut stream: TcpStream, state: &(Mutex<MockState>, Condvar)) -> std::io::Result<()> {
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
    let content_length = head
        .lines()
        .find_map(|line| {
            line.to_ascii_lowercase()
                .strip_prefix("content-length:")
                .map(|value| value.trim().parse::<usize>().unwrap_or_default())
        })
        .unwrap_or_default();
    let mut body = vec![0u8; content_length];
    reader.read_exact(&mut body)?;
    let memory_request = head
        .lines()
        .next()
        .and_then(|request_line| request_line.split_whitespace().nth(1))
        .is_some_and(|path| path.starts_with("/memory/"));
    if memory_request {
        return write_answer(&mut stream, "user: said hi");
    }
    let (lock, changed) = state;
    let index = {
        let mut state = lock.lock().unwrap_or_else(PoisonError::into_inner);
        state.counts.arrived += 1;
        state.counts.in_flight += 1;
        state.counts.peak_in_flight = state.counts.peak_in_flight.max(state.counts.in_flight);
        let index = state.counts.arrived;
        changed.notify_all();
        while state.released < index {
            state = changed.wait(state).unwrap_or_else(PoisonError::into_inner);
        }
        // Leaves the held set before the answer goes out: the client frees
        // its slot only after reading the whole stream, so a next request
        // that arrives while this one is still counted overlapped it.
        state.counts.in_flight -= 1;
        index
    };
    write_answer(&mut stream, &format!("answer {index}"))
}

fn chunk(delta: &Value, finish_reason: Option<&str>) -> String {
    json!({
        "id": "chatcmpl-test",
        "object": "chat.completion.chunk",
        "created": 0,
        "model": "mock-1",
        "choices": [{ "index": 0, "delta": delta, "finish_reason": finish_reason }]
    })
    .to_string()
}

/// One successful streamed completion carrying `content`.
fn write_answer(stream: &mut TcpStream, content: &str) -> std::io::Result<()> {
    let mut payload = String::new();
    for data in [
        chunk(&json!({"role": "assistant", "content": content}), None),
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

// The child is reaped by `Supervisor`'s `Drop` (kill + wait); clippy cannot
// see through the returned owner.
#[allow(clippy::zombie_processes)]
fn spawn_supervisor(socket: &Path, agent_dir: &Path) -> Supervisor {
    let child = daemon_command()
        .arg("supervisor")
        .arg("--socket")
        .arg(socket)
        .arg("--agent-dir")
        .arg(agent_dir)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .env_remove("PRIME_API_KEY")
        .env_remove("EUKHE_CODING_AGENT_DIR")
        // A supervisor killed at teardown must not leak its session workers
        // into later test binaries.
        .env(
            eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
            "15000",
        )
        .spawn()
        .expect("spawn eukhe-daemon supervisor");
    let supervisor = Supervisor { child };
    let deadline = Instant::now() + Duration::from_secs(10);
    while !socket.exists() {
        assert!(
            Instant::now() < deadline,
            "supervisor socket never appeared"
        );
        std::thread::sleep(Duration::from_millis(20));
    }
    supervisor
}

/// One supervisor client connection.
struct Client {
    reader: BufReader<UnixStream>,
    writer: UnixStream,
}

impl Client {
    fn connect(socket: &Path) -> Client {
        let stream = UnixStream::connect(socket).expect("connect");
        stream
            .set_read_timeout(Some(Duration::from_millis(100)))
            .expect("read timeout");
        let writer = stream.try_clone().expect("clone");
        let mut client = Client {
            reader: BufReader::new(stream),
            writer,
        };
        assert_eq!(client.read_line()["type"], "daemon_hello");
        client
    }

    fn read_line(&mut self) -> Value {
        let deadline = Instant::now() + Duration::from_mins(1);
        let mut line = String::new();
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

    fn send_command(&mut self, id: &str, command: &Value) {
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
    }

    /// The response for `id`; session events on the way are skipped.
    fn response(&mut self, id: &str) -> Value {
        let deadline = Instant::now() + Duration::from_mins(2);
        loop {
            assert!(Instant::now() < deadline, "no response for id {id}");
            let line = self.read_line();
            if line.get("id").and_then(Value::as_str) == Some(id) {
                return line;
            }
        }
    }

    fn request(&mut self, id: &str, command: &Value) -> Value {
        self.send_command(id, command);
        self.response(id)
    }

    /// Create the idle root session the subagents descend from; answers
    /// its `(sessionFile, activeSessionId, sessionId)`.
    fn create_parent(&mut self, cwd: &Path, session_dir: &Path) -> (String, String, String) {
        let created = self.request(
            "create",
            &json!({
                "type": "create",
                "config": {
                    "cwd": cwd.to_string_lossy(),
                    "sessionDir": session_dir.to_string_lossy(),
                    "provider": PROVIDER,
                    "model": "mock-1",
                },
            }),
        );
        assert_eq!(created["success"], true, "create failed: {created}");
        let field = |name: &str| {
            created["data"][name]
                .as_str()
                .unwrap_or_else(|| panic!("create answered no {name}: {created}"))
                .to_owned()
        };
        (
            field("sessionFile"),
            field("activeSessionId"),
            field("sessionId"),
        )
    }

    /// The `admission` field of subagent `child_id`'s roster summary
    /// (`None` when absent).
    fn admission(&mut self, child_id: &str) -> Option<String> {
        let list = self.request("list", &json!({ "type": "list" }));
        assert_eq!(list["success"], true, "list failed: {list}");
        let sessions = list["data"]["sessions"].as_array().expect("sessions");
        let summary = sessions
            .iter()
            .find(|summary| summary["rlmChildId"] == child_id)
            .unwrap_or_else(|| panic!("no roster summary for {child_id}: {list}"));
        summary["admission"].as_str().map(str::to_owned)
    }

    /// Poll the roster until subagent `child_id`'s admission reads
    /// `expected` (`None`: the field is absent).
    fn wait_admission(&mut self, child_id: &str, expected: Option<&str>) {
        let deadline = Instant::now() + Duration::from_secs(30);
        loop {
            let admission = self.admission(child_id);
            if admission.as_deref() == expected {
                return;
            }
            assert!(
                Instant::now() < deadline,
                "{child_id} never read admission={expected:?}, last: {admission:?}"
            );
            std::thread::sleep(Duration::from_millis(50));
        }
    }
}

/// models.json (the limited mock provider plus the compactor's own route)
/// and the global settings limiting the provider to one request in flight.
fn write_agent_config(agent_dir: &Path, mock: &GatedMock) {
    std::fs::write(
        agent_dir.join("models.json"),
        json!({
            "providers": {
                PROVIDER: {
                    "api": "openai-completions",
                    "baseUrl": mock.url(),
                    "apiKey": "sk-admission",
                    "models": [{
                        "id": "mock-1",
                        "name": "Mock 1",
                        "api": "openai-completions",
                        "contextWindow": 128_000,
                        "maxTokens": 4096
                    }]
                },
                // The chat-memory compactor's provider: without its own
                // model it would run on the limited route and take slots.
                "chat-memory": {
                    "api": "openai-completions",
                    "baseUrl": format!("http://127.0.0.1:{}/memory", mock.port),
                    "apiKey": "sk-memory",
                    "models": [{
                        "id": "summarizer",
                        "name": "Summarizer",
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
        json!({
            "providerMaxInFlight": { PROVIDER: 1 },
            "memory": { "model": "chat-memory/summarizer" }
        })
        .to_string(),
    )
    .expect("write settings.json");
}

/// Spawn subagent `child_id` of the root and prompt it: its turn starts
/// and its model request goes to the limited provider.
async fn spawn_and_prompt(children: &SupervisorChildSessions, child_id: &str, session_id: &str) {
    let child = children
        .spawn(RlmChildSpawnRequest {
            idempotency_key: format!("rlm:{child_id}:spawn"),
            child: RlmChildIdentity {
                rlm_child_id: child_id.to_owned(),
                session_id: session_id.to_owned(),
            },
            name: child_id.to_owned(),
            prompt: format!("{child_id} task"),
            model: None,
            thinking: None,
            depth: 1,
            max_depth: 2,
            spawned_by_request_id: None,
            parent_task_id: "1".to_owned(),
        })
        .await
        .expect("spawn child");
    children
        .prompt(RlmChildPromptRequest {
            idempotency_key: format!("rlm:{child_id}:prompt"),
            session_id: child.session_id,
            rlm_child_id: child_id.to_owned(),
            prompt: format!("{child_id} task"),
        })
        .await
        .expect("prompt child");
}

// The test thread blocks on the mock and the supervisor socket while the
// spawned children's link tasks keep running on the runtime's workers.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_limited_provider_admits_one_request_across_sessions() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let mock = GatedMock::start();
    write_agent_config(&agent_dir, &mock);
    let socket = dir.path().join("admission.sock");
    let _supervisor = spawn_supervisor(&socket, &agent_dir);
    let mut observer = Client::connect(&socket);
    let (parent_file, parent_active_id, parent_session_id) =
        observer.create_parent(dir.path(), &session_dir);

    let children = SupervisorChildSessions::new(
        Arc::new(SupervisorLink::new(socket.clone())),
        agent_dir.clone(),
        parent_active_id,
    );
    children.set_identity(ParentIdentity {
        rlm_depth: 0,
        rlm_max_depth: 2,
        model: Some(format!("{PROVIDER}/mock-1")),
        cwd: Some(agent_dir.to_string_lossy().into_owned()),
        session_id: Some(parent_session_id),
        session_file: Some(parent_file),
        thinking: None,
        child_script: None,
    });

    // The first subagent's request takes the one slot and is held there.
    spawn_and_prompt(&children, FIRST, "0a000000-0000-4000-8000-00000000000a").await;
    mock.wait_arrived(1);
    observer.wait_admission(FIRST, Some("generating"));

    // The second subagent's request waits for the slot: it never reaches
    // the provider while the first one is out.
    spawn_and_prompt(&children, SECOND, "0b000000-0000-4000-8000-00000000000b").await;
    observer.wait_admission(SECOND, Some("queued"));
    assert_eq!(
        mock.counts(),
        MockCounts {
            arrived: 1,
            in_flight: 1,
            peak_in_flight: 1,
        }
    );

    // The first request finishes and frees the slot: the waiting request
    // takes it and goes out.
    mock.release(1);
    mock.wait_arrived(2);
    observer.wait_admission(SECOND, Some("generating"));
    observer.wait_admission(FIRST, None);

    // Every later request (the root may answer its children's reports) is
    // answered at once; none of them ever overlapped another.
    mock.release(usize::MAX);
    observer.wait_admission(SECOND, None);
    let counts = mock.counts();
    assert_eq!(
        (counts.in_flight, counts.peak_in_flight),
        (0, 1),
        "{counts:?}"
    );
}
