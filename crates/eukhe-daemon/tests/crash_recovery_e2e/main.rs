//! Crash recovery e2e: `SIGKILL` the session worker, the supervisor, or
//! both while a turn is in each of its states, restart, reattach, and
//! read the durable transcript and the chat memory files:
//!
//! - every turn finishes exactly once (one user entry per prompt, one final
//!   answer, one tool result per tool call),
//! - no entry and no chat-memory message is duplicated (the logger's append
//!   keys), and no user message is lost,
//! - a compaction caught by the crash completes or fails visibly exactly
//!   once,
//! - the chat memory is the pre-crash content plus the finished turn, and
//!   the next turn logs after it.
//!
//! States: the model streaming (the reply held mid-stream), a slow tool
//! call (an `ipython` cell waiting on a release file), a threshold
//! compaction (the summarizer held), the chat-memory compactor (a tree
//! line's summarizer held), and a `codemode` script between its nested
//! calls (`codemode.rs`). The provider is a scripted OpenAI-compatible
//! mock in the test process, so the replacement worker reaches the same
//! script.
// Pedantic-gate dispositions (fleet-uniform ruling).
#![allow(clippy::large_futures)]
#![allow(clippy::too_many_lines)]
#![allow(clippy::cast_possible_truncation)]

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

use serde_json::{json, Value};

#[path = "../support/daemon.rs"]
mod daemon;
#[path = "../../../eukhe-cli/tests/support/durable_store.rs"]
mod durable_store;
#[path = "../support/isolated_supervisor.rs"]
mod isolated_supervisor;
#[path = "../support/mock_llm.rs"]
mod mock_llm;
#[path = "../support/process.rs"]
mod process;
#[path = "../support/wire_client.rs"]
mod wire_client;

mod cases;
mod codemode;

use isolated_supervisor::Supervisor;
use mock_llm::{Logged, MockLlm, Reply, Request, RequestKind, Served};
use wire_client::WireClient;

/// Budget of any one wait on the daemon (generous: parallel e2e load).
const WAIT: Duration = Duration::from_mins(3);

/// The model the mock serves.
const MODEL: &str = "mock-1";

/// Prompt tags the script answers.
const HOLD_STREAM: &str = "[hold-stream]";
const SLOW_TOOL: &str = "[slow-tool]";
const PADDING: &str = "[pad]";

/// Gates the test opens after the restart.
const STREAM_GATE: &str = "stream";
const SUMMARIZER_GATE: &str = "summarizer";
const NODE_GATE: &str = "node";

/// What the crash interrupts.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Phase {
    /// The model streams the turn's answer.
    Stream,
    /// A slow tool call runs.
    Tool,
    /// A blocking threshold compaction's summarizer runs.
    Compaction,
    /// The chat-memory compactor summarizes the turn's long message.
    MemoryNode,
}

/// What dies.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Target {
    Worker,
    Supervisor,
    Both,
}

/// One isolated daemon world: temp agent dir, socket, mock provider.
struct World {
    dir: tempfile::TempDir,
    agent_dir: PathBuf,
    session_dir: PathBuf,
    socket: PathBuf,
    mock: MockLlm,
    supervisor: Option<Supervisor>,
}

impl World {
    fn new(context_window: u64, settings: &Value) -> World {
        let dir = tempfile::tempdir().expect("temp dir");
        let agent_dir = dir.path().join("agent");
        let session_dir = agent_dir.join("sessions");
        std::fs::create_dir_all(&session_dir).expect("session dir");
        let release = dir.path().join("release");
        let mock = MockLlm::start(move |request| script(request, &release));
        std::fs::write(
            agent_dir.join("models.json"),
            mock.models_json(MODEL, context_window, 4096).to_string(),
        )
        .expect("models.json");
        let mut settings = settings.clone();
        settings["defaultProvider"] = json!("mock");
        settings["defaultModel"] = json!(MODEL);
        std::fs::write(agent_dir.join("settings.json"), settings.to_string())
            .expect("settings.json");
        let socket = dir.path().join("daemon.sock");
        let mut world = World {
            dir,
            agent_dir,
            session_dir,
            socket,
            mock,
            supervisor: None,
        };
        world.start_supervisor();
        world
    }

    fn start_supervisor(&mut self) {
        self.supervisor = Some(Supervisor::start(
            &self.socket,
            &self.agent_dir,
            &self.dir.path().join("supervisor.log"),
        ));
    }

    /// The crashed supervisor's guard stays in place: its orphaned workers
    /// belong to the successor once one serves the socket, and are stopped
    /// by this guard if none ever does.
    fn kill_supervisor(&mut self) {
        self.supervisor
            .as_mut()
            .expect("a running supervisor")
            .kill();
    }

    fn release_path(&self) -> PathBuf {
        self.dir.path().join("release")
    }

    fn tool_runs_path(&self) -> PathBuf {
        self.dir.path().join("tool-runs")
    }

    fn connect(&self) -> WireClient {
        WireClient::connect(&self.socket)
    }

    /// Create a session (`rlm_depth` 0: a chat-memory root) and attach;
    /// answers its active id.
    fn create(&self, client: &mut WireClient, rlm_depth: u32) -> String {
        self.open(client, rlm_depth, None)
    }

    /// Resume the one stored session the way a client does after a daemon
    /// restart (`create` naming its storage; a revived worker is joined),
    /// and attach; answers its active id.
    fn resume(&self, client: &mut WireClient, rlm_depth: u32) -> String {
        let dirs = durable_store::session_dirs(&self.session_dir);
        assert_eq!(dirs.len(), 1, "one session storage: {dirs:?}");
        self.open(client, rlm_depth, Some(&dirs[0]))
    }

    fn open(&self, client: &mut WireClient, rlm_depth: u32, storage: Option<&Path>) -> String {
        let config = json!({
            "cwd": self.dir.path().to_string_lossy(),
            "sessionDir": self.session_dir.to_string_lossy(),
            "provider": "mock",
            "model": MODEL,
            "rlmDepth": rlm_depth,
        });
        let mut command = json!({ "type": "create", "config": config });
        if let Some(storage) = storage {
            command["sessionPath"] = json!(storage.to_string_lossy());
        }
        let created = client.request(&command, WAIT);
        assert_eq!(
            created["success"],
            true,
            "create: {created}\n{}",
            self.diagnostics()
        );
        let session_id = created["data"]["activeSessionId"]
            .as_str()
            .expect("active session id")
            .to_string();
        attach(client, &session_id);
        session_id
    }

    fn transcript(&self) -> durable_store::Transcript {
        let dirs = durable_store::session_dirs(&self.session_dir);
        assert_eq!(dirs.len(), 1, "one session storage: {}", self.diagnostics());
        durable_store::read_transcript(&dirs[0])
    }

    /// Every storage with its user texts, and the supervisor log.
    fn diagnostics(&self) -> String {
        let mut report = String::new();
        for dir in durable_store::session_dirs(&self.session_dir) {
            let transcript = durable_store::read_transcript(&dir);
            let _ = writeln!(
                report,
                "storage {}: agent {} users {:?}",
                dir.display(),
                transcript.agent,
                transcript
                    .of_kind("pi.user")
                    .iter()
                    .map(|entry| entry["model"][0]["content"][0]["text"].clone())
                    .collect::<Vec<_>>()
            );
        }
        report.push_str(
            &std::fs::read_to_string(self.dir.path().join("supervisor.log")).unwrap_or_default(),
        );
        for log in log_files(&self.agent_dir) {
            let _ = writeln!(
                report,
                "--- {}\n{}",
                log.display(),
                std::fs::read_to_string(&log).unwrap_or_default()
            );
        }
        report
    }

    /// Every chat-memory message line, in file order.
    fn chat_messages(&self) -> Vec<Value> {
        jsonl_lines(&self.agent_dir.join("chat").join("main"))
    }

    /// Every chat-memory tree line, in file order.
    fn chat_tree(&self) -> Vec<Value> {
        jsonl_lines(&self.agent_dir.join("chat").join("tree"))
    }
}

/// The `*.log` files under `dir`, recursively.
fn log_files(dir: &Path) -> Vec<PathBuf> {
    let mut found = Vec::new();
    for entry in std::fs::read_dir(dir).into_iter().flatten().flatten() {
        let path = entry.path();
        if path.is_dir() {
            found.extend(log_files(&path));
        } else if path.extension().is_some_and(|extension| extension == "log") {
            found.push(path);
        }
    }
    found.sort();
    found
}

/// The lines of every `*.jsonl` file under `dir`, files in name order.
fn jsonl_lines(dir: &Path) -> Vec<Value> {
    let mut files: Vec<PathBuf> = std::fs::read_dir(dir)
        .map(|entries| {
            entries
                .flatten()
                .map(|entry| entry.path())
                .filter(|path| {
                    path.extension()
                        .is_some_and(|extension| extension == "jsonl")
                })
                .collect()
        })
        .unwrap_or_default();
    files.sort();
    files
        .iter()
        .flat_map(|file| {
            std::fs::read_to_string(file)
                .expect("read a chat file")
                .lines()
                .map(|line| serde_json::from_str::<Value>(line).expect("a whole chat line"))
                .collect::<Vec<_>>()
        })
        .collect()
}

fn attach(client: &mut WireClient, session_id: &str) {
    let attached = client.request(
        &json!({ "type": "attach", "activeSessionId": session_id }),
        WAIT,
    );
    assert_eq!(attached["success"], true, "attach: {attached}");
}

/// The mock's script. A turn tagged [`HOLD_STREAM`] streams its answer
/// held on [`STREAM_GATE`]; one tagged [`SLOW_TOOL`] calls `ipython` with a
/// cell that logs its run and waits for the release file, then answers
/// after the tool. Summarizer calls hold on [`SUMMARIZER_GATE`]; tree-line
/// calls hold on [`NODE_GATE`].
fn script(request: &Request, release: &Path) -> Reply {
    match request.kind {
        RequestKind::Summarizer => {
            Reply::text("## Goal\nThe crash test's compacted history.").held(SUMMARIZER_GATE)
        }
        RequestKind::MemoryNode => Reply::text("A padded user message.").held(NODE_GATE),
        RequestKind::Turn => {
            let prompt = prompt_tag(&request.prompt);
            if request.after_tool {
                // The call after the tool answers the prompt its call
                // id names.
                let call = request.tool_results.last().expect("a tool result");
                Reply::text(answer_for(call.strip_prefix("call-").unwrap_or(call)))
            } else if request.prompt.contains(codemode::TAG) {
                Reply::tool_call(
                    format!("call-{prompt}"),
                    "codemode",
                    json!({ "code": codemode::SCRIPT }),
                )
            } else if request.prompt.contains(SLOW_TOOL) {
                let runs = release.with_file_name("tool-runs");
                let code = format!(
                    "import os, time\nwith open({runs:?}, 'a') as f:\n    f.write('run\\n')\nwhile not os.path.exists({release:?}):\n    time.sleep(0.05)\nprint('tool finished')",
                    runs = runs.to_string_lossy(),
                    release = release.to_string_lossy(),
                );
                Reply::tool_call(format!("call-{prompt}"), "ipython", json!({ "code": code }))
            } else if request.prompt.contains(HOLD_STREAM) {
                Reply::text(answer_for(&prompt)).held(STREAM_GATE)
            } else {
                Reply::text(answer_for(&prompt))
            }
        }
    }
}

/// The prompt's first word: its name (`t1`, `crash`, ...), which every
/// answer echoes so the transcript names the turn it answers.
fn prompt_tag(text: &str) -> String {
    // A chat-memory root's request carries the view before the prompt:
    // the prompt is the last line.
    text.lines()
        .last()
        .unwrap_or_default()
        .split_whitespace()
        .next()
        .unwrap_or_default()
        .to_string()
}

fn answer_for(tag: &str) -> String {
    format!("answer to {tag}")
}

/// A prompt named `tag` with `tags`, padded with `pad` filler words.
fn prompt(tag: &str, tags: &[&str], pad: usize) -> String {
    let mut text = tag.to_string();
    for extra in tags {
        text.push(' ');
        text.push_str(extra);
    }
    if pad > 0 {
        text.push(' ');
        text.push_str(PADDING);
        for index in 0..pad {
            let _ = write!(text, " filler{index}");
        }
    }
    text
}

fn worker_pid(client: &mut WireClient, session_id: &str) -> u32 {
    let state = client.request(
        &json!({ "type": "get_state", "activeSessionId": session_id }),
        WAIT,
    );
    assert_eq!(state["success"], true, "get_state: {state}");
    state["data"]["workerPid"].as_u64().expect("the worker pid") as u32
}

fn sigkill(pid: u32) {
    let status = Command::new("kill")
        .arg("-9")
        .arg(pid.to_string())
        .status()
        .expect("run kill");
    assert!(status.success(), "kill -9 {pid}");
}

/// Wait until `pid` is gone (reaped or a zombie).
fn wait_dead(pid: u32) {
    let deadline = Instant::now() + WAIT;
    loop {
        let alive = std::fs::read_to_string(format!("/proc/{pid}/stat")).is_ok_and(|stat| {
            stat.rsplit_once(')')
                .and_then(|(_, rest)| rest.split_whitespace().next())
                .is_some_and(|state| !state.starts_with('Z') && !state.starts_with('X'))
        });
        if !alive {
            return;
        }
        assert!(Instant::now() < deadline, "process {pid} outlived SIGKILL");
        std::thread::sleep(Duration::from_millis(20));
    }
}

/// Reconnect after a worker crash and attach to `session_id`. The
/// supervisor relaunches the worker with backoff and the attach fails
/// until the replacement registered, so the attach repeats until it
/// succeeds or [`WAIT`] runs out.
fn reattach(world: &World, session_id: &str) -> WireClient {
    let deadline = Instant::now() + WAIT;
    let mut refusals = Vec::new();
    loop {
        let mut client = world.connect();
        let attached = client.request(
            &json!({ "type": "attach", "activeSessionId": session_id }),
            WAIT,
        );
        if attached["success"] == true {
            return client;
        }
        refusals.push(attached["error"].clone());
        assert!(
            Instant::now() < deadline,
            "the session never reattached: {refusals:?}"
        );
        std::thread::sleep(Duration::from_millis(100));
    }
}

/// Wait until the session is idle with nothing queued.
fn wait_idle(client: &mut WireClient, session_id: &str) {
    let idle = client.request(
        &json!({ "type": "wait_for_idle", "activeSessionId": session_id }),
        WAIT,
    );
    assert_eq!(idle["success"], true, "wait_for_idle: {idle}");
}

/// Run one prompt to completion on `client`.
fn run_turn(client: &mut WireClient, session_id: &str, message: &str) {
    let done = client.request(
        &json!({ "type": "prompt_and_wait", "activeSessionId": session_id, "message": message }),
        WAIT,
    );
    assert_eq!(done["success"], true, "prompt {message:?}: {done}");
}

/// The text blocks of a model message.
fn texts(message: &Value) -> Vec<String> {
    match &message["content"] {
        Value::String(text) => vec![text.clone()],
        Value::Array(blocks) => blocks
            .iter()
            .filter_map(|block| block["text"].as_str().map(str::to_string))
            .collect(),
        _ => Vec::new(),
    }
}

/// The transcript's model messages of `role`, with their entry ids.
fn messages_of(transcript: &durable_store::Transcript, role: &str) -> Vec<(u64, Value)> {
    transcript
        .entries
        .iter()
        .flat_map(|entry| {
            let id = entry["id"].as_u64().expect("entry id");
            entry["model"]
                .as_array()
                .cloned()
                .unwrap_or_default()
                .into_iter()
                .filter(|message| message["role"] == role)
                .map(move |message| (id, message))
        })
        .collect()
}

/// The transcript's turn-level invariants: ids strictly increase, each
/// prompt in `prompts` is stored exactly once and in order, each answer is
/// stored exactly once, and every tool call has exactly one result.
fn assert_transcript(world: &World, prompts: &[String]) {
    let transcript = world.transcript();
    let ids: Vec<u64> = transcript
        .entries
        .iter()
        .map(|entry| entry["id"].as_u64().expect("entry id"))
        .collect();
    assert!(
        ids.windows(2).all(|pair| pair[0] < pair[1]),
        "entry ids are not monotonic: {ids:?}"
    );
    let users: Vec<String> = transcript
        .of_kind("pi.user")
        .iter()
        .flat_map(|entry| entry["model"].as_array().cloned().unwrap_or_default())
        .flat_map(|message| texts(&message))
        .collect();
    assert_eq!(
        &users, prompts,
        "every prompt stored exactly once, in order"
    );
    let answers: Vec<String> = messages_of(&transcript, "assistant")
        .iter()
        .flat_map(|(_, message)| texts(message))
        .filter(|text| text.starts_with("answer to "))
        .collect();
    let expected: Vec<String> = prompts
        .iter()
        .map(|prompt| answer_for(&prompt_tag(prompt)))
        .collect();
    assert_eq!(answers, expected, "every turn answered exactly once");
    let mut calls = BTreeMap::new();
    for (_, message) in messages_of(&transcript, "assistant") {
        for block in message["content"].as_array().cloned().unwrap_or_default() {
            if block["type"] == "toolCall" {
                *calls
                    .entry(block["id"].as_str().expect("call id").to_string())
                    .or_insert(0usize) += 1;
            }
        }
    }
    let mut results = BTreeMap::new();
    for (_, message) in messages_of(&transcript, "toolResult") {
        *results
            .entry(
                message["toolCallId"]
                    .as_str()
                    .expect("tool call id")
                    .to_string(),
            )
            .or_insert(0usize) += 1;
    }
    assert!(
        calls.values().all(|count| *count == 1),
        "a tool call is stored twice: {calls:?}"
    );
    assert_eq!(
        calls.keys().collect::<Vec<_>>(),
        results.keys().collect::<Vec<_>>(),
        "every tool call has a result"
    );
    assert!(
        results.values().all(|count| *count == 1),
        "a tool result is stored twice: {results:?}"
    );
}

/// The chat log's invariants: ids are `0..n` in order, no append key
/// repeats, and every keyed scope counts `0..` without a gap.
fn assert_chat_log(messages: &[Value]) {
    let ids: Vec<u64> = messages
        .iter()
        .map(|message| message["i"].as_u64().expect("message id"))
        .collect();
    assert_eq!(
        ids,
        (0..messages.len() as u64).collect::<Vec<_>>(),
        "chat message ids are 0..n"
    );
    let mut scopes: BTreeMap<String, Vec<u64>> = BTreeMap::new();
    for message in messages {
        if let Some(key) = message.get("key") {
            scopes
                .entry(key["scope"].as_str().expect("key scope").to_string())
                .or_default()
                .push(key["seq"].as_u64().expect("key seq"));
        }
    }
    for (scope, seqs) in &scopes {
        assert_eq!(
            seqs,
            &(0..seqs.len() as u64).collect::<Vec<_>>(),
            "scope {scope}: append keys repeat or skip"
        );
    }
}

/// The tree's invariant: each node `(l, i)` is written at most once.
fn assert_chat_tree(lines: &[Value]) {
    let mut nodes = BTreeSet::new();
    for line in lines {
        if line.get("merge").is_some() {
            continue;
        }
        let node = (
            line["l"].as_u64().expect("node level"),
            line["i"].as_u64().expect("node index"),
        );
        assert!(nodes.insert(node), "tree node {node:?} written twice");
    }
}

/// `(kind, text)` of chat messages, the part a crash must not change.
fn chat_content(messages: &[Value]) -> Vec<(String, String)> {
    messages
        .iter()
        .map(|message| {
            (
                message["kind"].as_str().expect("kind").to_string(),
                message["text"].as_str().expect("text").to_string(),
            )
        })
        .collect()
}

/// Requests of the log matching `probe`.
fn requests(log: &[Logged], probe: impl Fn(&Logged) -> bool) -> Vec<&Logged> {
    log.iter().filter(|entry| probe(entry)).collect()
}

fn served(log: &[Logged]) -> Vec<Served> {
    log.iter().map(|entry| entry.served).collect()
}
