//! The main+worker eval (docs/usage.md, main and worker; the design's
//! "measured before default"): the golden tasks of [`tasks`] run in both
//! session shapes (`single`, `main-worker`) on the same model, each run
//! at least twice, through the real supervisor. While each task's first,
//! long tool call runs, the user sends three context messages, a redirect,
//! a status question and an unrelated request. Each run records:
//!
//! - success (the rubric: the file the work leaves holds every required
//!   substring, and an answer in the user's session holds the unrelated
//!   request's answer);
//! - wall time from the work order to the last answer;
//! - tokens and cost (`get_session_stats` of every session of the run);
//! - interrupted tool calls (a result that says it was aborted or
//!   interrupted, or a call with no result): must be 0 in `main-worker`;
//! - per message: how the user's session handled it (main's tool, or the
//!   single session's steer), how many of the working session's messages
//!   carry it (the worker gets the user's words once), and how long the
//!   first answer after it took.
//!
//! It prints one row per run, a summary per shape and the tasks that
//! flipped (a different verdict across shapes or runs); with
//! `EUKHE_EVAL_OUT` set it also writes every run as JSON there.
//!
//! Engines: by default the scripted faux model (the deterministic
//! mechanics: placement, verbatim delivery, no interrupted call, latency).
//! With `EUKHE_EVAL_MODEL=<provider>/<model>` and `EUKHE_EVAL_AGENT_DIR`
//! (an agent dir holding that provider's `auth.json`; copied into each
//! run's own agent dir) every run uses that model for main, worker and
//! single alike (the quality numbers). `EUKHE_EVAL_RUNS` (default 2) and
//! `EUKHE_EVAL_TASKS` (comma-separated ids) narrow it.
//!
//! ```text
//! cargo test -p eukhe-daemon --test front_worker_eval -- --ignored --nocapture
//! ```

#[path = "../support/daemon.rs"]
mod daemon;
#[path = "../support/process.rs"]
mod process;
mod tasks;
#[path = "../support/wire_client.rs"]
mod wire_client;

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use daemon::supervisor_command;
use process::Daemon;
use serde_json::{json, Value};
use tasks::{Task, BUILD_SECONDS, STATUS, TASKS};
use wire_client::WireClient;

/// One reply of the daemon.
const REPLY: Duration = Duration::from_secs(60);
/// The whole of one run, a real model's included.
const RUN: Duration = Duration::from_secs(600);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Shape {
    Single,
    MainWorker,
}

impl Shape {
    fn setting(self) -> &'static str {
        match self {
            Shape::Single => "single",
            Shape::MainWorker => "main-worker",
        }
    }
}

/// The model every session of a run talks to.
enum Engine {
    /// Scripted faux responses (the mechanics).
    Faux,
    /// A real provider: `provider/model` and the agent dir holding its
    /// credentials.
    Provider { model: String, auth_dir: PathBuf },
}

impl Engine {
    fn from_env() -> Engine {
        match (
            std::env::var("EUKHE_EVAL_MODEL"),
            std::env::var_os("EUKHE_EVAL_AGENT_DIR"),
        ) {
            (Ok(model), Some(dir)) => Engine::Provider {
                model,
                auth_dir: PathBuf::from(dir),
            },
            _ => Engine::Faux,
        }
    }

    fn name(&self) -> String {
        match self {
            Engine::Faux => "faux".to_owned(),
            Engine::Provider { model, .. } => model.clone(),
        }
    }
}

/// The kinds of the scripted mid-task messages, in the order they go.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    Context,
    Redirect,
    Status,
    Unrelated,
}

impl Kind {
    fn label(self) -> &'static str {
        match self {
            Kind::Context => "context",
            Kind::Redirect => "redirect",
            Kind::Status => "status",
            Kind::Unrelated => "unrelated",
        }
    }
}

fn messages(task: &Task) -> Vec<(Kind, &'static str)> {
    let mut all: Vec<(Kind, &'static str)> = task
        .contexts
        .iter()
        .map(|text| (Kind::Context, *text))
        .collect();
    all.push((Kind::Redirect, task.redirect));
    all.push((Kind::Status, STATUS));
    all.push((Kind::Unrelated, task.unrelated.0));
    all
}

/// How one mid-task message was handled.
struct Handled {
    kind: Kind,
    text: &'static str,
    /// Main's tools for it (`main-worker`), or `steer` (`single`).
    route: String,
    /// The working session's user and custom rows that carry its words.
    delivered: usize,
    /// From sending it to the first answer with text in the user's session.
    reply_ms: Option<u64>,
}

struct RunResult {
    task: &'static str,
    shape: Shape,
    run: usize,
    file_ok: bool,
    unrelated_ok: bool,
    wall_ms: u64,
    tokens: u64,
    cost: f64,
    tool_calls: usize,
    interrupted: usize,
    handled: Vec<Handled>,
    error: Option<String>,
}

impl RunResult {
    fn success(&self) -> bool {
        self.error.is_none() && self.file_ok && self.unrelated_ok
    }

    fn json(&self) -> Value {
        json!({
            "task": self.task,
            "shape": self.shape.setting(),
            "run": self.run,
            "success": self.success(),
            "fileOk": self.file_ok,
            "unrelatedOk": self.unrelated_ok,
            "wallMs": self.wall_ms,
            "tokens": self.tokens,
            "cost": self.cost,
            "toolCalls": self.tool_calls,
            "interrupted": self.interrupted,
            "error": self.error,
            "messages": self.handled.iter().map(|handled| json!({
                "kind": handled.kind.label(),
                "text": handled.text,
                "route": handled.route,
                "delivered": handled.delivered,
                "replyMs": handled.reply_ms,
            })).collect::<Vec<_>>(),
        })
    }
}

fn now_ms() -> u64 {
    let since = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("the clock is after the epoch");
    u64::try_from(since.as_millis()).expect("milliseconds fit u64")
}

fn elapsed_ms(since: Instant) -> u64 {
    u64::try_from(since.elapsed().as_millis()).expect("milliseconds fit u64")
}

/// The text of a wire message's content (a string or blocks).
fn text_of(message: &Value) -> String {
    match &message["content"] {
        Value::String(text) => text.clone(),
        Value::Array(blocks) => blocks
            .iter()
            .filter_map(|block| block["text"].as_str())
            .collect::<Vec<_>>()
            .join("\n"),
        _ => String::new(),
    }
}

fn tool_calls(message: &Value) -> Vec<&Value> {
    message["content"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|block| block["type"] == "toolCall")
        .collect()
}

// ---------------------------------------------------------------------------
// Faux scripts
// ---------------------------------------------------------------------------

fn call(name: &str, arguments: &Value) -> Value {
    json!({ "content": [{ "type": "toolCall", "name": name, "arguments": arguments }] })
}

fn step(text: &str, code: &str) -> Value {
    json!({ "content": [
        { "type": "text", "text": text },
        { "type": "toolCall", "name": "python", "arguments": { "code": code } },
    ] })
}

/// The working session's script: the long build, then the file with every
/// note folded in, then the answer (`single` also answers the unrelated
/// request there: it has no one else to).
fn worker_script(task: &Task, shape: Shape) -> Value {
    let content = serde_json::to_string(task.scripted_content).expect("a JSON string");
    let file = serde_json::to_string(task.file).expect("a JSON string");
    let answer = match shape {
        Shape::Single => format!(
            "Done: wrote {}. And {} -> {}.",
            task.file, task.unrelated.0, task.unrelated.1
        ),
        Shape::MainWorker => format!("Done: wrote {}.", task.file),
    };
    json!({
        "repeatLastResponse": true,
        "responses": [
            step(
                "Running the simulated build first.",
                &format!("import time\ntime.sleep({BUILD_SECONDS})\nprint('build done')"),
            ),
            step(
                &format!("Build done; writing {} with your notes folded in.", task.file),
                &format!("open({file}, 'w').write({content})\nprint('wrote')"),
            ),
            { "text": answer },
        ],
    })
}

/// Main's script (`main-worker`): the hand-over, then per message the tool
/// a router would pick and a short answer, then the worker's report.
fn main_script(task: &Task) -> Value {
    let mut responses = vec![
        call("worker_assign", &json!({})),
        json!({ "text": "On it: the worker has the task." }),
    ];
    for (kind, _) in messages(task) {
        match kind {
            Kind::Context => responses.extend([
                call("worker_forward", &json!({ "kind": "context" })),
                json!({ "text": "Passed to the worker as context." }),
            ]),
            Kind::Redirect => responses.extend([
                call("worker_forward", &json!({ "kind": "redirect" })),
                json!({ "text": "Passed to the worker as a redirect." }),
            ]),
            Kind::Status => responses.extend([
                call("worker_status", &json!({})),
                json!({ "text": "The worker is on its build step." }),
            ]),
            Kind::Unrelated => responses.push(json!({
                "text": format!("{} -> {}", task.unrelated.0, task.unrelated.1),
            })),
        }
    }
    responses.push(json!({ "text": format!("The worker reports: {} is written.", task.file) }));
    json!({ "repeatLastResponse": true, "responses": responses })
}

// ---------------------------------------------------------------------------
// One run
// ---------------------------------------------------------------------------

struct Session<'a> {
    client: &'a mut WireClient,
}

impl Session<'_> {
    fn data(&mut self, command: &Value) -> Result<Value, String> {
        let reply = self.client.request(command, REPLY);
        if reply["success"] == true {
            Ok(reply["data"].clone())
        } else {
            Err(format!("{} failed: {reply}", command["type"]))
        }
    }

    fn messages(&mut self, session: &str) -> Result<Vec<Value>, String> {
        let data = self.data(&json!({ "type": "get_messages", "activeSessionId": session }))?;
        Ok(data["messages"].as_array().cloned().unwrap_or_default())
    }

    fn state(&mut self, session: &str) -> Result<Value, String> {
        self.data(&json!({ "type": "get_state", "activeSessionId": session }))
    }

    /// Wait until `session` is idle, observing the user's session's
    /// answers meanwhile.
    fn idle_observing(
        &mut self,
        session: &str,
        user: &str,
        answers: &mut Answers,
    ) -> Result<(), String> {
        let id = self
            .client
            .send(&json!({ "type": "wait_for_idle", "activeSessionId": session }));
        let reply = poll(RUN, "idle", || {
            answers.observe(&self.messages(user)?);
            Ok(self.client.try_response(&id))
        })?;
        if reply["success"] == true {
            Ok(())
        } else {
            Err(format!("wait_for_idle failed: {reply}"))
        }
    }

    /// Main's workers' live ids and states.
    fn workers(&mut self, main: &str) -> Result<Vec<(String, String)>, String> {
        Ok(self.state(main)?["workers"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|worker| {
                (
                    worker["activeSessionId"]
                        .as_str()
                        .unwrap_or_default()
                        .to_owned(),
                    worker["state"].as_str().unwrap_or_default().to_owned(),
                )
            })
            .collect())
    }

    fn usage(&mut self, session: &str) -> Result<(u64, f64), String> {
        let stats =
            self.data(&json!({ "type": "get_session_stats", "activeSessionId": session }))?;
        Ok((
            stats["tokens"]["total"].as_u64().unwrap_or_default(),
            stats["cost"].as_f64().unwrap_or_default(),
        ))
    }
}

/// One answer of the user's session, as this client first saw it.
struct Answer {
    seen_ms: u64,
    text: String,
    /// Its tool calls (`name(kind)` for a forward).
    tools: Vec<String>,
}

/// The user's session's answers in the order this client first saw them:
/// the faux model stamps its replies when its script loads, so the wire
/// timestamps cannot time them.
#[derive(Default)]
struct Answers {
    rows: Vec<Answer>,
}

impl Answers {
    fn observe(&mut self, messages: &[Value]) {
        let assistants: Vec<&Value> = messages
            .iter()
            .filter(|message| message["role"] == "assistant")
            .collect();
        let seen_ms = now_ms();
        for message in assistants.iter().skip(self.rows.len()) {
            self.rows.push(Answer {
                seen_ms,
                text: text_of(message),
                tools: tool_calls(message)
                    .iter()
                    .map(|call| {
                        let name = call["name"].as_str().unwrap_or_default();
                        match call["arguments"]["kind"].as_str() {
                            Some(kind) => format!("{name}({kind})"),
                            None => name.to_owned(),
                        }
                    })
                    .collect(),
            });
        }
    }

    /// When the first answer with text after `at` was seen.
    fn reply_after(&self, at: u64) -> Option<u64> {
        self.rows
            .iter()
            .find(|answer| answer.seen_ms >= at && !answer.text.trim().is_empty())
            .map(|answer| answer.seen_ms)
    }
}

/// Poll `probe` every 100 ms until it answers `Some`, at most `budget`.
fn poll<T>(
    budget: Duration,
    what: &str,
    mut probe: impl FnMut() -> Result<Option<T>, String>,
) -> Result<T, String> {
    let deadline = Instant::now() + budget;
    loop {
        if let Some(found) = probe()? {
            return Ok(found);
        }
        if Instant::now() >= deadline {
            return Err(format!("timed out waiting for {what}"));
        }
        std::thread::sleep(Duration::from_millis(100));
    }
}

/// Whether the working session has a model-issued call with no result yet.
fn in_tool(messages: &[Value]) -> bool {
    let calls: usize = messages
        .iter()
        .filter(|message| message["role"] == "assistant")
        .map(|message| tool_calls(message).len())
        .sum();
    let results = messages
        .iter()
        .filter(|message| message["role"] == "toolResult")
        .count();
    calls > results
}

fn copy_credentials(from: &Path, to: &Path) {
    for name in ["auth.json", "models.json"] {
        let source = from.join(name);
        if source.is_file() {
            std::fs::copy(&source, to.join(name)).expect("copy the eval credentials");
        }
    }
}

fn run(engine: &Engine, task: &'static Task, shape: Shape, index: usize) -> RunResult {
    let mut result = RunResult {
        task: task.id,
        shape,
        run: index,
        file_ok: false,
        unrelated_ok: false,
        wall_ms: 0,
        tokens: 0,
        cost: 0.0,
        tool_calls: 0,
        interrupted: 0,
        handled: Vec::new(),
        error: None,
    };
    if let Err(error) = run_into(engine, task, shape, &mut result) {
        result.error = Some(error);
    }
    result
}

#[allow(clippy::too_many_lines)] // one run, read top to bottom
fn run_into(
    engine: &Engine,
    task: &'static Task,
    shape: Shape,
    result: &mut RunResult,
) -> Result<(), String> {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent = dir.path().join("agent");
    let workspace = dir.path().join("ws");
    std::fs::create_dir_all(&agent).expect("agent dir");
    std::fs::create_dir_all(&workspace).expect("workspace");
    std::fs::write(
        agent.join("settings.json"),
        json!({ "onboardingShown": true, "sessionShape": shape.setting() }).to_string(),
    )
    .expect("settings");
    let socket = dir.path().join("d.sock");
    let mut config = json!({
        "cwd": workspace.to_string_lossy(),
        "sessionDir": agent.join("sessions").to_string_lossy(),
    });
    let mut prompt = task.prompt.to_owned();
    match engine {
        Engine::Faux => {
            let (session_script, child_script) = match shape {
                Shape::Single => (worker_script(task, shape), None),
                Shape::MainWorker => (main_script(task), Some(worker_script(task, shape))),
            };
            let path = dir.path().join("script.json");
            std::fs::write(&path, session_script.to_string()).expect("script");
            config["script"] = json!(path.to_string_lossy());
            if let Some(child) = child_script {
                let path = dir.path().join("child.json");
                std::fs::write(&path, child.to_string()).expect("child script");
                config["childScript"] = json!(path.to_string_lossy());
            }
        }
        Engine::Provider { model, auth_dir } => {
            copy_credentials(auth_dir, &agent);
            let (provider, id) = model
                .split_once('/')
                .ok_or("EUKHE_EVAL_MODEL is <provider>/<model>")?;
            config["provider"] = json!(provider);
            config["model"] = json!(id);
            let _ = write!(
                prompt,
                " Before writing it, run a simulated build in one tool call: \
                 `import time; time.sleep({BUILD_SECONDS})`."
            );
        }
    }
    let _daemon = Daemon::spawn_bound(
        &mut supervisor_command(&socket, &agent),
        &socket,
        Duration::from_secs(20),
    );
    let mut client = WireClient::connect(&socket);
    let mut wire = Session {
        client: &mut client,
    };
    let created = wire.data(&json!({ "type": "create", "config": config }))?;
    let main = created["activeSessionId"]
        .as_str()
        .ok_or("create answered no activeSessionId")?
        .to_owned();

    let started = Instant::now();
    let mut answers = Answers::default();
    wire.data(&json!({ "type": "prompt", "activeSessionId": main, "message": prompt }))?;
    let working = match shape {
        Shape::Single => main.clone(),
        Shape::MainWorker => {
            // A watch attach, as the TUI's worker pane: it reads the
            // worker without taking its approvals or holding its kernel.
            // The row can name the worker before its session routes.
            poll(RUN, "main's worker, attached", || {
                let Some((worker, _)) = wire.workers(&main)?.into_iter().next() else {
                    return Ok(None);
                };
                let attach = json!({
                    "type": "attach", "activeSessionId": worker, "clientKind": "watch",
                });
                Ok(wire.data(&attach).is_ok().then_some(worker))
            })?
        }
    };
    poll(RUN, "the work's first tool call", || {
        answers.observe(&wire.messages(&main)?);
        Ok(in_tool(&wire.messages(&working)?).then_some(()))
    })?;

    // The mid-task messages, while that call runs.
    let mut sent = Vec::new();
    for (kind, text) in messages(task) {
        let at = now_ms();
        sent.push((kind, text, at));
        match shape {
            Shape::MainWorker => {
                wire.data(&json!({ "type": "prompt", "activeSessionId": main, "message": text }))?;
                poll(RUN, "main's answer", || {
                    answers.observe(&wire.messages(&main)?);
                    Ok(answers.reply_after(at).map(drop))
                })?;
                wire.idle_observing(&main, &main, &mut answers)?;
            }
            Shape::Single => {
                wire.data(&json!({ "type": "steer", "activeSessionId": main, "message": text }))?;
                std::thread::sleep(Duration::from_millis(200));
                answers.observe(&wire.messages(&main)?);
            }
        }
    }

    // The end: the work settled and main answered its report.
    match shape {
        Shape::Single => wire.idle_observing(&main, &main, &mut answers)?,
        Shape::MainWorker => {
            let ours: Vec<&str> = sent.iter().map(|(_, text, _)| *text).collect();
            poll(RUN, "the workers' reports, answered", || {
                let rows = wire.messages(&main)?;
                answers.observe(&rows);
                let workers = wire.workers(&main)?;
                let settled = workers
                    .iter()
                    .all(|(_, state)| state == "idle" || state == "stopped");
                let reported = rows.iter().any(|message| {
                    (message["role"] == "user" || message["role"] == "custom")
                        && !ours.iter().any(|text| text_of(message) == *text)
                        && text_of(message) != prompt
                });
                let answered = rows.last().is_some_and(|last| {
                    last["role"] == "assistant" && last["stopReason"] == "stop"
                });
                Ok((settled && reported && answered).then_some(()))
            })?;
            wire.idle_observing(&main, &main, &mut answers)?;
        }
    }
    result.wall_ms = elapsed_ms(started);
    answers.observe(&wire.messages(&main)?);

    // Score it.
    let mut sessions = vec![main.clone()];
    if shape == Shape::MainWorker {
        sessions.extend(wire.workers(&main)?.into_iter().map(|(id, _)| id));
    }
    let mut all_rows = Vec::new();
    for session in &sessions {
        let (tokens, cost) = wire.usage(session)?;
        result.tokens += tokens;
        result.cost += cost;
        all_rows.extend(wire.messages(session)?);
    }
    let calls: usize = all_rows
        .iter()
        .filter(|message| message["role"] == "assistant")
        .map(|message| tool_calls(message).len())
        .sum();
    let results: Vec<&Value> = all_rows
        .iter()
        .filter(|message| message["role"] == "toolResult")
        .collect();
    result.tool_calls = calls;
    let broken = results
        .iter()
        .filter(|message| {
            let text = text_of(message).to_lowercase();
            message["isError"] == true
                && ["abort", "interrupt", "cancel", "killed"]
                    .iter()
                    .any(|word| text.contains(word))
        })
        .count();
    result.interrupted = broken + calls.saturating_sub(results.len());

    let file = std::fs::read_to_string(workspace.join(task.file)).unwrap_or_default();
    result.file_ok = task.must_hold.iter().all(|needle| file.contains(needle));
    result.unrelated_ok = answers
        .rows
        .iter()
        .any(|answer| answer.text.contains(task.unrelated.1));
    let working_rows = wire.messages(&working)?;
    for (position, (kind, text, at)) in sent.iter().enumerate() {
        let until = sent.get(position + 1).map_or(u64::MAX, |next| next.2);
        let route = match shape {
            Shape::Single => "steer".to_owned(),
            Shape::MainWorker => {
                let tools: Vec<String> = answers
                    .rows
                    .iter()
                    .filter(|answer| answer.seen_ms >= *at && answer.seen_ms < until)
                    .flat_map(|answer| answer.tools.iter().cloned())
                    .collect();
                if tools.is_empty() {
                    "answered".to_owned()
                } else {
                    tools.join("+")
                }
            }
        };
        let delivered = working_rows
            .iter()
            .filter(|message| message["role"] == "user" || message["role"] == "custom")
            .filter(|message| text_of(message).contains(text))
            .count();
        result.handled.push(Handled {
            kind: *kind,
            text,
            route,
            delivered,
            reply_ms: answers.reply_after(*at).map(|seen| seen - at),
        });
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Report
// ---------------------------------------------------------------------------

fn seconds(ms: u64) -> String {
    format!("{}.{}", ms / 1000, (ms % 1000) / 100)
}

fn row(result: &RunResult) -> String {
    let replies: Vec<String> = result
        .handled
        .iter()
        .map(|handled| {
            format!(
                "{}:{}/{}x/{}",
                handled.kind.label(),
                handled.route,
                handled.delivered,
                handled.reply_ms.map_or("-".to_owned(), |ms| ms.to_string()),
            )
        })
        .collect();
    format!(
        "| {} | {} | {} | {} | {} | {} | {:.4} | {}/{} | {} | {} |",
        result.task,
        result.shape.setting(),
        result.run,
        if result.success() { "pass" } else { "FAIL" },
        seconds(result.wall_ms),
        result.tokens,
        result.cost,
        result.interrupted,
        result.tool_calls,
        replies.join(" "),
        result.error.as_deref().unwrap_or(""),
    )
}

fn median(mut values: Vec<u64>) -> u64 {
    values.sort_unstable();
    values.get(values.len() / 2).copied().unwrap_or_default()
}

fn summary(results: &[RunResult], shape: Shape) -> String {
    let runs: Vec<&RunResult> = results.iter().filter(|r| r.shape == shape).collect();
    let passed = runs.iter().filter(|r| r.success()).count();
    let replies = |kinds: &[Kind]| -> u64 {
        median(
            runs.iter()
                .flat_map(|r| r.handled.iter())
                .filter(|handled| kinds.contains(&handled.kind))
                .filter_map(|handled| handled.reply_ms)
                .collect(),
        )
    };
    let to_worker: usize = runs
        .iter()
        .flat_map(|r| {
            r.handled
                .iter()
                .filter(|handled| matches!(handled.kind, Kind::Context | Kind::Redirect))
                .map(|handled| usize::from(handled.delivered == 1))
        })
        .sum();
    let forwarded = runs.len() * 4;
    format!(
        "| {} | {passed}/{} | {} | {} | {:.4} | {} | {} | {} | {} | {}/{forwarded} |",
        shape.setting(),
        runs.len(),
        seconds(median(runs.iter().map(|r| r.wall_ms).collect())),
        runs.iter().map(|r| r.tokens).sum::<u64>(),
        runs.iter().map(|r| r.cost).sum::<f64>(),
        runs.iter().map(|r| r.interrupted).sum::<usize>(),
        replies(&[Kind::Context, Kind::Redirect]),
        replies(&[Kind::Status]),
        replies(&[Kind::Unrelated]),
        to_worker,
    )
}

/// Tasks whose verdict differs across shapes or runs.
fn flips(results: &[RunResult]) -> Vec<String> {
    let mut flipped = Vec::new();
    for task in &TASKS {
        let verdicts = |shape: Shape| -> Vec<bool> {
            results
                .iter()
                .filter(|r| r.task == task.id && r.shape == shape)
                .map(RunResult::success)
                .collect()
        };
        let (single, worker) = (verdicts(Shape::Single), verdicts(Shape::MainWorker));
        let consistent = |runs: &[bool]| runs.windows(2).all(|pair| pair[0] == pair[1]);
        if single.is_empty() && worker.is_empty() {
            continue;
        }
        if !consistent(&single) || !consistent(&worker) || single.first() != worker.first() {
            flipped.push(format!(
                "{}: single {single:?}, main-worker {worker:?}",
                task.id
            ));
        }
    }
    flipped
}

#[test]
#[ignore = "the main+worker eval: minutes of real runs; run on demand with --ignored --nocapture"]
fn front_worker_eval() {
    let engine = Engine::from_env();
    let runs: usize = std::env::var("EUKHE_EVAL_RUNS")
        .ok()
        .and_then(|runs| runs.parse().ok())
        .unwrap_or(2);
    let only: Option<Vec<String>> = std::env::var("EUKHE_EVAL_TASKS")
        .ok()
        .map(|ids| ids.split(',').map(str::to_owned).collect());
    let mut results = Vec::new();
    for task in &TASKS {
        if only
            .as_ref()
            .is_some_and(|only| !only.iter().any(|id| id == task.id))
        {
            continue;
        }
        for index in 1..=runs {
            for shape in [Shape::Single, Shape::MainWorker] {
                let result = run(&engine, task, shape, index);
                println!("{}", row(&result));
                results.push(result);
            }
        }
    }
    let mut report = format!(
        "\n## Eval: engine {}, {runs} run(s) per task and shape\n\n",
        engine.name()
    );
    report.push_str(
        "| task | shape | run | rubric | wall s | tokens | cost | interrupted/calls | messages (kind:route/delivered/reply ms) | error |\n|---|---|---|---|---|---|---|---|---|---|\n",
    );
    for result in &results {
        report.push_str(&row(result));
        report.push('\n');
    }
    report.push_str(
        "\n| shape | success | median wall s | tokens | cost | interrupted | median reply ms: context+redirect | status | unrelated | context+redirect delivered once |\n|---|---|---|---|---|---|---|---|---|---|\n",
    );
    for shape in [Shape::Single, Shape::MainWorker] {
        report.push_str(&summary(&results, shape));
        report.push('\n');
    }
    let flipped = flips(&results);
    let _ = write!(
        report,
        "\nFlipped tasks: {}\n",
        if flipped.is_empty() {
            "none".to_owned()
        } else {
            flipped.join("; ")
        }
    );
    println!("{report}");
    if let Some(out) = std::env::var_os("EUKHE_EVAL_OUT") {
        let all: Vec<Value> = results.iter().map(RunResult::json).collect();
        std::fs::write(
            PathBuf::from(out),
            serde_json::to_string_pretty(&json!({ "engine": engine.name(), "runs": all }))
                .expect("JSON"),
        )
        .expect("write EUKHE_EVAL_OUT");
    }
    let interrupted: usize = results
        .iter()
        .filter(|r| r.shape == Shape::MainWorker)
        .map(|r| r.interrupted)
        .sum();
    assert_eq!(interrupted, 0, "main-worker interrupted a tool call");
}
