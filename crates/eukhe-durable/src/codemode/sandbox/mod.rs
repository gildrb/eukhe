//! The code mode sandbox (pi-codemode `CodemodeSandboxBase.start()` and its
//! host side, `runtime/execution.ts`): runs one script deterministically in
//! a `QuickJS` VM on its own thread, with the caller answering its calls.
//!
//! The same script, start time, seed, tools, globals, and store, answered
//! with the same results in the same `seq` order, makes the same calls with
//! the same arguments and produces the same output, on any VM with the same
//! fingerprint, so a host can replay it after a restart. The VM runs in UTC,
//! its clock reads `started_at` and then the `now` of the result being
//! processed, its randomness comes from `seed`, and `WeakRef`,
//! `FinalizationRegistry`, timers, I/O, and modules do not exist.
//!
//! The host owns everything the script must not influence: call records,
//! output, the deadline, aborts, and the decoding of what the VM reports.
//! The first terminal event wins: the script's end, a VM crash, the
//! deadline, or an abort; then the VM is stopped and the run's last event,
//! [`CodemodeRunEvent::Finished`], carries the result.

mod vm;

use std::collections::HashSet;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError, Weak};
use std::time::Duration;

use eukhe_chord::json::JsonValue;
use indexmap::IndexMap;
use tokio::sync::{mpsc as async_mpsc, oneshot, Notify};

use self::vm::{run_vm, VmCommand, VmData, VmDelivery, VmDone, VmDoneOutcome, VmMessage};
use super::identifier::to_codemode_identifier;
use super::types::{
    CodemodeDeclaredGlobal, CodemodeDeclaredTool, CodemodeDuring, CodemodeEnding, CodemodeError,
    CodemodeErrorKind, CodemodeHostCall, CodemodeOutcome, CodemodeOutputItem, CodemodeResult,
    CodemodeStoreWrites,
};

/// The engine the VM runs, part of the fingerprint. Kept in step with
/// `Cargo.lock` by a test.
const ENGINE: &str = "rquickjs 0.14.0";

/// Bumped whenever the VM glue changes what a deterministic script observes
/// beyond what the fingerprint's other parts (engine, glue hash, limits)
/// capture.
const DETERMINISTIC_VERSION: u32 = 1;

/// `QuickJS`'s own stack limit; deep recursion throws a catchable
/// `RangeError` well before the thread's stack overflows.
const MAX_STACK_BYTES: usize = 1024 * 1024;

/// Stack of the VM thread: room for `QuickJS`'s limit plus the host frames.
const VM_THREAD_STACK_BYTES: usize = 8 * 1024 * 1024;

/// Names scripts own; globals may not shadow them.
const RESERVED_GLOBALS: [&str; 9] = [
    "tools",
    "ALL_TOOLS",
    "console",
    "text",
    "image",
    "exit",
    "globalThis",
    "store",
    "load",
];

/// Options of a [`CodemodeSandbox`].
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct CodemodeSandboxOptions {
    /// Memory the VM may allocate; beyond it allocations fail inside the
    /// script as `InternalError: out of memory`. `None`: no limit.
    pub memory_limit_bytes: Option<usize>,
}

/// Runs code mode scripts, each in its own VM (pi-codemode
/// `CodemodeSandboxBase`). Clones share the sandbox; [`close`](Self::close)
/// aborts every running script and refuses new ones.
#[derive(Clone)]
pub struct CodemodeSandbox {
    inner: Arc<SandboxInner>,
}

struct SandboxInner {
    options: CodemodeSandboxOptions,
    fingerprint: String,
    closed: AtomicBool,
    running: Mutex<Vec<Weak<RunControl>>>,
}

impl std::fmt::Debug for CodemodeSandbox {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("CodemodeSandbox")
            .field("options", &self.inner.options)
            .field("fingerprint", &self.inner.fingerprint)
            .finish_non_exhaustive()
    }
}

/// What a run starts with (pi-codemode `CodemodeRunOptions`).
#[derive(Debug, Clone, PartialEq)]
pub struct CodemodeRunOptions {
    /// The VM clock's start, in ms since the epoch.
    pub started_at: f64,
    /// Seeds `Math.random()`.
    pub seed: u32,
    pub tools: Vec<CodemodeDeclaredTool>,
    pub globals: Vec<CodemodeDeclaredGlobal>,
    /// Values the script reads with `load(key)`.
    pub store: IndexMap<String, JsonValue>,
    /// Deadline of this run; `None`: none.
    pub timeout_ms: Option<f64>,
}

/// Why a run could not start.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum CodemodeStartError {
    #[error("Sandbox is closed")]
    Closed,
    #[error("startedAt must be a non-negative number of milliseconds since the epoch")]
    StartedAt,
    #[error("Tool names must be unique")]
    DuplicateTool,
    #[error("Tool script names must be unique")]
    DuplicateScriptName,
    #[error("Invalid global name \"{0}\"")]
    InvalidGlobal(String),
    #[error("Global \"{0}\" is already registered")]
    DuplicateGlobal(String),
    #[error("Global \"{0}\" conflicts with the namespace \"{0}\"")]
    GlobalNamespace(String),
    #[error("The sandbox thread could not start: {0}")]
    Thread(String),
}

/// Why a result could not be delivered (pi-codemode `CodemodeRun.deliver()`
/// throws).
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum CodemodeDeliverError {
    #[error("The clock value of result {0} is not a finite number")]
    Clock(u64),
    #[error("Result number {0} is not a positive integer used once")]
    Seq(u64),
    #[error("Call {0} is not waiting for a result")]
    NotWaiting(u64),
}

/// What a run reports, in order; `Finished` is last.
#[derive(Debug, Clone, PartialEq)]
pub enum CodemodeRunEvent {
    /// The VM's fingerprint, before the script runs and before any call.
    Started { fingerprint: String },
    /// The script made a call; answer it with [`CodemodeRunHandle::deliver`].
    Call(CodemodeHostCall),
    /// The VM processed result `seq` (0: the script's first run) and waits
    /// again, having issued `issued` calls in total.
    Idle { seq: u64, issued: u64 },
    /// The run has its outcome and its VM stopped.
    Finished(CodemodeResult),
}

/// A running script (pi-codemode `CodemodeRun`): its events and a handle.
pub struct CodemodeRun {
    events: async_mpsc::UnboundedReceiver<CodemodeRunEvent>,
    handle: CodemodeRunHandle,
}

impl CodemodeRun {
    /// The next event; `None` once `Finished` was taken.
    pub async fn next_event(&mut self) -> Option<CodemodeRunEvent> {
        self.events.recv().await
    }

    /// A handle to answer calls and abort the run.
    #[must_use]
    pub fn handle(&self) -> CodemodeRunHandle {
        self.handle.clone()
    }
}

/// Answers a run's calls and aborts it; clones share the run.
#[derive(Clone)]
pub struct CodemodeRunHandle {
    control: Arc<RunControl>,
}

struct RunControl {
    state: Mutex<RunState>,
    commands: Mutex<mpsc::Sender<VmCommand>>,
    stop: Arc<AtomicBool>,
    abort: Notify,
}

#[derive(Default)]
struct RunState {
    /// Whether the run has its outcome.
    finished: bool,
    /// Result numbers `deliver()` used.
    delivered: HashSet<u64>,
    /// Calls waiting for a result.
    pending: HashSet<u64>,
    /// The first abort's message.
    abort: Option<String>,
}

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

impl CodemodeRunHandle {
    /// Whether the run has its outcome: the script ended, timed out, or
    /// failed, or the run was aborted. Calls can no longer be answered.
    #[must_use]
    pub fn finished(&self) -> bool {
        lock(&self.control.state).finished
    }

    /// Answer call `id` as result number `seq`. Results are numbered 1, 2,
    /// ... without gaps, and the VM applies them strictly in that order,
    /// whatever order they arrive in. While it processes this one, its clock
    /// reads `now` (ms since the epoch), or the previous value if `now` is
    /// earlier. A finished run ignores deliveries.
    ///
    /// # Errors
    ///
    /// A call that is not waiting for an answer, a `seq` used before or 0,
    /// or a `now` that is not finite.
    pub fn deliver(
        &self,
        seq: u64,
        now: f64,
        id: u64,
        outcome: &CodemodeOutcome,
    ) -> Result<(), CodemodeDeliverError> {
        let mut state = lock(&self.control.state);
        if state.finished {
            return Ok(());
        }
        if !now.is_finite() {
            return Err(CodemodeDeliverError::Clock(seq));
        }
        if seq == 0 || state.delivered.contains(&seq) {
            return Err(CodemodeDeliverError::Seq(seq));
        }
        if !state.pending.contains(&id) {
            return Err(CodemodeDeliverError::NotWaiting(id));
        }
        let (ok, payload, properties) = match outcome {
            CodemodeOutcome::Ok { value } => (true, value.as_ref().map(ToString::to_string), None),
            CodemodeOutcome::Err {
                message,
                properties,
            } => (
                false,
                Some(message.clone()),
                properties
                    .as_ref()
                    .map(|properties| JsonValue::Object(Arc::new(properties.clone())).to_string()),
            ),
        };
        state.delivered.insert(seq);
        state.pending.remove(&id);
        drop(state);
        // A VM that already ended dropped its receiver; its outcome arrives
        // as an event.
        let _ = lock(&self.control.commands).send(VmCommand::Deliver(VmDelivery {
            seq,
            now,
            id,
            ok,
            payload,
            properties,
        }));
        Ok(())
    }

    /// End the run with an `aborted` error the script cannot catch; the
    /// first abort's message counts.
    pub fn abort(&self, message: impl Into<String>) {
        {
            let mut state = lock(&self.control.state);
            if state.finished || state.abort.is_some() {
                return;
            }
            state.abort = Some(message.into());
        }
        self.control.abort.notify_one();
    }
}

impl CodemodeSandbox {
    /// A sandbox with `options`.
    #[must_use]
    pub fn new(options: CodemodeSandboxOptions) -> Self {
        let fingerprint = format!(
            "{ENGINE}, glue {}, deterministic {DETERMINISTIC_VERSION}, stack {MAX_STACK_BYTES}, heap {}",
            fnv1a(&[vm::HOST_SOURCE, vm::PRELUDE_SOURCE]),
            options
                .memory_limit_bytes
                .map_or_else(|| "none".to_owned(), |limit| limit.to_string()),
        );
        Self {
            inner: Arc::new(SandboxInner {
                options,
                fingerprint,
                closed: AtomicBool::new(false),
                running: Mutex::new(Vec::new()),
            }),
        }
    }

    /// The fingerprint every VM of this sandbox reports: what a replay must
    /// match.
    #[must_use]
    pub fn fingerprint(&self) -> &str {
        &self.inner.fingerprint
    }

    /// Run `code`, an async function body (`return` and top-level `await`
    /// work), deterministically, with the caller answering its calls. Never
    /// fails for script failures; those end the run with an error result.
    /// Must be called within a Tokio runtime.
    ///
    /// # Errors
    ///
    /// The sandbox is closed, the options are invalid, or the VM thread
    /// cannot be spawned.
    #[expect(
        clippy::needless_pass_by_value,
        reason = "mirrors upstream `start(code, options)`: a run owns its options"
    )]
    pub fn start(
        &self,
        code: &str,
        options: CodemodeRunOptions,
    ) -> Result<CodemodeRun, CodemodeStartError> {
        if self.inner.closed.load(Ordering::SeqCst) {
            return Err(CodemodeStartError::Closed);
        }
        if !options.started_at.is_finite() || options.started_at < 0.0 {
            return Err(CodemodeStartError::StartedAt);
        }
        let names: HashSet<&str> = options
            .tools
            .iter()
            .map(|tool| tool.name.as_str())
            .collect();
        if names.len() != options.tools.len() {
            return Err(CodemodeStartError::DuplicateTool);
        }
        let script_names: HashSet<&str> = options
            .tools
            .iter()
            .map(|tool| tool.js_name.as_str())
            .collect();
        if script_names.len() != options.tools.len() {
            return Err(CodemodeStartError::DuplicateScriptName);
        }
        check_globals(&options.globals)?;
        let data = VmData {
            code: code.to_owned(),
            tools_json: tools_json(&options.tools),
            globals_json: globals_json(&options.globals),
            store_json: store_json(&options.store),
            memory_limit_bytes: self.inner.options.memory_limit_bytes,
            max_stack_bytes: MAX_STACK_BYTES,
            started_at: options.started_at,
            seed: options.seed,
            fingerprint: self.inner.fingerprint.clone(),
        };
        let (post, messages) = async_mpsc::unbounded_channel();
        let (commands, received) = mpsc::channel();
        let stop = Arc::new(AtomicBool::new(false));
        let (stopped, vm_stopped) = oneshot::channel::<()>();
        let vm_stop = Arc::clone(&stop);
        std::thread::Builder::new()
            .name("codemode-vm".to_owned())
            .stack_size(VM_THREAD_STACK_BYTES)
            .spawn(move || {
                run_vm(data, &post, &received, &vm_stop);
                drop(stopped);
            })
            .map_err(|error| CodemodeStartError::Thread(error.to_string()))?;
        let control = Arc::new(RunControl {
            state: Mutex::new(RunState::default()),
            commands: Mutex::new(commands),
            stop,
            abort: Notify::new(),
        });
        {
            let mut running = lock(&self.inner.running);
            running.retain(|run| run.strong_count() > 0);
            running.push(Arc::downgrade(&control));
        }
        let (events, event_receiver) = async_mpsc::unbounded_channel();
        let execution = Execution {
            control: Arc::clone(&control),
            events,
            output: Vec::new(),
        };
        tokio::spawn(execution.run(messages, vm_stopped, options.timeout_ms));
        Ok(CodemodeRun {
            events: event_receiver,
            handle: CodemodeRunHandle { control },
        })
    }

    /// Abort every running script (they end `aborted`: "Sandbox closed") and
    /// refuse new ones.
    pub fn close(&self) {
        self.inner.closed.store(true, Ordering::SeqCst);
        let running: Vec<Arc<RunControl>> = lock(&self.inner.running)
            .drain(..)
            .filter_map(|run| run.upgrade())
            .collect();
        for control in running {
            CodemodeRunHandle { control }.abort("Sandbox closed");
        }
    }
}

/// FNV-1a over the UTF-16 code units of `parts`, as 8 hex digits: identifies
/// the VM glue in the fingerprint.
fn fnv1a(parts: &[&str]) -> String {
    let mut hash: u32 = 0x811c_9dc5;
    for unit in parts.iter().flat_map(|part| part.encode_utf16()) {
        hash ^= u32::from(unit);
        hash = hash.wrapping_mul(0x0100_0193);
    }
    format!("{hash:08x}")
}

fn is_identifier(text: &str) -> bool {
    let mut chars = text.chars();
    chars
        .next()
        .is_some_and(|first| first.is_ascii_alphabetic() || first == '_' || first == '$')
        && chars.all(|char| char.is_ascii_alphanumeric() || char == '_' || char == '$')
}

/// Global names: identifiers or `namespace.member`, not shadowing a built-in
/// global or each other.
fn check_globals(globals: &[CodemodeDeclaredGlobal]) -> Result<(), CodemodeStartError> {
    let mut names = HashSet::new();
    let mut namespaces = Vec::new();
    for global in globals {
        let parts: Vec<&str> = global.name.split('.').collect();
        if parts.len() > 2
            || !parts.iter().all(|part| is_identifier(part))
            || RESERVED_GLOBALS.contains(&parts[0])
        {
            return Err(CodemodeStartError::InvalidGlobal(global.name.clone()));
        }
        if !names.insert(global.name.as_str()) {
            return Err(CodemodeStartError::DuplicateGlobal(global.name.clone()));
        }
        if parts.len() == 2 {
            namespaces.push(parts[0]);
        }
    }
    match namespaces.into_iter().find(|name| names.contains(name)) {
        Some(name) => Err(CodemodeStartError::GlobalNamespace(name.to_owned())),
        None => Ok(()),
    }
}

fn tools_json(tools: &[CodemodeDeclaredTool]) -> String {
    let items: Vec<serde_json::Value> = tools
        .iter()
        .map(|tool| {
            let js_name = if tool.js_name.is_empty() {
                to_codemode_identifier(&tool.name)
            } else {
                tool.js_name.clone()
            };
            serde_json::json!({ "name": tool.name, "jsName": js_name, "description": tool.description })
        })
        .collect();
    serde_json::Value::Array(items).to_string()
}

fn globals_json(globals: &[CodemodeDeclaredGlobal]) -> String {
    let items: Vec<serde_json::Value> = globals
        .iter()
        .map(|global| serde_json::json!({ "name": global.name, "spread": global.spread }))
        .collect();
    serde_json::Value::Array(items).to_string()
}

/// `{ key: <JSON text of the value> }`, as the prelude reads its store.
fn store_json(store: &IndexMap<String, JsonValue>) -> String {
    let mut object = serde_json::Map::new();
    for (key, value) in store {
        object.insert(key.clone(), serde_json::Value::String(value.to_string()));
    }
    serde_json::Value::Object(object).to_string()
}

/// A payload the VM sent that does not decode. The prelude runs in the same
/// VM as the script, so a script that patches built-ins could make it send
/// malformed data; the run then fails as a sandbox error.
struct BridgeError(String);

fn parse_bridge_json(json: &str, what: &str) -> Result<JsonValue, BridgeError> {
    JsonValue::parse(json).map_err(|_| BridgeError(format!("{what} is not valid JSON")))
}

fn parse_store_writes(json: &str) -> Result<CodemodeStoreWrites, BridgeError> {
    let entries = parse_bridge_json(json, "store writes")?;
    let entries = entries
        .as_array()
        .ok_or_else(|| BridgeError("store writes are not an array".to_owned()))?;
    let mut writes = CodemodeStoreWrites::default();
    for entry in entries {
        let malformed = || BridgeError("store writes contain a malformed entry".to_owned());
        let items = entry.as_array().ok_or_else(malformed)?;
        match items {
            [key] => writes
                .delete
                .push(key.as_str().ok_or_else(malformed)?.to_owned()),
            [key, value] => {
                let key = key.as_str().ok_or_else(malformed)?;
                let value = value.as_str().ok_or_else(malformed)?;
                let parsed = parse_bridge_json(value, &format!("store value for {key:?}"))?;
                writes.set.insert(key.to_owned(), parsed);
            }
            _ => return Err(malformed()),
        }
    }
    Ok(writes)
}

fn parse_script_error(json: &str) -> Result<CodemodeError, BridgeError> {
    let parsed = parse_bridge_json(json, "script error")?;
    let object = parsed
        .as_object()
        .ok_or_else(|| BridgeError("script error is not an object".to_owned()))?;
    let malformed = || BridgeError("script error is malformed".to_owned());
    let optional = |key: &str| -> Result<Option<String>, BridgeError> {
        match object.get(key) {
            None => Ok(None),
            Some(value) => value
                .as_str()
                .map(|text| Some(text.to_owned()))
                .ok_or_else(malformed),
        }
    };
    let message = object
        .get("message")
        .and_then(JsonValue::as_str)
        .ok_or_else(malformed)?
        .to_owned();
    Ok(CodemodeError {
        kind: CodemodeErrorKind::Script,
        name: optional("name")?,
        message,
        stack: optional("stack")?,
    })
}

fn sandbox_error(message: String) -> CodemodeError {
    CodemodeError {
        kind: CodemodeErrorKind::Sandbox,
        name: None,
        message,
        stack: None,
    }
}

fn bridge_failure(error: &BridgeError) -> CodemodeError {
    sandbox_error(format!(
        "Sandbox bridge broken: {}. The script may have modified built-ins such as a prototype's toJSON.",
        error.0
    ))
}

/// The host side of one run.
struct Execution {
    control: Arc<RunControl>,
    events: async_mpsc::UnboundedSender<CodemodeRunEvent>,
    output: Vec<CodemodeOutputItem>,
}

/// How the run ended, before its result is assembled.
enum Finish {
    Failed(CodemodeError, Option<CodemodeDuring>),
    Completed(
        Option<JsonValue>,
        CodemodeStoreWrites,
        Option<CodemodeDuring>,
    ),
}

impl Execution {
    async fn run(
        mut self,
        mut messages: async_mpsc::UnboundedReceiver<VmMessage>,
        vm_stopped: oneshot::Receiver<()>,
        timeout_ms: Option<f64>,
    ) {
        let deadline = timeout_ms.map(|ms| {
            // An unrepresentable deadline is none.
            tokio::time::Instant::now().checked_add(Duration::from_secs_f64(ms.max(0.0) / 1000.0))
        });
        let finish = loop {
            let timer = async {
                match deadline {
                    Some(Some(at)) => tokio::time::sleep_until(at).await,
                    Some(None) | None => std::future::pending::<()>().await,
                }
            };
            tokio::select! {
                message = messages.recv() => match message {
                    Some(message) => {
                        if let Some(finish) = self.receive(message) {
                            break finish;
                        }
                    }
                    None => break Finish::Failed(
                        sandbox_error("The sandbox VM stopped without a result".to_owned()),
                        None,
                    ),
                },
                () = timer => break Finish::Failed(
                    CodemodeError {
                        kind: CodemodeErrorKind::Timeout,
                        name: None,
                        message: format!(
                            "Execution timed out after {} ms",
                            JsonValue::try_from(timeout_ms.unwrap_or_default())
                                .map_or_else(|_| "?".to_owned(), |value| value.to_string())
                        ),
                        stack: None,
                    },
                    None,
                ),
                () = self.control.abort.notified() => {
                    let message = lock(&self.control.state)
                        .abort
                        .clone()
                        .unwrap_or_else(|| "Execution aborted".to_owned());
                    break Finish::Failed(
                        CodemodeError { kind: CodemodeErrorKind::Aborted, name: None, message, stack: None },
                        None,
                    );
                }
            }
        };
        {
            let mut state = lock(&self.control.state);
            state.finished = true;
            state.pending.clear();
        }
        self.control.stop.store(true, Ordering::SeqCst);
        let _ = lock(&self.control.commands).send(VmCommand::Stop);
        // The thread ends after disposing the VM, dropping its sender.
        let _ = vm_stopped.await;
        let (ending, during) = match finish {
            Finish::Failed(error, during) => (CodemodeEnding::Failed(error), during),
            Finish::Completed(value, store_writes, during) => (
                CodemodeEnding::Completed {
                    value,
                    store_writes,
                },
                during,
            ),
        };
        let _ = self.events.send(CodemodeRunEvent::Finished(CodemodeResult {
            ending,
            output: self.output,
            during,
        }));
    }

    /// Handle one VM message; `Some` when it ends the run.
    fn receive(&mut self, message: VmMessage) -> Option<Finish> {
        match message {
            VmMessage::Started { fingerprint } => {
                let _ = self.events.send(CodemodeRunEvent::Started { fingerprint });
                None
            }
            VmMessage::Output(item) => {
                self.output.push(item);
                None
            }
            VmMessage::Call {
                id,
                target,
                name,
                args,
            } => {
                let args = match args {
                    None => None,
                    Some(json) => match parse_bridge_json(&json, "call arguments") {
                        Ok(value) => Some(value),
                        Err(error) => return Some(Finish::Failed(bridge_failure(&error), None)),
                    },
                };
                if !lock(&self.control.state).pending.insert(id) {
                    return Some(Finish::Failed(
                        bridge_failure(&BridgeError(format!("duplicate call id {id}"))),
                        None,
                    ));
                }
                let _ = self.events.send(CodemodeRunEvent::Call(CodemodeHostCall {
                    id,
                    target,
                    name,
                    args,
                }));
                None
            }
            VmMessage::Idle { seq, issued } => {
                let _ = self.events.send(CodemodeRunEvent::Idle { seq, issued });
                None
            }
            VmMessage::Done(VmDone { outcome, during }) => {
                let during = during.map(|(seq, issued)| CodemodeDuring { seq, issued });
                Some(match outcome {
                    VmDoneOutcome::Failed { error } => match parse_script_error(&error) {
                        Ok(error) => Finish::Failed(error, during),
                        Err(error) => Finish::Failed(bridge_failure(&error), during),
                    },
                    VmDoneOutcome::Completed { value, writes } => {
                        let value = match value
                            .map(|json| parse_bridge_json(&json, "return value"))
                            .transpose()
                        {
                            Ok(value) => value,
                            Err(error) => {
                                return Some(Finish::Failed(bridge_failure(&error), during))
                            }
                        };
                        match parse_store_writes(&writes) {
                            Ok(writes) => Finish::Completed(value, writes, during),
                            Err(error) => Finish::Failed(bridge_failure(&error), during),
                        }
                    }
                })
            }
            VmMessage::Crash { message } => Some(Finish::Failed(sandbox_error(message), None)),
        }
    }
}

#[cfg(test)]
mod tests;
