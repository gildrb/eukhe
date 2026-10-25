//! One execution of the code mode tool (pi-durable `codemode.ts`
//! `CodemodeCall`): a first run, or a rerun after a restart that replays the
//! journal.
//!
//! The call is one loop over the run's events and the call's own work
//! (commits, nested calls, globals), so its state needs no locks. Each
//! result's acknowledged call count is recorded with the next journal
//! commit, or at once when the VM has processed everything delivered: a
//! script waiting on a long call is where a restart usually finds it.
//!
//! A call is launched only once the count of calls issued in the drain that
//! made it is committed. So every key an earlier attempt admitted is at most
//! its last recorded count; a replay checks every recorded count, so when it
//! releases its calls it has made every call an earlier attempt could have
//! admitted, and later calls are new.

use std::collections::{BTreeMap, HashMap};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use eukhe_chord::context::{AbortSignal, Context};
use eukhe_chord::json::{from_json, to_json, JsonValue};
use eukhe_types::pi_ai::{JsonObject as PiJsonObject, TextContent, UserContentBlock};
use futures::future::BoxFuture;
use futures::stream::FuturesUnordered;
use futures::{FutureExt, StreamExt};
use tokio::sync::{OnceCell, Semaphore};

use super::discover::discover;
use super::docs::{
    CodemodeJournal, CodemodeRunState, CodemodeStart, CodemodeStore, JournalEntry, JournalGlobal,
    StartNamespace, StartTool, CODEMODE_JOURNAL_DOC, CODEMODE_RUN_DOC, CODEMODE_STORE_DOC,
};
use super::identifier::to_codemode_identifier;
use super::models::{
    catalog_call, model_call_tool, CATALOG_GLOBALS, CODEMODE_INTERNAL_PREFIX, GENERATE_IMAGES_TOOL,
    MAX_CONCURRENT_MODEL_CALLS, MODEL_CALL_GLOBALS,
};
use super::output::{format_result, FormatOptions, OutputFiles, DEFAULT_MAX_OUTPUT_TOKENS};
use super::sandbox::{CodemodeRun, CodemodeRunEvent, CodemodeRunHandle, CodemodeRunOptions};
use super::source::parse_codemode_source;
use super::tool::{CodemodeToolOptions, CODEMODE_MODULE_VERSION, OUTPUT_LIMITS};
use super::types::{
    CodemodeCallStatus, CodemodeCallTarget, CodemodeDeclaredGlobal, CodemodeDeclaredTool,
    CodemodeEnding, CodemodeErrorKind, CodemodeHostCall, CodemodeNestedCall, CodemodeOutcome,
    CodemodeResult, CodemodeToolDetails,
};
use super::{describe, CodemodeModels};
use crate::env::ExecutionEnv;
use crate::harness::tool::{nested_call_task, ToolTaskInput};
use crate::harness::types::{
    ExecuteToolOptions, NestedToolExecutionResult, ToolDiagnosticSeverity, ToolExecutionApi,
    ToolExecutionApiExt, ToolExecutionResult,
};
use crate::session::{SessionError, SessionResult};

const ARGS_PREVIEW_CHARS: usize = 200;
const ERROR_PREVIEW_CHARS: usize = 500;

/// Globals for finding tools, answered from the start data, so a replay
/// sees what the first run saw.
pub(super) const DISCOVERY_GLOBALS: [&str; 3] =
    ["searchTools", "describeTool", "describeNamespace"];

/// `text` cut to `max` UTF-16 code units for display, ending in `...`.
fn cut(text: &str, max: usize) -> String {
    if text.encode_utf16().count() <= max {
        return text.to_owned();
    }
    let mut units = 0;
    let mut end = 0;
    for (index, char) in text.char_indices() {
        units += char.len_utf16();
        if units > max - 3 {
            break;
        }
        end = index + char.len_utf8();
    }
    format!("{}...", &text[..end])
}

fn error_result(message: String) -> ToolExecutionResult {
    ToolExecutionResult {
        output: Some(vec![UserContentBlock::Text(TextContent::new(message))]),
        is_error: Some(true),
        ..ToolExecutionResult::default()
    }
}

fn now_ms() -> f64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0.0, |elapsed| elapsed.as_secs_f64() * 1000.0)
        .floor()
}

/// `JSON.stringify(value) ?? ""`.
fn json_text(value: Option<&JsonValue>) -> String {
    value.map(ToString::to_string).unwrap_or_default()
}

fn describe_call(call: &CodemodeHostCall) -> String {
    let prefix = match call.target {
        CodemodeCallTarget::Tool => "tools.",
        CodemodeCallTarget::Global => "",
    };
    format!("{prefix}{}({})", call.name, json_text(call.args.as_ref()))
}

/// The text of a schema-less tool's collapsed output: a string, or an array
/// of text and image blocks.
fn text_of(value: Option<&JsonValue>) -> String {
    match value {
        Some(JsonValue::String(text)) => text.to_string(),
        Some(JsonValue::Array(items)) => items
            .iter()
            .filter(|item| item.get("type").and_then(JsonValue::as_str) == Some("text"))
            .filter_map(|item| item.get("text").and_then(JsonValue::as_str))
            .collect::<Vec<_>>()
            .join("\n"),
        Some(_) | None => String::new(),
    }
}

/// What a script gets for a nested call. A tool with a schema resolves with
/// its value, also on an error result that carries one (`bash`'s `{ output,
/// exitCode }` for a nonzero exit); a schema-less tool resolves with its text
/// output. Any other error rejects, with its text: a schema-less tool's
/// output, else its error diagnostics.
fn outcome_of(name: &str, structured: bool, result: &NestedToolExecutionResult) -> CodemodeOutcome {
    let value = if structured {
        result.structured_output.clone()
    } else {
        Some(JsonValue::from(text_of(result.structured_output.as_ref())))
    };
    if !result.is_error || (structured && value.is_some()) {
        return CodemodeOutcome::Ok { value };
    }
    let message = if structured {
        String::new()
    } else {
        text_of(value.as_ref())
    };
    let diagnostics = error_diagnostics(result);
    let message = [message, diagnostics]
        .into_iter()
        .find(|text| !text.is_empty())
        .unwrap_or_else(|| format!("Tool {name} failed"));
    CodemodeOutcome::Err {
        message,
        properties: value.map(|value| std::iter::once(("structuredOutput", value)).collect()),
    }
}

fn error_diagnostics(result: &NestedToolExecutionResult) -> String {
    result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == ToolDiagnosticSeverity::Error)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>()
        .join("\n")
}

/// Images in a `models.generateImages()` result.
fn count_images(value: Option<&JsonValue>) -> u64 {
    value
        .and_then(|value| value.get("output"))
        .and_then(JsonValue::as_array)
        .map_or(0, |items| {
            items
                .iter()
                .filter(|item| item.get("type").and_then(JsonValue::as_str) == Some("image"))
                .count() as u64
        })
}

/// A script's call of `models.classify()` or `models.generateImages()` as the
/// call of its internal tool.
fn as_tool_call(call: CodemodeHostCall) -> CodemodeHostCall {
    let tool = match call.target {
        CodemodeCallTarget::Global => model_call_tool(&call.name),
        CodemodeCallTarget::Tool => None,
    };
    let Some(tool) = tool else {
        return call;
    };
    let argument = |index: usize| {
        call.args
            .as_ref()
            .and_then(|args| args.get_index(index))
            .cloned()
            .unwrap_or(JsonValue::Null)
    };
    let args: eukhe_chord::json::JsonObject = [("model", argument(0)), ("context", argument(1))]
        .into_iter()
        .collect();
    CodemodeHostCall {
        id: call.id,
        target: CodemodeCallTarget::Tool,
        name: tool.to_owned(),
        args: Some(JsonValue::Object(Arc::new(args))),
    }
}

/// Structural JSON equality of two script values; `undefined` equals only
/// itself.
fn same_json(a: Option<&JsonValue>, b: Option<&JsonValue>) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(a), Some(b)) => a == b,
        (Some(_), None) | (None, Some(_)) => false,
    }
}

/// What the call learned from finishing a tool call.
struct ToolDone {
    outcome: CodemodeOutcome,
    result: Option<NestedToolExecutionResult>,
}

/// A finished live call waiting for its journal commit.
struct Finished {
    id: u64,
    at: f64,
    outcome: CodemodeOutcome,
    global: Option<JournalGlobal>,
}

/// The call's own work in flight.
enum Work {
    /// The fingerprint of the first run is committed.
    Fingerprint(SessionResult<()>),
    /// An outcome the call decided is stored; then the VM stops with
    /// `abort`.
    Decided {
        result: SessionResult<()>,
        abort: String,
    },
    /// A replayed tool call reattached and got its result.
    Replayed {
        call: CodemodeHostCall,
        done: SessionResult<ToolDone>,
    },
    /// A live call finished.
    Launched {
        call: CodemodeHostCall,
        at: f64,
        done: SessionResult<(CodemodeOutcome, Option<NestedToolExecutionResult>)>,
    },
    /// The held calls were checked against an earlier attempt's keys: the
    /// other call made under a key, when it is another one.
    Released {
        calls: Vec<CodemodeHostCall>,
        checked: SessionResult<Option<(u64, String)>>,
    },
    /// A journal commit of finished calls and acknowledged counts.
    Pumped {
        batch: Vec<Finished>,
        acks: Vec<(u64, u64)>,
        result: SessionResult<()>,
    },
}

/// What waits for the fingerprint check.
enum Gated {
    DeliverReplayed,
    CallReplayed(CodemodeHostCall),
    Release,
}

/// What the start commit found.
enum Found {
    Done(ToolExecutionResult),
    Start {
        start: CodemodeStart,
        journal: CodemodeJournal,
        rerun: bool,
    },
}

/// Execute the code mode tool with `source`: the whole call.
#[expect(
    clippy::too_many_lines,
    reason = "one ported upstream routine: build the start record, then find or commit it"
)]
pub(super) async fn execute(
    options: Arc<CodemodeToolOptions>,
    api: Arc<dyn ToolExecutionApi>,
    cx: Context,
    source: &str,
) -> SessionResult<ToolExecutionResult> {
    let parsed = parse_codemode_source(source).map_err(|error| SessionError::error(error.0))?;
    let agent = api.agent(&cx).await?;
    let tools: Vec<StartTool> = agent
        .callable
        .iter()
        .map(|tool| StartTool {
            name: tool.name.clone(),
            js_name: to_codemode_identifier(&tool.name),
            description: describe::sample_of(tool),
            structured: tool.structured_output_schema.is_some(),
            hidden: tool.name.starts_with(CODEMODE_INTERNAL_PREFIX),
        })
        .collect();
    let listed: Vec<&str> = agent
        .callable
        .iter()
        .map(|tool| tool.name.as_str())
        .filter(|name| !name.starts_with(CODEMODE_INTERNAL_PREFIX))
        .collect();
    let mut namespaces: Vec<StartNamespace> = Vec::new();
    for (name, namespace) in listed
        .iter()
        .zip(describe::namespaces_of(&listed, &options.namespaces))
    {
        let Some(namespace) = namespace else {
            continue;
        };
        match namespaces
            .iter_mut()
            .find(|entry| entry.name == namespace.name)
        {
            Some(entry) => entry.tools.push((*name).to_owned()),
            None => namespaces.push(StartNamespace {
                name: namespace.name.clone(),
                description: namespace.description.clone(),
                instructions: namespace.instructions.clone(),
                tools: vec![(*name).to_owned()],
            }),
        }
    }
    let models: Vec<&str> = match options.models {
        CodemodeModels::Included => CATALOG_GLOBALS
            .iter()
            .chain(MODEL_CALL_GLOBALS.iter())
            .copied()
            .collect(),
        CodemodeModels::Excluded => Vec::new(),
    };
    let globals: Vec<CodemodeDeclaredGlobal> = DISCOVERY_GLOBALS
        .iter()
        .chain(models.iter())
        .map(|name| CodemodeDeclaredGlobal {
            name: (*name).to_owned(),
            spread: true,
        })
        .chain(options.globals.iter().map(|global| CodemodeDeclaredGlobal {
            name: global.name.clone(),
            spread: global.spread,
        }))
        .collect();
    let now = now_ms();
    #[expect(
        clippy::cast_possible_truncation,
        reason = "the seed is the low 32 random bits of a v4 UUID"
    )]
    let seed = uuid::Uuid::new_v4().as_u128() as u32;
    let task_id = api.task_id();
    let conversation_id = api.conversation_id();
    let max_output_tokens = parsed
        .options
        .max_output_tokens
        .unwrap_or(DEFAULT_MAX_OUTPUT_TOKENS);
    #[expect(clippy::cast_precision_loss, reason = "timeouts are at most 2^31 ms")]
    let deadline = parsed
        .options
        .timeout_ms
        .map(|timeout| now + timeout as f64);
    let found = api
        .commit(
            move |tx| async move {
                let run = tx.doc(&CODEMODE_RUN_DOC, task_id).await?;
                let state: CodemodeRunState = from_json(&run.value()?)?;
                if let Some(result) = state.result {
                    return Ok(Found::Done(result));
                }
                let rerun = state.start.is_some();
                let start = if let Some(start) = state.start {
                    start
                } else {
                    let store = tx.doc(&CODEMODE_STORE_DOC, conversation_id).await?;
                    let store: CodemodeStore = from_json(&store.value()?)?;
                    let start = CodemodeStart {
                        version: CODEMODE_MODULE_VERSION,
                        started_at: now,
                        seed,
                        fingerprint: None,
                        deadline,
                        tools,
                        namespaces,
                        globals,
                        max_output_tokens,
                        store: store.values,
                    };
                    run.set("start", to_json(&start)?)?;
                    start
                };
                let journal = tx.doc(&CODEMODE_JOURNAL_DOC, task_id).await?;
                let journal: CodemodeJournal = from_json(&journal.value()?)?;
                Ok(Found::Start {
                    start,
                    journal,
                    rerun,
                })
            },
            &cx,
        )
        .await?;
    let (start, journal, rerun) = match found {
        Found::Done(result) => return Ok(result),
        Found::Start {
            start,
            journal,
            rerun,
        } => (start, journal, rerun),
    };
    let call = CodemodeCall::new(options, api, cx, start, journal, rerun);
    call.execute(&parsed.code).await
}

/// The state of one execution.
#[expect(
    clippy::struct_excessive_bools,
    reason = "the flags mirror upstream code mode's independent per-call state"
)]
struct CodemodeCall {
    options: Arc<CodemodeToolOptions>,
    api: Arc<dyn ToolExecutionApi>,
    cx: Context,
    start: Arc<CodemodeStart>,
    /// The journal as this attempt found it; replay delivers exactly these.
    replayed: Vec<JournalEntry>,
    /// Journal index of each replayed call ID.
    replay_index: HashMap<u64, usize>,
    /// Entries in the journal, replayed and live; the next delivery is
    /// `journal_length + 1`.
    journal_length: u64,
    /// Replayed entries delivered so far.
    next_replayed: usize,
    replaying: bool,
    /// Whether an earlier attempt ran this call: its nested call keys may
    /// already exist.
    rerun: bool,
    /// Whether live calls may launch; before, they are held.
    released: bool,
    /// The count an earlier attempt recorded after the script's first run.
    first_issued: Option<u64>,
    /// The highest issued count known to be committed: calls up to it may
    /// launch.
    durable_issued: u64,
    /// Live calls waiting for their issued count to be committed.
    waiting: Vec<CodemodeHostCall>,
    /// Calls the VM issued so far; its call IDs are 1, 2, ...
    issued: u64,
    /// Replay: results of journaled calls, ready to deliver in journal order.
    ready: HashMap<u64, CodemodeOutcome>,
    /// Replay: calls the journal does not have, admitted once replay is done.
    held: Vec<CodemodeHostCall>,
    /// Live: finished calls waiting for their journal commit.
    queue: Vec<Finished>,
    /// Acknowledged counts to record, by result number (0: the first run).
    acks: BTreeMap<u64, u64>,
    committing: bool,
    /// Set once the call decided an outcome other than the script's own
    /// (divergence, mismatch).
    ended: Option<ToolExecutionResult>,
    failure: Option<SessionError>,
    /// Whether this call aborted the run (TS `controller.signal.aborted`).
    aborted_run: bool,
    /// Set with `ended`, `failure`, and when the run finishes: what work in
    /// flight checks before a paid model call.
    stopped_flag: Arc<AtomicBool>,
    /// `models.classify()`/`generateImages()` calls in flight.
    model_slots: Arc<Semaphore>,
    /// Images `models.generateImages()` returned.
    generated_images: u64,
    /// The script's tool calls for `details`, by VM call ID.
    rows: BTreeMap<u64, CodemodeNestedCall>,
    /// Whether the VM's fingerprint is checked or recorded; nothing is
    /// delivered or admitted before.
    gate_open: bool,
    gated: Vec<Gated>,
    run: Option<CodemodeRunHandle>,
    commits: FuturesUnordered<BoxFuture<'static, Work>>,
    calls: FuturesUnordered<BoxFuture<'static, Work>>,
}

impl CodemodeCall {
    fn new(
        options: Arc<CodemodeToolOptions>,
        api: Arc<dyn ToolExecutionApi>,
        cx: Context,
        start: CodemodeStart,
        journal: CodemodeJournal,
        rerun: bool,
    ) -> Self {
        let replay_index = journal
            .entries
            .iter()
            .enumerate()
            .map(|(index, entry)| (entry.id, index))
            .collect();
        let durable_issued = journal
            .entries
            .iter()
            .filter_map(|entry| entry.issued_after)
            .fold(journal.first_issued.unwrap_or(0), u64::max);
        Self {
            options,
            api,
            cx,
            start: Arc::new(start),
            replay_index,
            journal_length: journal.entries.len() as u64,
            next_replayed: 0,
            replaying: !journal.entries.is_empty(),
            rerun,
            released: false,
            first_issued: journal.first_issued,
            durable_issued,
            replayed: journal.entries,
            waiting: Vec::new(),
            issued: 0,
            ready: HashMap::new(),
            held: Vec::new(),
            queue: Vec::new(),
            acks: BTreeMap::new(),
            committing: false,
            ended: None,
            failure: None,
            aborted_run: false,
            stopped_flag: Arc::new(AtomicBool::new(false)),
            model_slots: Arc::new(Semaphore::new(MAX_CONCURRENT_MODEL_CALLS)),
            generated_images: 0,
            rows: BTreeMap::new(),
            gate_open: false,
            gated: Vec::new(),
            run: None,
            commits: FuturesUnordered::new(),
            calls: FuturesUnordered::new(),
        }
    }

    fn run(&self) -> &CodemodeRunHandle {
        self.run.as_ref().expect("the run started")
    }

    /// Whether nothing more may happen: the run has its outcome, or the call
    /// decided or failed.
    fn stopped(&self) -> bool {
        self.ended.is_some()
            || self.failure.is_some()
            || self.run.as_ref().is_some_and(CodemodeRunHandle::finished)
    }

    #[expect(
        clippy::too_many_lines,
        reason = "one ported upstream routine: the main event loop of a call"
    )]
    async fn execute(mut self, code: &str) -> SessionResult<ToolExecutionResult> {
        if self.start.version != CODEMODE_MODULE_VERSION {
            let message = format!(
                "The script cannot resume: it started under code mode version {}, this is {CODEMODE_MODULE_VERSION}.",
                self.start.version
            );
            return self.decide(error_result(message)).await;
        }
        let remaining = self.start.deadline.map(|deadline| deadline - now_ms());
        if remaining.is_some_and(|remaining| remaining <= 0.0) {
            return self
                .decide(error_result(
                    "Script timed out: its deadline passed while it was interrupted.".to_owned(),
                ))
                .await;
        }
        let options = CodemodeRunOptions {
            started_at: self.start.started_at,
            seed: self.start.seed,
            tools: self
                .start
                .tools
                .iter()
                .filter(|tool| !tool.hidden)
                .map(|tool| CodemodeDeclaredTool {
                    name: tool.name.clone(),
                    js_name: tool.js_name.clone(),
                    description: tool.description.clone(),
                })
                .collect(),
            globals: self.start.globals.clone(),
            store: self
                .start
                .store
                .as_object()
                .map(|values| {
                    values
                        .iter()
                        .map(|(key, value)| (key.to_string(), value.clone()))
                        .collect()
                })
                .unwrap_or_default(),
            timeout_ms: remaining,
        };
        let mut run = self
            .options
            .sandbox
            .start(code, options)
            .map_err(|error| SessionError::error(error.to_string()))?;
        self.run = Some(run.handle());
        let result = self.drive(&mut run).await;
        self.stopped_flag.store(true, Ordering::SeqCst);
        // Commits in flight finish before the outcome is decided; nested
        // calls left running are aborted by the Harness when this call
        // settles.
        self.calls = FuturesUnordered::new();
        while let Some(work) = self.commits.next().await {
            if let Work::Decided {
                result: Err(error), ..
            } = work
            {
                self.fail(error);
            }
        }
        let Some(result) = result else {
            return Err(SessionError::error(
                "The code mode sandbox ended without a result",
            ));
        };
        if let Some(failure) = self.failure.take() {
            return Err(failure);
        }
        if let Some(ended) = self.ended.take() {
            return Ok(ended);
        }
        if let Some(reason) = self.cx.abort_signal().and_then(|signal| signal.reason()) {
            return Err(SessionError::Aborted(reason));
        }
        // Aborted, but not by this call: the host closed the sandbox, for
        // example while shutting down before closing the Harness. That
        // decides nothing about the script: store nothing and end with this
        // invocation, so a later attempt replays it.
        if let CodemodeEnding::Failed(error) = &result.ending {
            if error.kind == CodemodeErrorKind::Aborted && !self.aborted_run {
                if let Some(signal) = self.cx.abort_signal() {
                    return Err(SessionError::Aborted(signal.cancelled().await));
                }
                return Err(SessionError::error(
                    "The code mode sandbox was closed while the script ran",
                ));
            }
        }
        // A replay that ends where the live run went on is a divergence.
        if let Some(during) = result.during.filter(|during| {
            self.rerun && usize::try_from(during.seq).is_ok_and(|seq| seq <= self.replayed.len())
        }) {
            let seq = usize::try_from(during.seq).unwrap_or(usize::MAX);
            let acknowledged = if seq == 0 {
                !self.replayed.is_empty() || self.first_issued.is_some()
            } else {
                self.replayed[seq - 1].issued_after.is_some()
            };
            let continued = acknowledged
                || self.replayed[seq..]
                    .iter()
                    .any(|entry| entry.id > during.issued);
            if continued {
                let message = format!(
                    "The script took a different path when resumed after a restart: it ended after result {}, where it went on before.",
                    during.seq
                );
                return self.decide(error_result(message)).await;
            }
        }
        self.complete(result).await
    }

    /// Process the run's events and the call's work until the run finishes.
    async fn drive(&mut self, run: &mut CodemodeRun) -> Option<CodemodeResult> {
        let mut abort = self
            .cx
            .abort_signal()
            .map(|signal| async move { signal.cancelled().await }.boxed());
        loop {
            tokio::select! {
                event = run.next_event() => match event? {
                    CodemodeRunEvent::Started { fingerprint } => self.on_started(fingerprint),
                    CodemodeRunEvent::Call(call) => self.on_call(call),
                    CodemodeRunEvent::Idle { seq, issued } => self.on_idle(seq, issued),
                    CodemodeRunEvent::Finished(result) => return Some(result),
                },
                Some(work) = self.commits.next(), if !self.commits.is_empty() => self.on_work(work),
                Some(work) = self.calls.next(), if !self.calls.is_empty() => self.on_work(work),
                reason = async { abort.as_mut().expect("guarded").await }, if abort.is_some() => {
                    abort = None;
                    self.abort_run(reason.to_string());
                }
            }
        }
    }

    fn abort_run(&mut self, message: String) {
        self.aborted_run = true;
        self.stopped_flag.store(true, Ordering::SeqCst);
        self.run().abort(message);
    }

    fn fail(&mut self, error: SessionError) {
        if self.failure.is_some() {
            return;
        }
        let message = error.to_string();
        self.failure = Some(error);
        if self.run.is_some() {
            self.abort_run(message);
        }
    }

    /// End the call with `message`: store it as the outcome, then stop the
    /// VM with an error the script cannot catch.
    fn diverge(&mut self, message: &str) {
        if self.ended.is_some() || self.failure.is_some() {
            return;
        }
        let result = self.with_details(error_result(format!(
            "The script took a different path when resumed after a restart: {message}"
        )));
        self.end(result, message.to_owned());
    }

    /// Decide `result` as the outcome: store it, then stop the VM with
    /// `abort`.
    fn end(&mut self, result: ToolExecutionResult, abort: String) {
        self.ended = Some(result.clone());
        self.stopped_flag.store(true, Ordering::SeqCst);
        let stored = self.store_decided(result);
        self.commits.push(
            async move {
                Work::Decided {
                    result: stored.await,
                    abort,
                }
            }
            .boxed(),
        );
    }

    fn with_details(&self, result: ToolExecutionResult) -> ToolExecutionResult {
        ToolExecutionResult {
            details: Some(to_json(&self.details()).unwrap_or_else(|_| JsonValue::object())),
            ..result
        }
    }

    /// Store a decided outcome unless one is stored.
    fn store_decided(&self, result: ToolExecutionResult) -> BoxFuture<'static, SessionResult<()>> {
        let task_id = self.api.task_id();
        self.api.commit(
            move |tx| async move {
                let run = tx.doc(&CODEMODE_RUN_DOC, task_id).await?;
                if run.get("result")?.is_none() {
                    run.set("result", to_json(&result)?)?;
                }
                Ok(())
            },
            &self.cx,
        )
    }

    /// Store an outcome the call decided before or without a VM; returns it.
    async fn decide(self, decided: ToolExecutionResult) -> SessionResult<ToolExecutionResult> {
        let result = self.with_details(decided);
        self.store_decided(result.clone()).await?;
        Ok(result)
    }

    fn on_work(&mut self, work: Work) {
        match work {
            Work::Fingerprint(result) => match result {
                Ok(()) => self.open_gate(),
                Err(error) => self.fail(error),
            },
            Work::Decided { result, abort } => {
                if let Err(error) = result {
                    self.fail(error);
                }
                if !self.aborted_run {
                    self.abort_run(abort);
                }
            }
            Work::Replayed { call, done } => match done {
                Ok(done) => {
                    self.finish_tool(call.id, &done);
                    self.ready.insert(call.id, done.outcome);
                    self.deliver_replayed();
                }
                Err(error) => self.call_failed(&call, error),
            },
            Work::Launched { call, at, done } => match done {
                Ok((outcome, result)) => {
                    let global = match call.target {
                        CodemodeCallTarget::Tool => {
                            self.finish_tool(
                                call.id,
                                &ToolDone {
                                    outcome: outcome.clone(),
                                    result,
                                },
                            );
                            None
                        }
                        CodemodeCallTarget::Global => Some(JournalGlobal {
                            name: call.name.clone(),
                            args: call.args.clone(),
                            outcome: outcome.clone(),
                        }),
                    };
                    self.queue.push(Finished {
                        id: call.id,
                        at,
                        outcome,
                        global,
                    });
                    self.pump();
                }
                Err(error) => self.call_failed(&call, error),
            },
            Work::Released { calls, checked } => match checked {
                Err(error) => self.fail(error),
                Ok(_) if self.stopped() => {}
                Ok(Some((id, other))) => {
                    let call = calls
                        .iter()
                        .find(|call| call.id == id)
                        .map_or_else(String::new, describe_call);
                    self.diverge(&format!("call {id} is {call}, but was {other}"));
                }
                Ok(None) => self.finish_release(calls),
            },
            Work::Pumped {
                batch,
                acks,
                result,
            } => {
                if let Err(error) = result {
                    self.fail(error);
                    return;
                }
                for (_, issued) in &acks {
                    self.durable_issued = self.durable_issued.max(*issued);
                }
                for item in batch {
                    self.journal_length += 1;
                    if !self.run().finished() {
                        let delivered = self.run().deliver(
                            self.journal_length,
                            item.at,
                            item.id,
                            &item.outcome,
                        );
                        if let Err(error) = delivered {
                            self.fail(SessionError::error(error.to_string()));
                            return;
                        }
                    }
                }
                self.launch_covered();
                self.committing = false;
                self.pump();
            }
        }
    }

    /// A call's work failed: an abort fails the call; anything else is a key
    /// an earlier attempt admitted with another tool or other arguments.
    fn call_failed(&mut self, call: &CodemodeHostCall, error: SessionError) {
        if self.stopped() {
            return;
        }
        if self.cx.aborted() {
            self.fail(error);
        } else {
            self.diverge(&format!(
                "call {} is {}: {error}",
                call.id,
                describe_call(call)
            ));
        }
    }

    fn on_started(&mut self, fingerprint: String) {
        match &self.start.fingerprint {
            Some(recorded) if *recorded != fingerprint => {
                let message = format!(
                    "The script cannot resume: the sandbox changed since it started ({recorded} -> {fingerprint})."
                );
                let result = self.with_details(error_result(message));
                self.end(result, "Sandbox fingerprint changed".to_owned());
            }
            Some(_) => self.open_gate(),
            None => {
                let task_id = self.api.task_id();
                let committed = self.api.commit(
                    move |tx| async move {
                        let run = tx.doc(&CODEMODE_RUN_DOC, task_id).await?;
                        if let Some(start) = run.get("start")? {
                            if let Some(start) = start.as_draft() {
                                start.set("fingerprint", fingerprint)?;
                            }
                        }
                        Ok(())
                    },
                    &self.cx,
                );
                self.commits
                    .push(async move { Work::Fingerprint(committed.await) }.boxed());
            }
        }
    }

    fn open_gate(&mut self) {
        self.gate_open = true;
        // Nothing was delivered before the gate: start now. A rerun without
        // a journal releases its calls at the script's first acknowledgment
        // instead.
        if self.replaying {
            self.deliver_replayed();
        } else if !self.rerun {
            self.release();
        }
        for action in std::mem::take(&mut self.gated) {
            self.perform(action);
        }
    }

    fn gate(&mut self, action: Gated) {
        if self.gate_open {
            self.perform(action);
        } else {
            self.gated.push(action);
        }
    }

    fn perform(&mut self, action: Gated) {
        match action {
            Gated::DeliverReplayed => self.deliver_replayed(),
            Gated::Release => self.release(),
            Gated::CallReplayed(call) => {
                let running = self.call_tool(&call);
                self.calls.push(
                    async move {
                        let done = running.await;
                        Work::Replayed { call, done }
                    }
                    .boxed(),
                );
            }
        }
    }

    fn on_call(&mut self, made: CodemodeHostCall) {
        if self.stopped() {
            return;
        }
        let call = as_tool_call(made);
        if call.target == CodemodeCallTarget::Tool {
            self.started_row(&call);
        }
        self.issued = self.issued.max(call.id);
        let index = if self.replaying {
            self.replay_index.get(&call.id).copied()
        } else {
            None
        };
        let Some(index) = index else {
            if self.released {
                self.waiting.push(call);
                self.launch_covered();
            } else {
                self.held.push(call);
            }
            return;
        };
        if let Some(global) = self.replayed[index].global.clone() {
            if call.target != CodemodeCallTarget::Global
                || call.name != global.name
                || !same_json(call.args.as_ref(), global.args.as_ref())
            {
                self.diverge(&format!(
                    "call {} is {}, but was a call to {}",
                    call.id,
                    describe_call(&call),
                    global.name
                ));
                return;
            }
            self.ready.insert(call.id, global.outcome);
            self.gate(Gated::DeliverReplayed);
            return;
        }
        if call.target != CodemodeCallTarget::Tool {
            self.diverge(&format!(
                "call {} is {}, but was a tool call",
                call.id,
                describe_call(&call)
            ));
            return;
        }
        self.gate(Gated::CallReplayed(call));
    }

    /// Replay: deliver journaled results in journal order, each once the VM
    /// has issued its call.
    fn deliver_replayed(&mut self) {
        while self.next_replayed < self.replayed.len() && !self.stopped() {
            let entry = &self.replayed[self.next_replayed];
            if entry.id > self.issued || !self.ready.contains_key(&entry.id) {
                return;
            }
            let (id, at) = (entry.id, entry.at);
            let Some(outcome) = self.ready.remove(&id) else {
                return;
            };
            self.next_replayed += 1;
            let seq = self.next_replayed as u64;
            if let Err(error) = self.run().deliver(seq, at, id, &outcome) {
                self.fail(SessionError::error(error.to_string()));
                return;
            }
        }
    }

    fn on_idle(&mut self, seq: u64, issued: u64) {
        if self.stopped() {
            return;
        }
        let replayed = self.replayed.len() as u64;
        // A count an earlier attempt recorded must match; a missing one is
        // recorded now.
        if self.rerun && seq <= replayed {
            let recorded = if seq == 0 {
                self.first_issued
            } else {
                self.replayed[usize::try_from(seq - 1).unwrap_or(usize::MAX)].issued_after
            };
            if let Some(recorded) = recorded.filter(|recorded| *recorded != issued) {
                let message = if seq == 0 {
                    format!("its first run made {issued} calls, where it had made {recorded}")
                } else {
                    format!("after result {seq} it had made {issued} calls, where it had made {recorded}")
                };
                self.diverge(&message);
                return;
            }
        }
        self.acks.insert(seq, issued);
        if !self.replaying {
            // A rerun without a journal: every call an earlier attempt could
            // have admitted is made by now.
            if seq == 0 && self.rerun {
                self.release();
            }
            // Committed at once when the script has processed everything
            // delivered; otherwise with the next commit.
            if seq == self.journal_length {
                self.pump();
            }
            return;
        }
        // Caught up: the VM processed everything delivered and waits.
        if seq != self.next_replayed as u64 {
            return;
        }
        if let Some(next) = self
            .replayed
            .get(usize::try_from(seq).unwrap_or(usize::MAX))
        {
            if next.id > issued {
                let message = format!(
                    "it waits without making call {}, which it made before",
                    next.id
                );
                self.diverge(&message);
            }
            return;
        }
        // The last replayed result is acknowledged: continue live, admitting
        // the calls the journal did not have once their count is committed.
        self.replaying = false;
        self.pump();
        self.release();
    }

    /// Let the held calls launch, and later live calls, each once its issued
    /// count is committed. On a rerun, an earlier attempt may have admitted
    /// some of them under their keys, as other calls: all held calls are
    /// checked first, and a divergence launches none.
    fn release(&mut self) {
        if !self.gate_open {
            self.gated.push(Gated::Release);
            return;
        }
        if self.stopped() || self.released {
            return;
        }
        let calls: Vec<CodemodeHostCall> = std::mem::take(&mut self.held);
        if !self.rerun {
            self.finish_release(calls);
            return;
        }
        let (api, cx) = (Arc::clone(&self.api), self.cx.clone());
        let keys: Vec<CodemodeHostCall> = calls.clone();
        self.commits.push(
            async move {
                let mut checked = Ok(None);
                for call in &keys {
                    match earlier(&api, call, &cx).await {
                        Ok(None) => {}
                        Ok(Some(other)) => {
                            checked = Ok(Some((call.id, other)));
                            break;
                        }
                        Err(error) => {
                            checked = Err(error);
                            break;
                        }
                    }
                }
                Work::Released { calls, checked }
            }
            .boxed(),
        );
    }

    fn finish_release(&mut self, calls: Vec<CodemodeHostCall>) {
        self.released = true;
        self.waiting.extend(calls);
        self.waiting.append(&mut self.held);
        self.launch_covered();
    }

    /// Launch the waiting calls whose issued count is committed.
    fn launch_covered(&mut self) {
        if !self.released || self.stopped() {
            return;
        }
        let durable = self.durable_issued;
        let (covered, waiting): (Vec<_>, Vec<_>) = std::mem::take(&mut self.waiting)
            .into_iter()
            .partition(|call| call.id <= durable);
        self.waiting = waiting;
        for call in covered {
            self.launch(call);
        }
    }

    /// Run one live call; its result is journaled when it finishes.
    fn launch(&mut self, call: CodemodeHostCall) {
        if self.stopped() {
            return;
        }
        let running: BoxFuture<
            'static,
            SessionResult<(CodemodeOutcome, Option<NestedToolExecutionResult>)>,
        > = match call.target {
            CodemodeCallTarget::Tool => {
                let tool = self.call_tool(&call);
                async move {
                    let done = tool.await?;
                    Ok((done.outcome, done.result))
                }
                .boxed()
            }
            CodemodeCallTarget::Global => {
                let global = self.call_global(&call);
                async move { Ok((global.await?, None)) }.boxed()
            }
        };
        self.calls.push(
            async move {
                let done = running.await;
                Work::Launched {
                    call,
                    at: now_ms(),
                    done,
                }
            }
            .boxed(),
        );
    }

    /// A nested call of the tool, keyed `c<id>`, and its outcome.
    fn call_tool(&self, call: &CodemodeHostCall) -> BoxFuture<'static, SessionResult<ToolDone>> {
        let name = call.name.clone();
        let structured = self
            .start
            .tools
            .iter()
            .any(|tool| tool.name == name && tool.structured);
        let args: Result<PiJsonObject, String> = match &call.args {
            None => Ok(PiJsonObject::new()),
            Some(JsonValue::Object(_)) => match serde_json::to_value(call.args.as_ref()) {
                Ok(serde_json::Value::Object(object)) => Ok(object),
                Ok(_) | Err(_) => Err(format!("Tool {name} arguments are not a JSON object")),
            },
            Some(_) => Err(format!("Tool {name} arguments must be an object")),
        };
        let model = name.starts_with(CODEMODE_INTERNAL_PREFIX);
        let (api, cx) = (Arc::clone(&self.api), self.cx.clone());
        let slots = Arc::clone(&self.model_slots);
        let stopped = Arc::clone(&self.stopped_flag);
        let run = self.run.clone();
        let key = format!("c{}", call.id);
        async move {
            let args = match args {
                Ok(args) => args,
                // Validation would reject arguments that are not an object;
                // nothing is called.
                Err(message) => {
                    return Ok(ToolDone {
                        outcome: CodemodeOutcome::Err {
                            message,
                            properties: None,
                        },
                        result: None,
                    });
                }
            };
            let _slot = if model {
                let permit = slots
                    .acquire_owned()
                    .await
                    .map_err(|error| SessionError::error(error.to_string()))?;
                // The call may have stopped while this one waited: a finished
                // script admits no new paid call.
                if stopped.load(Ordering::SeqCst)
                    || run.as_ref().is_some_and(CodemodeRunHandle::finished)
                {
                    return Err(SessionError::error("The script has ended"));
                }
                Some(permit)
            } else {
                None
            };
            let options = ExecuteToolOptions {
                key: Some(key),
                progress: None,
            };
            let result = api.execute_tool(&name, args, &cx, options).await?;
            Ok(ToolDone {
                outcome: outcome_of(&name, structured, &result),
                result: Some(result),
            })
        }
        .boxed()
    }

    /// A global's outcome: discovery from the start data, the model
    /// catalog, or a host global.
    fn call_global(
        &self,
        call: &CodemodeHostCall,
    ) -> BoxFuture<'static, SessionResult<CodemodeOutcome>> {
        let name = call.name.clone();
        let args = call.args.clone();
        let cx = self.cx.clone();
        if DISCOVERY_GLOBALS.contains(&name.as_str()) {
            let outcome = match discover(&self.start, &name, args.as_ref()) {
                Ok(value) => CodemodeOutcome::Ok { value },
                Err(message) => CodemodeOutcome::Err {
                    message,
                    properties: None,
                },
            };
            return async move { Ok(outcome) }.boxed();
        }
        if CATALOG_GLOBALS.contains(&name.as_str()) {
            let models = self.api.models();
            return async move {
                match catalog_call(&name, args.as_ref(), &models, &cx).await {
                    Ok(value) => Ok(CodemodeOutcome::Ok { value }),
                    Err(message) => abort_or(&cx, message),
                }
            }
            .boxed();
        }
        let Some(global) = self
            .options
            .globals
            .iter()
            .find(|global| global.name == name)
        else {
            return async move {
                Ok(CodemodeOutcome::Err {
                    message: format!("Unknown global {name}"),
                    properties: None,
                })
            }
            .boxed();
        };
        let running = (global.execute)(args, Arc::clone(&self.api), cx.clone());
        async move {
            match running.await {
                Ok(value) => Ok(CodemodeOutcome::Ok { value }),
                Err(error) => abort_or(&cx, error.to_string()),
            }
        }
        .boxed()
    }

    /// The script made a tool call: its row appears, running, also while it
    /// waits to launch.
    fn started_row(&mut self, call: &CodemodeHostCall) {
        if self.rows.contains_key(&call.id) {
            return;
        }
        let name = call
            .name
            .strip_prefix(CODEMODE_INTERNAL_PREFIX)
            .unwrap_or(&call.name)
            .to_owned();
        self.rows.insert(
            call.id,
            CodemodeNestedCall {
                id: call.id,
                name,
                args: cut(&json_text(call.args.as_ref()), ARGS_PREVIEW_CHARS),
                status: CodemodeCallStatus::Running,
                duration_ms: None,
                error: None,
            },
        );
    }

    /// A tool call ended: its row gets its status, duration, and error (an
    /// error result is an error row, also when the script got its value).
    fn finish_tool(&mut self, id: u64, done: &ToolDone) {
        let Some(row) = self.rows.get_mut(&id) else {
            return;
        };
        let is_error = done.result.as_ref().is_none_or(|result| result.is_error);
        if let Some(result) = &done.result {
            if row.name == GENERATE_IMAGES_TOOL.trim_start_matches(CODEMODE_INTERNAL_PREFIX) {
                self.generated_images += count_images(result.structured_output.as_ref());
            }
            row.duration_ms = result.duration_ms;
        }
        row.status = if is_error {
            CodemodeCallStatus::Error
        } else {
            CodemodeCallStatus::Ok
        };
        let error = match &done.outcome {
            CodemodeOutcome::Err { message, .. } => message.clone(),
            CodemodeOutcome::Ok { .. } => done
                .result
                .as_ref()
                .map(error_diagnostics)
                .unwrap_or_default(),
        };
        if is_error && !error.is_empty() {
            row.error = Some(cut(&error, ERROR_PREVIEW_CHARS));
        }
    }

    /// The rows in call order; calls still running when the script ended
    /// were cancelled.
    fn details(&self) -> CodemodeToolDetails {
        CodemodeToolDetails {
            calls: self
                .rows
                .values()
                .map(|row| match row.status {
                    CodemodeCallStatus::Running => CodemodeNestedCall {
                        status: CodemodeCallStatus::Cancelled,
                        ..row.clone()
                    },
                    CodemodeCallStatus::Ok
                    | CodemodeCallStatus::Error
                    | CodemodeCallStatus::Cancelled => row.clone(),
                })
                .collect(),
            full_output_path: None,
        }
    }

    /// Journal finished calls and acknowledged counts in one commit, then
    /// deliver the calls and launch the calls the counts cover; one commit in
    /// flight at a time, so what arrives meanwhile goes into the next.
    fn pump(&mut self) {
        if self.committing || self.stopped() {
            return;
        }
        if self.queue.is_empty() && self.acks.is_empty() {
            return;
        }
        self.committing = true;
        let batch: Vec<Finished> = std::mem::take(&mut self.queue);
        let acks: Vec<(u64, u64)> = std::mem::take(&mut self.acks).into_iter().collect();
        let entries: Vec<JournalEntry> = batch
            .iter()
            .map(|item| JournalEntry {
                id: item.id,
                at: item.at,
                issued_after: None,
                global: item.global.clone(),
            })
            .collect();
        let task_id = self.api.task_id();
        let counts = acks.clone();
        let committed = self.api.commit(
            move |tx| async move {
                let journal = tx.doc(&CODEMODE_JOURNAL_DOC, task_id).await?;
                let list = journal.child("entries")?;
                for (seq, issued) in counts {
                    if seq == 0 {
                        if journal.get("firstIssued")?.is_none() {
                            journal.set("firstIssued", to_json(&issued)?)?;
                        }
                        continue;
                    }
                    let index = usize::try_from(seq - 1).unwrap_or(usize::MAX);
                    if index < list.len()? {
                        let entry = list.child(index)?;
                        if entry.get("issuedAfter")?.is_none() {
                            entry.set("issuedAfter", to_json(&issued)?)?;
                        }
                    }
                }
                for entry in &entries {
                    list.push([to_json(entry)?])?;
                }
                Ok(())
            },
            &self.cx,
        );
        self.commits.push(
            async move {
                Work::Pumped {
                    batch,
                    acks,
                    result: committed.await,
                }
            }
            .boxed(),
        );
    }

    /// The script's own outcome, stored with its store writes in one
    /// transaction.
    async fn complete(self, result: CodemodeResult) -> SessionResult<ToolExecutionResult> {
        let details = self.details();
        let files = RunFiles {
            api: Arc::clone(&self.api),
            env: self.api.env(),
            cx: self.cx.clone(),
            directory: OnceCell::new(),
        };
        let formatted = format_result(
            &result,
            FormatOptions {
                generated_images: self.generated_images,
                wall_ms: now_ms() - self.start.started_at,
                max_output_tokens: self.start.max_output_tokens,
                calls: &details.calls,
                limits: OUTPUT_LIMITS,
            },
            &files,
        )
        .await;
        let details = CodemodeToolDetails {
            full_output_path: formatted.full_output_path,
            ..details
        };
        let (is_error, writes) = match result.ending {
            CodemodeEnding::Completed { store_writes, .. } => (false, Some(store_writes)),
            CodemodeEnding::Failed(_) => (true, None),
        };
        let tool = ToolExecutionResult {
            output: Some(formatted.content),
            is_error: Some(is_error),
            details: Some(to_json(&details)?),
            ..ToolExecutionResult::default()
        };
        let task_id = self.api.task_id();
        let conversation_id = self.api.conversation_id();
        self.api
            .commit(
                move |tx| async move {
                    let run = tx.doc(&CODEMODE_RUN_DOC, task_id).await?;
                    if let Some(stored) = run.get("result")? {
                        return Ok(from_json(&stored.to_value()?)?);
                    }
                    run.set("result", to_json(&tool)?)?;
                    if let Some(writes) =
                        writes.filter(|writes| !writes.set.is_empty() || !writes.delete.is_empty())
                    {
                        let store = tx.doc(&CODEMODE_STORE_DOC, conversation_id).await?;
                        let values = store.child("values")?;
                        for key in &writes.delete {
                            values.delete(key.as_str())?;
                        }
                        for (key, value) in writes.set {
                            values.set(key, value)?;
                        }
                    }
                    Ok(tool)
                },
                &self.cx,
            )
            .await
    }
}

/// `{ ok: false, message }`, unless `cx` was aborted: then the abort.
fn abort_or(cx: &Context, message: String) -> SessionResult<CodemodeOutcome> {
    match cx
        .abort_signal()
        .and_then(|signal: AbortSignal| signal.reason())
    {
        Some(reason) => Err(SessionError::Aborted(reason)),
        None => Ok(CodemodeOutcome::Err {
            message,
            properties: None,
        }),
    }
}

/// The call an earlier attempt made under this call's key, when it is
/// another one: another target, tool, or arguments.
async fn earlier(
    api: &Arc<dyn ToolExecutionApi>,
    call: &CodemodeHostCall,
    cx: &Context,
) -> SessionResult<Option<String>> {
    let reader: &dyn crate::types::DocumentReader = api.as_ref();
    let Some(task_id) =
        nested_call_task(reader, api.task_id(), &format!("c{}", call.id), cx).await?
    else {
        return Ok(None);
    };
    let Some(record) = api.get_task(task_id, cx).await? else {
        return Ok(None);
    };
    let Ok(ToolTaskInput::Nested { call: made, .. }) = from_json::<ToolTaskInput>(&record.input)
    else {
        return Ok(None);
    };
    let made_arguments = to_json(&made.arguments)?;
    let arguments = call.args.clone().unwrap_or_else(JsonValue::object);
    if call.target == CodemodeCallTarget::Tool
        && made.name == call.name
        && made_arguments == arguments
    {
        return Ok(None);
    }
    Ok(Some(format!("tools.{}({made_arguments})", made.name)))
}

/// Writes the result's files under fixed names into the run's output
/// directory, so a rerun overwrites them.
struct RunFiles {
    api: Arc<dyn ToolExecutionApi>,
    env: Option<Arc<dyn ExecutionEnv>>,
    cx: Context,
    directory: OnceCell<String>,
}

impl RunFiles {
    /// The run's output directory: the recorded one, else a new temp
    /// directory, recorded before any file is written.
    async fn directory(&self, env: &Arc<dyn ExecutionEnv>) -> Result<String, String> {
        let task_id = self.api.task_id();
        let recorded = self
            .api
            .commit(
                move |tx| async move {
                    let run = tx.doc(&CODEMODE_RUN_DOC, task_id).await?;
                    Ok(run.get("outputDir")?.and_then(|item| {
                        item.as_value()
                            .and_then(JsonValue::as_str)
                            .map(str::to_owned)
                    }))
                },
                &self.cx,
            )
            .await
            .map_err(|error| error.to_string())?;
        if let Some(recorded) = recorded {
            return Ok(recorded);
        }
        let created = env
            .create_temp_dir(Some("pi-codemode-"), &self.cx)
            .await
            .map_err(|error| error.message)?;
        self.api
            .commit(
                move |tx| async move {
                    let run = tx.doc(&CODEMODE_RUN_DOC, task_id).await?;
                    if let Some(recorded) = run.get("outputDir")?.and_then(|item| {
                        item.as_value()
                            .and_then(JsonValue::as_str)
                            .map(str::to_owned)
                    }) {
                        return Ok(recorded);
                    }
                    run.set("outputDir", created.as_str())?;
                    Ok(created)
                },
                &self.cx,
            )
            .await
            .map_err(|error| error.to_string())
    }
}

impl OutputFiles for RunFiles {
    async fn write(&self, name: &str, data: &[u8]) -> Result<String, String> {
        let Some(env) = &self.env else {
            return Err("no execution environment".to_owned());
        };
        let directory = self
            .directory
            .get_or_try_init(|| self.directory(env))
            .await?;
        let path = format!("{directory}/{name}");
        env.write_file(&path, data, &self.cx)
            .await
            .map_err(|error| error.message)?;
        Ok(path)
    }
}
