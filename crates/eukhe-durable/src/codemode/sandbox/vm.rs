//! Drives one `QuickJS` VM through one script on its own thread (pi-codemode
//! `runtime/vm.ts` in deterministic mode, with the worker thread of
//! `CodemodeSandbox`).
//!
//! The thread owns the VM: it evaluates `host.js` (clock, timezone, and
//! randomness) and `prelude.js` (built-ins frozen, `tools`, output helpers,
//! `store`/`load`, globals), compiles the script, runs it until it waits,
//! then applies results the host sends, strictly in `seq` order, buffering
//! early ones. Everything it reports goes to the host as [`VmMessage`]s:
//! `Started` with the fingerprint before the script runs, `Call` for each
//! call, `Output`, `Idle` after each drain with the calls issued so far, and
//! one `Done` or `Crash`. The VM never decides on its own when it is
//! finished: after `Done` or `Crash` it stays alive until the host sends
//! `Stop` (or drops its command sender).
//!
//! `stop` is polled by `QuickJS` while the script runs and here between
//! batches of promise jobs; set, it throws an uncatchable error in the
//! script, which surfaces as `Crash`.

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::mpsc::Receiver;
use std::sync::Arc;

use rquickjs::context::{intrinsic, EvalOptions};
use rquickjs::{Context, Ctx, Function, Object, Persistent, Runtime, Value};
use tokio::sync::mpsc::UnboundedSender;

use super::super::types::{CodemodeCallTarget, CodemodeOutputItem, TextOrigin};

/// The VM's glue: deterministic clock, timezone, and randomness, and the
/// bridge encoding.
pub(super) const HOST_SOURCE: &str = include_str!("host.js");
/// pi-codemode's prelude, unchanged.
pub(super) const PRELUDE_SOURCE: &str = include_str!("prelude.js");

/// Promise jobs run between two `stop` polls while draining the job queue.
const JOBS_PER_POLL: u64 = 50;

/// Intrinsics of the VM: everything `QuickJS` has except `WeakRef` and
/// `FinalizationRegistry` (collection timing would be observable) and
/// `performance` (a host clock).
type Intrinsics = (
    intrinsic::Date,
    intrinsic::Eval,
    intrinsic::RegExpCompiler,
    intrinsic::RegExp,
    intrinsic::Json,
    intrinsic::Proxy,
    intrinsic::MapSet,
    intrinsic::TypedArrays,
    intrinsic::Promise,
);

/// What the VM thread starts with.
pub(super) struct VmData {
    /// The async function body, as the model wrote it.
    pub(super) code: String,
    /// JSON text of `[{ name, jsName, description }]`.
    pub(super) tools_json: String,
    /// JSON text of `[{ name, spread }]`.
    pub(super) globals_json: String,
    /// JSON text of `{ key: <JSON text of the value> }`.
    pub(super) store_json: String,
    pub(super) memory_limit_bytes: Option<usize>,
    pub(super) max_stack_bytes: usize,
    pub(super) started_at: f64,
    pub(super) seed: u32,
    pub(super) fingerprint: String,
}

/// A result for the VM: call `id` settles as result `seq`.
#[derive(Debug, Clone, PartialEq)]
pub(super) struct VmDelivery {
    pub(super) seq: u64,
    pub(super) now: f64,
    pub(super) id: u64,
    pub(super) ok: bool,
    /// The value's JSON text, or the error message; `None`: `undefined`.
    pub(super) payload: Option<String>,
    /// JSON text of an error's own properties.
    pub(super) properties: Option<String>,
}

/// What the host sends the VM thread.
#[derive(Debug)]
pub(super) enum VmCommand {
    Deliver(VmDelivery),
    /// Dispose the VM and end the thread.
    Stop,
}

/// What the VM reports.
#[derive(Debug, Clone, PartialEq)]
pub(super) enum VmMessage {
    Started {
        fingerprint: String,
    },
    Call {
        id: u64,
        target: CodemodeCallTarget,
        name: String,
        /// JSON text; `None`: `undefined`.
        args: Option<String>,
    },
    Output(CodemodeOutputItem),
    Idle {
        seq: u64,
        issued: u64,
    },
    Done(VmDone),
    Crash {
        message: String,
    },
}

/// How the script ended, as the prelude reported it.
#[derive(Debug, Clone, PartialEq)]
pub(super) struct VmDone {
    pub(super) outcome: VmDoneOutcome,
    /// The result being processed (0: the first run) and the calls issued
    /// by then; absent for a script that failed to compile.
    pub(super) during: Option<(u64, u64)>,
}

#[derive(Debug, Clone, PartialEq)]
pub(super) enum VmDoneOutcome {
    /// The returned value's JSON text (`None`: `undefined`) and the store
    /// writes' JSON text.
    Completed {
        value: Option<String>,
        writes: String,
    },
    /// The error's JSON text: `{ name?, message, stack? }`.
    Failed { error: String },
}

/// Run the VM until the host stops it. Every failure is posted as `Crash`.
pub(super) fn run_vm(
    data: VmData,
    post: &UnboundedSender<VmMessage>,
    commands: &Receiver<VmCommand>,
    stop: &Arc<AtomicBool>,
) {
    let counters = Arc::new(Counters::default());
    match start_vm(data, post, stop, &counters) {
        Ok(vm) => serve(&vm, post, commands, stop, &counters),
        Err(message) => {
            let _ = post.send(VmMessage::Crash { message });
            wait_for_stop(commands);
        }
    }
}

/// What the bridge counts while the script runs.
#[derive(Default)]
struct Counters {
    /// Calls the script issued, tools and globals.
    issued: AtomicU64,
    /// The result being processed; 0 during the first run.
    current: AtomicU64,
}

/// Fields drop in order: the persisted API object before the context and
/// the runtime, which asserts that no object outlives it.
struct Vm {
    api: Persistent<Object<'static>>,
    context: Context,
    runtime: Runtime,
}

fn crash(error: &rquickjs::Error) -> String {
    format!("{error}")
}

fn start_vm(
    data: VmData,
    post: &UnboundedSender<VmMessage>,
    stop: &Arc<AtomicBool>,
    counters: &Arc<Counters>,
) -> Result<Vm, String> {
    let runtime = Runtime::new().map_err(|error| crash(&error))?;
    if let Some(limit) = data.memory_limit_bytes {
        runtime.set_memory_limit(limit);
    }
    runtime.set_max_stack_size(data.max_stack_bytes);
    let interrupt = Arc::clone(stop);
    runtime.set_interrupt_handler(Some(Box::new(move || interrupt.load(Ordering::SeqCst))));
    let context = Context::custom::<Intrinsics>(&runtime).map_err(|error| crash(&error))?;
    let api = context.with(|ctx| setup(&ctx, &data, post, counters))?;
    let _ = post.send(VmMessage::Started {
        fingerprint: data.fingerprint,
    });
    let vm = Vm {
        api,
        context,
        runtime,
    };
    let compiled = vm.context.with(|ctx| -> Result<bool, String> {
        let api = restore(&ctx, &vm.api)?;
        let mut options = EvalOptions::default();
        options.strict = false;
        // The prefix shares the first line with the script so reported line
        // numbers match the script as written.
        options.filename = Some("codemode.js".to_owned());
        let source = format!("(async (tools, console) => {{{}\n}})", data.code);
        match ctx.eval_with_options::<Function, _>(source, options) {
            Ok(script) => {
                call_api::<_, Value>(&ctx, &api, "run", (script,))?;
                Ok(true)
            }
            Err(rquickjs::Error::Exception) => {
                let error = ctx.catch();
                let described: String = call_api(&ctx, &api, "describe", (error,))?;
                let _ = post.send(VmMessage::Done(VmDone {
                    outcome: VmDoneOutcome::Failed { error: described },
                    during: None,
                }));
                Ok(false)
            }
            Err(error) => Err(crash(&error)),
        }
    })?;
    if compiled {
        drain(&vm, stop)?;
        let _ = post.send(VmMessage::Idle {
            seq: 0,
            issued: counters.issued.load(Ordering::SeqCst),
        });
    }
    Ok(vm)
}

/// Evaluate the glue and the prelude; return the API object `{ settle, run,
/// stalled, setNow, describe }`.
fn setup(
    ctx: &Ctx<'_>,
    data: &VmData,
    post: &UnboundedSender<VmMessage>,
    counters: &Arc<Counters>,
) -> Result<Persistent<Object<'static>>, String> {
    let result = (|| -> rquickjs::Result<Persistent<Object<'static>>> {
        let mut options = EvalOptions::default();
        options.filename = Some("codemode-prelude.js".to_owned());
        let host: Function = ctx.eval_with_options(HOST_SOURCE, options)?;
        let host: Object = host.call((data.started_at, data.seed))?;
        let mut options = EvalOptions::default();
        options.filename = Some("codemode-prelude.js".to_owned());
        let prelude: Function = ctx.eval_with_options(PRELUDE_SOURCE, options)?;
        let sender = post.clone();
        let counters = Arc::clone(counters);
        let receive = Function::new(ctx.clone(), move |text: String| {
            bridge(&text, &sender, &counters);
        })?;
        let make_bridge: Function = host.get("bridge")?;
        let bridge: Function = make_bridge.call((receive,))?;
        let api: Object = prelude.call((
            bridge,
            data.tools_json.as_str(),
            data.globals_json.as_str(),
            data.store_json.as_str(),
        ))?;
        api.set("setNow", host.get::<_, Function>("setNow")?)?;
        api.set("describe", host.get::<_, Function>("describe")?)?;
        Ok(Persistent::save(ctx, api))
    })();
    result.map_err(|error| match error {
        rquickjs::Error::Exception => {
            let thrown = ctx.catch();
            format!("The sandbox failed to start: {}", thrown_text(&thrown))
        }
        other => crash(&other),
    })
}

/// A thrown value's text for a crash report.
fn thrown_text(value: &Value<'_>) -> String {
    if let Some(object) = value.as_object() {
        let name: Option<String> = object.get("name").ok();
        let message: Option<String> = object.get("message").ok();
        return match (name, message) {
            (Some(name), Some(message)) => format!("{name}: {message}"),
            (Some(text), None) | (None, Some(text)) => text,
            (None, None) => "unknown error".to_owned(),
        };
    }
    value
        .as_string()
        .and_then(|text| text.to_string().ok())
        .unwrap_or_else(|| "unknown error".to_owned())
}

fn restore<'js>(ctx: &Ctx<'js>, api: &Persistent<Object<'static>>) -> Result<Object<'js>, String> {
    api.clone().restore(ctx).map_err(|error| crash(&error))
}

/// Call `api[name](args)`. An exception here is uncatchable (an interrupt)
/// or the VM's own failure: the run crashes.
fn call_api<'js, A, R>(ctx: &Ctx<'js>, api: &Object<'js>, name: &str, args: A) -> Result<R, String>
where
    A: rquickjs::function::IntoArgs<'js>,
    R: rquickjs::FromJs<'js>,
{
    let function: Function = api.get(name).map_err(|error| crash(&error))?;
    function.call(args).map_err(|error| match error {
        rquickjs::Error::Exception => {
            let thrown = ctx.catch();
            if thrown.is_null() || thrown.is_undefined() {
                "Execution interrupted".to_owned()
            } else {
                thrown_text(&thrown)
            }
        }
        other => crash(&other),
    })
}

/// Decode one bridge message, `[kind, a, b, c]` as JSON text, and post it.
/// The prelude only calls the bridge with the shapes below; anything else
/// is a broken bridge and crashes the run.
fn bridge(text: &str, post: &UnboundedSender<VmMessage>, counters: &Counters) {
    let message = decode_bridge(text, counters).unwrap_or_else(|problem| VmMessage::Crash {
        message: format!(
            "Sandbox bridge broken: {problem}. The script may have modified built-ins such as a prototype's toJSON."
        ),
    });
    let _ = post.send(message);
}

fn decode_bridge(text: &str, counters: &Counters) -> Result<VmMessage, String> {
    let parts: Vec<serde_json::Value> =
        serde_json::from_str(text).map_err(|_| "bridge message is not valid JSON".to_owned())?;
    let [kind, a, b, c] = <[serde_json::Value; 4]>::try_from(parts)
        .map_err(|_| "bridge message is not four values".to_owned())?;
    let text_of = |value: &serde_json::Value| -> Result<String, String> {
        value
            .as_str()
            .map(str::to_owned)
            .ok_or_else(|| "bridge message has a malformed field".to_owned())
    };
    let optional_text = |value: &serde_json::Value| -> Result<Option<String>, String> {
        match value {
            serde_json::Value::Null => Ok(None),
            other => text_of(other).map(Some),
        }
    };
    match kind.as_str() {
        Some(kind @ ("call" | "global")) => {
            let id = a
                .as_u64()
                .ok_or_else(|| "a call has no numeric id".to_owned())?;
            counters.issued.fetch_add(1, Ordering::SeqCst);
            Ok(VmMessage::Call {
                id,
                target: if kind == "call" {
                    CodemodeCallTarget::Tool
                } else {
                    CodemodeCallTarget::Global
                },
                name: text_of(&b)?,
                args: optional_text(&c)?,
            })
        }
        Some("output") => {
            let item = match text_of(&a)?.as_str() {
                "image" => CodemodeOutputItem::Image {
                    data: text_of(&b)?,
                    mime_type: text_of(&c)?,
                },
                "console" => CodemodeOutputItem::Text {
                    text: text_of(&b)?,
                    origin: TextOrigin::Console,
                },
                "text" => CodemodeOutputItem::Text {
                    text: text_of(&b)?,
                    origin: TextOrigin::Script,
                },
                _ => return Err("unknown output kind".to_owned()),
            };
            Ok(VmMessage::Output(item))
        }
        Some("done") => {
            let during = Some((
                counters.current.load(Ordering::SeqCst),
                counters.issued.load(Ordering::SeqCst),
            ));
            let outcome = match a.as_bool() {
                Some(true) => VmDoneOutcome::Completed {
                    value: optional_text(&b)?,
                    writes: text_of(&c)?,
                },
                Some(false) => VmDoneOutcome::Failed {
                    error: text_of(&b)?,
                },
                None => return Err("done has no ok flag".to_owned()),
            };
            Ok(VmMessage::Done(VmDone { outcome, during }))
        }
        _ => Err("unknown message kind".to_owned()),
    }
}

/// Run queued jobs, then fail a script that waits on nothing that can ever
/// resume it.
fn drain(vm: &Vm, stop: &AtomicBool) -> Result<(), String> {
    let mut jobs: u64 = 0;
    while vm.runtime.is_job_pending() {
        // A job only fails for uncatchable errors, such as an interrupt.
        vm.runtime
            .execute_pending_job()
            .map_err(|_| "Promise job failed".to_owned())?;
        jobs += 1;
        if jobs.is_multiple_of(JOBS_PER_POLL) && stop.load(Ordering::SeqCst) {
            return Err("Execution interrupted".to_owned());
        }
    }
    vm.context.with(|ctx| {
        let api = restore(&ctx, &vm.api)?;
        call_api::<_, Value>(&ctx, &api, "stalled", ()).map(drop)
    })
}

/// Apply one result: the clock, the settlement, and the jobs it unblocks.
fn apply(vm: &Vm, delivery: VmDelivery, stop: &AtomicBool) -> Result<(), String> {
    vm.context.with(|ctx| {
        let api = restore(&ctx, &vm.api)?;
        call_api::<_, Value>(&ctx, &api, "setNow", (delivery.now,))?;
        call_api::<_, Value>(
            &ctx,
            &api,
            "settle",
            (
                // QuickJS numbers; call IDs stay far below 2^53.
                #[expect(clippy::cast_precision_loss, reason = "call IDs are small integers")]
                {
                    delivery.id as f64
                },
                delivery.ok,
                delivery.payload,
                delivery.properties,
            ),
        )
        .map(drop)
    })?;
    drain(vm, stop)
}

/// Serve deliveries until the host stops the VM.
fn serve(
    vm: &Vm,
    post: &UnboundedSender<VmMessage>,
    commands: &Receiver<VmCommand>,
    stop: &AtomicBool,
    counters: &Counters,
) {
    let mut next_seq: u64 = 1;
    let mut early: BTreeMap<u64, VmDelivery> = BTreeMap::new();
    let mut failed = false;
    while let Ok(command) = commands.recv() {
        let delivery = match command {
            VmCommand::Deliver(delivery) => delivery,
            VmCommand::Stop => return,
        };
        if failed {
            continue;
        }
        if delivery.seq < next_seq || early.contains_key(&delivery.seq) {
            let _ = post.send(VmMessage::Crash {
                message: format!(
                    "Result {} has sequence number {}, expected {next_seq} or later, once",
                    delivery.id, delivery.seq
                ),
            });
            failed = true;
            continue;
        }
        early.insert(delivery.seq, delivery);
        while let Some(next) = early.remove(&next_seq) {
            counters.current.store(next_seq, Ordering::SeqCst);
            if let Err(message) = apply(vm, next, stop) {
                let _ = post.send(VmMessage::Crash { message });
                failed = true;
                break;
            }
            let _ = post.send(VmMessage::Idle {
                seq: next_seq,
                issued: counters.issued.load(Ordering::SeqCst),
            });
            next_seq += 1;
        }
    }
}

fn wait_for_stop(commands: &Receiver<VmCommand>) {
    while let Ok(command) = commands.recv() {
        match command {
            VmCommand::Deliver(_) => {}
            VmCommand::Stop => return,
        }
    }
}
