//! The kernel host requests of the `autoresearch` skill:
//! `autoresearch.init`, `.run`, `.log`, `.flag`, `.notes`, `.state`; and
//! the loop's continuation. The loop is the autonomous run of the
//! Director stack (`durable/goals`), with [`CONTINUATION`] as its prompt:
//! when the Lab's mode turns on (an accepted init), it starts; when an
//! operation finds the mode off (the iteration cap stopped it,
//! `/autoresearch off`, or the branch changed: a branch without an open
//! session has the mode off), it stops. A user's own autonomous run is
//! never touched.

use std::sync::{Arc, Weak};
use std::time::Duration;

use anyhow::{bail, Context as _};
use eukhe_bend::rules::autoresearch::{Direction, Mode, Status};
use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_durable::harness::Harness;
use eukhe_durable::types::ConversationId;
use futures::FutureExt;
use serde_json::Value;

use super::ops::{InitArgs, LogArgs, Reply};
use super::runner::RunGate;
use super::Autoresearch;
use crate::autonomous::AgentAutonomousConfig;
use crate::durable::goals::{autonomous_state, set_autonomous, AutonomousChange};
use crate::durable::rlm::session_env;
use crate::durable::shell::{auto_set, SinkApprover};
use crate::durable::{HostCall, HostDeps};
use crate::kernel::manager::local_env;

/// The prompt of the autonomous run that continues the loop after each
/// final answer (its identity: a run with another prompt is the user's).
pub(crate) const CONTINUATION: &str = "Autoresearch mode is on: continue the experiment loop. \
First call `await autoresearch.state()`: it holds the goal, the runs, the best result, a pending \
run and your notes, and it says when the mode is off (then stop and report to the user). Log a \
pending run before you run again. Then make the next coherent experiment, run it, and log it. \
Keep going until the iteration cap or the user stops you. Preserve correctness; never game the \
benchmark.";

/// The default timeout of one run.
const DEFAULT_TIMEOUT: Duration = Duration::from_mins(10);

/// The host requests.
#[derive(Debug, Clone, Copy)]
enum Request {
    Init,
    Run,
    Log,
    Flag,
    Notes,
    State,
}

/// The autoresearch host of a session: its stores under
/// `<agent_dir>/autoresearch`, its cwd, and the gate of the `bash` tool
/// (the `shell.autoEffects` auto set read at each run, the session's
/// path policy and approval sink).
pub(crate) fn of(deps: &Arc<HostDeps>) -> Autoresearch {
    let weak = Arc::downgrade(deps);
    Autoresearch::new(
        &deps.agent_dir,
        deps.cwd.clone(),
        Arc::new(move |request: &str| gate(&weak, request)),
    )
}

fn gate(deps: &Weak<HostDeps>, request: &str) -> RunGate {
    let call = format!("autoresearch:{request}");
    match deps.upgrade() {
        Some(deps) => RunGate {
            env: local_env(&session_env(&deps)),
            auto: auto_set(&deps.settings),
            paths: crate::durable::path_policy::session_policy(
                &deps.agent_dir,
                &deps.settings,
                &deps.cwd,
            ),
            approver: SinkApprover {
                sink: deps.shell_approval.clone(),
                call,
            },
        },
        // The session closed: nothing runs unasked, nobody answers.
        None => RunGate {
            env: std::collections::HashMap::new(),
            auto: eukhe_types::shell::AutoSet::default(),
            paths: eukhe_types::path_policy::PathPolicy::new(Vec::new(), Vec::new(), Vec::new()),
            approver: SinkApprover { sink: None, call },
        },
    }
}

/// Register the `autoresearch.*` host requests of the session.
pub(crate) fn register_host_requests(deps: &Arc<HostDeps>) {
    for (name, request) in [
        ("autoresearch.init", Request::Init),
        ("autoresearch.run", Request::Run),
        ("autoresearch.log", Request::Log),
        ("autoresearch.flag", Request::Flag),
        ("autoresearch.notes", Request::Notes),
        ("autoresearch.state", Request::State),
    ] {
        let weak = Arc::downgrade(deps);
        deps.host_requests.register(
            name,
            Arc::new(move |call: HostCall| {
                let weak = weak.clone();
                async move {
                    let deps = weak
                        .upgrade()
                        .context("the session ended before the request could be served")?;
                    handle(&deps, request, call).await
                }
                .boxed()
            }),
        );
    }
}

#[tracing::instrument(skip_all, fields(request = ?request))]
async fn handle(deps: &Arc<HostDeps>, request: Request, call: HostCall) -> anyhow::Result<Value> {
    let lab = of(deps);
    let data = &call.data;
    let reply = match request {
        Request::Init => lab.init(init_args(data)?).await?,
        Request::Run => {
            let timeout = match data.get("timeout_s") {
                None | Some(Value::Null) => DEFAULT_TIMEOUT,
                Some(value) => value
                    .as_f64()
                    .filter(|seconds| seconds.is_finite() && *seconds > 0.0)
                    .map(Duration::from_secs_f64)
                    .context("autoresearch.run timeout_s must be a positive number")?,
            };
            let id = call
                .call
                .as_ref()
                .map_or_else(|| "run".to_owned(), |api| api.task_id().to_string());
            lab.run(timeout, &id).await?
        }
        Request::Log => lab.log(log_args(data)?).await?,
        Request::Flag => {
            let (run, reason) = flag(data)?;
            lab.flag(run, reason).await?
        }
        Request::Notes => {
            lab.notes(optional_text(data, "body")?, optional_text(data, "idea")?)
                .await?
        }
        Request::State => lab.state().await?,
    };
    let conversation = match &call.call {
        Some(api) => api.conversation_id(),
        None => deps.harness.root().context("the Harness is closed")?.id(),
    };
    follow_mode(&deps.harness.require()?, conversation, &reply).await?;
    Ok(reply.value)
}

/// Make the autoresearch continuation follow the Lab's mode after an
/// operation: start it when the operation turned the mode on and no
/// autonomous run is on; stop it when the mode is off and the run on is
/// the autoresearch one.
pub(crate) async fn follow_mode(
    harness: &Harness,
    conversation: ConversationId,
    reply: &Reply,
) -> anyhow::Result<()> {
    let cx = BACKGROUND_CONTEXT.clone();
    let current = autonomous_state(harness, conversation, &cx).await?;
    let ours = current.enabled && current.continuation_prompt == CONTINUATION;
    let change = match reply.mode {
        Mode::On if reply.started && !current.enabled => Some(AutonomousChange::On(continuation())),
        Mode::Off if ours => Some(AutonomousChange::Off),
        Mode::On | Mode::Off => None,
    };
    if let Some(change) = change {
        set_autonomous(harness, conversation, change, &cx).await?;
    }
    Ok(())
}

/// The largest integer exact JSON holds (`Number.MAX_SAFE_INTEGER`): the
/// autonomous run's state is a durable JSON document, which refuses
/// anything larger.
const UNBOUNDED: u64 = (1 << 53) - 1;

/// The autonomous run of the loop: the Lab's iteration cap and mode end
/// it, so its own limits are the largest a durable document holds (about
/// 285,000 years of timeout), never reached first.
fn continuation() -> AgentAutonomousConfig {
    AgentAutonomousConfig {
        enabled: Some(true),
        max_continuations: Some(UNBOUNDED),
        max_turns: Some(UNBOUNDED),
        max_tokens: Some(UNBOUNDED),
        timeout_ms: Some(UNBOUNDED),
        continuation_prompt: Some(CONTINUATION.to_owned()),
        gates: None,
        subagent_keep_alive_ms: None,
    }
}

fn text(data: &Value, key: &str) -> anyhow::Result<String> {
    match data.get(key).and_then(Value::as_str) {
        Some(value) => Ok(value.to_owned()),
        None => bail!("autoresearch: `{key}` must be a string"),
    }
}

fn optional_text(data: &Value, key: &str) -> anyhow::Result<Option<String>> {
    match data.get(key) {
        None | Some(Value::Null) => Ok(None),
        Some(Value::String(value)) => Ok(Some(value.clone())),
        Some(_) => bail!("autoresearch: `{key}` must be a string or None"),
    }
}

fn texts(data: &Value, key: &str) -> anyhow::Result<Vec<String>> {
    match data.get(key) {
        None | Some(Value::Null) => Ok(Vec::new()),
        Some(Value::Array(items)) => items
            .iter()
            .map(|item| {
                item.as_str()
                    .map(str::to_owned)
                    .with_context(|| format!("autoresearch: `{key}` must hold strings"))
            })
            .collect(),
        Some(_) => bail!("autoresearch: `{key}` must be a list of strings"),
    }
}

fn run_id(value: &Value, key: &str) -> anyhow::Result<u32> {
    value
        .as_u64()
        .and_then(|run| u32::try_from(run).ok())
        .with_context(|| format!("autoresearch: `{key}` must be a run number"))
}

fn init_args(data: &Value) -> anyhow::Result<InitArgs> {
    Ok(InitArgs {
        name: text(data, "name")?,
        metric: text(data, "metric")?,
        goal: optional_text(data, "goal")?,
        unit: optional_text(data, "unit")?.unwrap_or_default(),
        direction: match optional_text(data, "direction")?.as_deref() {
            None | Some("lower") => Direction::Lower,
            Some("higher") => Direction::Higher,
            Some(other) => {
                bail!("autoresearch: direction must be \"lower\" or \"higher\", not {other:?}")
            }
        },
        secondary: texts(data, "secondary")?,
        scope: texts(data, "scope")?,
        off_limits: texts(data, "off_limits")?,
        constraints: texts(data, "constraints")?,
        max_iterations: match data.get("max_iterations") {
            None | Some(Value::Null) => None,
            Some(value) => Some(run_id(value, "max_iterations")?),
        },
        new_segment: data
            .get("new_segment")
            .and_then(Value::as_bool)
            .unwrap_or(false),
    })
}

fn log_args(data: &Value) -> anyhow::Result<LogArgs> {
    let status = match text(data, "status")?.as_str() {
        "keep" => Status::Keep,
        "discard" => Status::Discard,
        "crash" => Status::Crash,
        "checks_failed" => Status::ChecksFailed,
        other => bail!(
            "autoresearch: status must be \"keep\", \"discard\", \"crash\" or \"checks_failed\", not {other:?}"
        ),
    };
    let flags = match data.get("flag_runs") {
        None | Some(Value::Null) => Vec::new(),
        Some(Value::Array(items)) => items.iter().map(flag).collect::<anyhow::Result<_>>()?,
        Some(_) => bail!("autoresearch: `flag_runs` must be a list of {{run, reason}}"),
    };
    Ok(LogArgs {
        status,
        description: text(data, "description")?,
        justification: optional_text(data, "justification")?,
        flags,
    })
}

fn flag(data: &Value) -> anyhow::Result<(u32, String)> {
    let run = data
        .get("run")
        .context("autoresearch: a flag needs `run`")?;
    Ok((run_id(run, "run")?, text(data, "reason")?))
}
