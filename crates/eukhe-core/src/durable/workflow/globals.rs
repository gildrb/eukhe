//! The `wf.*` host globals behind the script API: `wf.batch` (admit the
//! writing agents a script starts together as one batch on the agent
//! tree, [`super::tree`]), `wf.agent` (admit, spawn a silent child
//! through `rlm.run`: a read-only help leaf, or a writing batch's leaf;
//! wait through `rlm.collect`, read the answer through `rlm.answer`),
//! `wf.phase`, and `wf.log`. Each result is journaled by code mode, so a
//! replay never calls one twice; a global cut off by a restart runs again
//! and finds its batch, its agent row and its child by name.

use std::sync::Arc;
use std::time::Duration;

use eukhe_bend::wire::{Reader, WireError, Writer};
use eukhe_bend::{expect_core, Entry};
use eukhe_chord::context::Context;
use eukhe_chord::json::JsonValue;
use eukhe_durable::codemode::CodemodeGlobal;
use eukhe_durable::harness::types::{ToolExecutionApi, ToolExecutionApiExt};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_types::input_origin::ChildFailure;
use eukhe_types::workflow::WorkflowAgentStatus;
use futures::FutureExt;
use serde_json::{json, Map, Value};
use sha2::{Digest, Sha256};

use super::batch::{crown as batch_crown, place, Outcome, NEEDS_FILES};
use super::batch_doc::{tx_batches, tx_end, tx_put_batch, tx_remove_batch};
use super::run_doc::{tx_put_run, tx_run, tx_runs, AgentRow, RunRecord};
use super::schema::{extract_json, validate, SchemaMismatch};
use super::tree::{self, Written};
use crate::durable::deps::{HostCall, HostRequestRegistry};

/// What the globals need from the session.
pub(super) struct WorkflowServices {
    pub(super) host_requests: HostRequestRegistry,
}

/// What a child's spawn and wait run on: the session's host requests,
/// the calling `workflow` run, and its context.
#[derive(Clone, Copy)]
struct Host<'a> {
    services: &'a WorkflowServices,
    api: &'a Arc<dyn ToolExecutionApi>,
    cx: &'a Context,
}

/// The longest one `rlm.collect` wait asks for (the runtime caps it at 30
/// minutes); the run checks its abort between two.
const COLLECT_WAIT_MS: u64 = 30_000;
/// How `rlm.answer` refuses a name no live child holds.
const NO_SUCH_CHILD: &str = "No direct RLM child matches";
/// Characters of an answer or error a row's note keeps.
const NOTE_CHARS: usize = 160;

const AGENT_PREAMBLE: &str = "You are one agent of a dynamic workflow. Do the task below completely. Your final message is returned verbatim to the orchestrating script, so end with the full result, not a summary of your process.\n\n";
const READ_ONLY: &str =
    "You are read-only: read, run read-only commands, and report; write no file.\n\n";

/// The `wf.*` globals.
pub(super) fn globals(services: &Arc<WorkflowServices>) -> Vec<CodemodeGlobal> {
    let agent_services = Arc::clone(services);
    let batch_services = Arc::clone(services);
    vec![
        CodemodeGlobal {
            name: "wf.batch".to_owned(),
            spread: false,
            execute: Arc::new(move |args, api, cx| {
                let services = Arc::clone(&batch_services);
                async move { batch(&services, args, api, cx).await }.boxed()
            }),
        },
        CodemodeGlobal {
            name: "wf.agent".to_owned(),
            spread: false,
            execute: Arc::new(move |args, api, cx| {
                let services = Arc::clone(&agent_services);
                async move { agent(&services, args, api, cx).await }.boxed()
            }),
        },
        CodemodeGlobal {
            name: "wf.phase".to_owned(),
            spread: false,
            execute: Arc::new(|args, api, cx| {
                async move {
                    let title = string_field(args.as_ref(), "title")?;
                    update_run(&api, &cx, move |run| {
                        run.push_log(format!("phase: {title}"));
                        run.active_phase = Some(title);
                    })
                    .await?;
                    Ok(None)
                }
                .boxed()
            }),
        },
        CodemodeGlobal {
            name: "wf.log".to_owned(),
            spread: false,
            execute: Arc::new(|args, api, cx| {
                async move {
                    let message = string_field(args.as_ref(), "message")?;
                    update_run(&api, &cx, move |run| run.push_log(message)).await?;
                    Ok(None)
                }
                .boxed()
            }),
        },
    ]
}

fn to_serde(value: Option<&JsonValue>) -> SessionResult<Value> {
    match value {
        None => Ok(Value::Null),
        Some(value) => {
            serde_json::to_value(value).map_err(|error| SessionError::error(error.to_string()))
        }
    }
}

fn string_field(args: Option<&JsonValue>, key: &str) -> SessionResult<String> {
    match to_serde(args)?.get(key) {
        Some(Value::String(text)) => Ok(text.clone()),
        Some(_) | None => Err(SessionError::type_error(format!(
            "wf: {key} must be a string"
        ))),
    }
}

/// Change the run record of the calling `workflow` call.
async fn update_run(
    api: &Arc<dyn ToolExecutionApi>,
    cx: &Context,
    change: impl FnOnce(&mut RunRecord) + Send + 'static,
) -> SessionResult<()> {
    let run_id = api.task_id().to_string();
    let conversation_id = api.conversation_id();
    api.commit(
        move |tx| async move {
            let mut run = tx_run(&tx, conversation_id, &run_id)
                .await?
                .ok_or_else(|| {
                    SessionError::error(format!("workflow run {run_id} has no record"))
                })?;
            change(&mut run);
            tx_put_run(&tx, conversation_id, &run_id, &mut run).await
        },
        cx,
    )
    .await
}

/// The validated options of one `agent()` call.
#[derive(Debug, Clone, PartialEq)]
pub(super) struct AgentOptions {
    pub(super) label: Option<String>,
    pub(super) phase: Option<String>,
    pub(super) schema: Option<Value>,
    pub(super) model: Option<String>,
    pub(super) thinking: Option<String>,
    pub(super) access: Access,
}

/// What an agent may change.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Access {
    /// A help leaf: reads, writes nothing.
    ReadOnly,
    /// A leaf of a writing batch: writes these files and directories.
    Writes(Vec<String>),
}

/// Why `agent(prompt, opts)`'s `opts` are refused.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub(super) enum WorkflowOptionError {
    #[error("agent(prompt, opts): opts must be an object")]
    NotObject,
    #[error(
        "agent(prompt, opts): unknown option {key} (label, phase, schema, model, effort, scope)"
    )]
    UnknownOption { key: String },
    #[error("agent(prompt, opts): {key} must be a non-empty string")]
    NotNonEmptyString { key: &'static str },
    #[error("agent(prompt, opts): schema must be a JSON Schema object")]
    SchemaNotObject,
    #[error("{}", NEEDS_FILES)]
    NoScope,
}

/// Validate `agent(prompt, opts)`'s `opts`.
///
/// # Errors
///
/// An unknown key, a value of the wrong type, or a `scope` that names no
/// file.
pub(super) fn agent_options(options: &Value) -> Result<AgentOptions, WorkflowOptionError> {
    const KEYS: [&str; 6] = ["label", "phase", "schema", "model", "effort", "scope"];
    let Value::Object(object) = options else {
        return Err(WorkflowOptionError::NotObject);
    };
    if let Some(key) = object.keys().find(|key| !KEYS.contains(&key.as_str())) {
        return Err(WorkflowOptionError::UnknownOption { key: key.clone() });
    }
    let text = |key: &'static str| match object.get(key) {
        None | Some(Value::Null) => Ok(None),
        Some(Value::String(text)) if !text.trim().is_empty() => Ok(Some(text.trim().to_owned())),
        Some(_) => Err(WorkflowOptionError::NotNonEmptyString { key }),
    };
    let schema = match object.get("schema") {
        None | Some(Value::Null) => None,
        Some(schema @ Value::Object(_)) => Some(schema.clone()),
        Some(_) => return Err(WorkflowOptionError::SchemaNotObject),
    };
    let access = match object.get("scope") {
        None | Some(Value::Null) => Access::ReadOnly,
        Some(Value::Array(paths)) if !paths.is_empty() => Access::Writes(
            paths
                .iter()
                .map(|path| match path {
                    Value::String(path) if !path.trim().is_empty() => Ok(path.trim().to_owned()),
                    _ => Err(WorkflowOptionError::NoScope),
                })
                .collect::<Result<_, _>>()?,
        ),
        Some(_) => return Err(WorkflowOptionError::NoScope),
    };
    Ok(AgentOptions {
        label: text("label")?,
        phase: text("phase")?,
        schema,
        model: text("model")?,
        thinking: text("effort")?,
        access,
    })
}

/// The resume key of an `agent()` call: the hash of its prompt and
/// options (as JSON, in the order the script wrote them), and its occurrence among the
/// run's calls with the same pair.
#[must_use]
pub(super) fn resume_key(prompt: &str, options: &Value, occurrence: u32) -> String {
    let canonical = json!([prompt, options]).to_string();
    let digest = Sha256::digest(canonical.as_bytes());
    let mut head = [0_u8; 16];
    head.copy_from_slice(&digest[..16]);
    format!("{:032x}:{occurrence}", u128::from_be_bytes(head))
}

/// What the admission of one `agent()` call decided.
#[derive(Debug, Clone, PartialEq)]
pub(super) enum Admission {
    /// Run (or reattach to) the agent of this row.
    Run(AgentRow),
    /// The agent ended before (a replayed call cut off by a restart).
    Ended(AgentRow),
    /// An earlier run's answer serves it.
    Cached(AgentRow),
    /// The run spawned `max_agents` agents already.
    Exhausted(u32),
}

/// The run an `agent()` call may take finished answers from.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(super) enum Resumed<'a> {
    /// The run resumes none.
    Fresh,
    /// The run resumes this earlier run.
    From(&'a RunRecord),
}

/// What the admission rule decided for one `agent()` call
/// (`bend/workflow.bend` `Admit`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Decision {
    /// The call's ordinal has an ended row: replay its answer.
    Ended,
    /// The call's ordinal has a queued or running row: reattach.
    Reattach,
    /// The earlier run's row at this position (in ordinal order) serves it.
    Reuse(usize),
    /// Spawn an agent: the budget has one left.
    Spawn,
    /// The budget is spent.
    Refused,
}

/// The facts the admission rule reads (`bend/workflow.bend` `admit`):
/// the status of the call's ordinal in this run, the call's key, the
/// earlier run's rows as (key, status) in ordinal order, and the budget.
/// Keys are interned: equal resume keys get equal indexes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct AdmitFacts {
    pub(super) prior: Option<WorkflowAgentStatus>,
    pub(super) key: usize,
    pub(super) rows: Vec<(usize, WorkflowAgentStatus)>,
    pub(super) spawned: u32,
    pub(super) max_agents: u32,
}

/// A row status's wire tag (`bend/ffi_workflow.bend`).
fn status_tag(status: WorkflowAgentStatus) -> u32 {
    match status {
        WorkflowAgentStatus::Queued => 0,
        WorkflowAgentStatus::Running => 1,
        WorkflowAgentStatus::Done => 2,
        WorkflowAgentStatus::Failed => 3,
        WorkflowAgentStatus::Cancelled => 4,
        WorkflowAgentStatus::Cached => 5,
    }
}

/// The admission rule of one `agent()` call: the Bend model's `admit`
/// (`bend/workflow.bend`), run by the compiled core.
pub(super) fn decide(facts: &AdmitFacts) -> Decision {
    let decided = (|| -> Result<Decision, eukhe_bend::Error> {
        let mut request = Writer::new();
        request.tag(0);
        match facts.prior {
            None => request.none(),
            Some(status) => request.some().tag(status_tag(status)),
        };
        request.count(facts.key).count(facts.rows.len());
        for &(key, status) in &facts.rows {
            request.count(key).tag(status_tag(status));
        }
        request
            .u32(facts.spawned)
            .u32(facts.max_agents.saturating_sub(facts.spawned));
        let reply = eukhe_bend::call(Entry::Workflow, &request.finish()?)?;
        let mut reader = Reader::reply(&reply)?;
        let decision = match reader.tag_of(5, "an admission")? {
            0 => Decision::Ended,
            1 => Decision::Reattach,
            2 => {
                let at = reader.count()?;
                if at >= facts.rows.len() {
                    return Err(WireError::Malformed {
                        at: 0,
                        expected: "a row of the earlier run",
                    }
                    .into());
                }
                Decision::Reuse(at)
            }
            3 => Decision::Spawn,
            4 => Decision::Refused,
            tag => {
                return Err(WireError::Malformed {
                    at: usize::try_from(tag).unwrap_or(usize::MAX),
                    expected: "an admission",
                }
                .into())
            }
        };
        reader.nat()?;
        reader.nat()?;
        reader.end()?;
        Ok(decision)
    })();
    expect_core(Entry::Workflow, decided)
}

/// Decide one `agent()` call against the run `run`, which may take the
/// cache of the run it resumes (`resumed`), and record it: the rule the
/// `wf.agent` global commits.
pub(super) fn admit(
    run: &mut RunRecord,
    resumed: Resumed<'_>,
    ordinal: u32,
    fresh: AgentRow,
) -> Admission {
    let earlier: Vec<&AgentRow> = match resumed {
        Resumed::Fresh => Vec::new(),
        Resumed::From(earlier) => earlier.agents.values().collect(),
    };
    let facts = {
        let mut keys: Vec<&str> = vec![fresh.key.as_str()];
        let rows = earlier
            .iter()
            .map(|row| {
                let key = row.key.as_str();
                let at = keys
                    .iter()
                    .position(|known| *known == key)
                    .unwrap_or_else(|| {
                        keys.push(key);
                        keys.len() - 1
                    });
                (at, row.status)
            })
            .collect();
        AdmitFacts {
            prior: run.agents.get(&ordinal).map(|row| row.status),
            key: 0,
            rows,
            spawned: run.spawned(),
            max_agents: run.max_agents,
        }
    };
    match decide(&facts) {
        Decision::Ended => Admission::Ended(run.agents[&ordinal].clone()),
        Decision::Reattach => Admission::Run(run.agents[&ordinal].clone()),
        Decision::Reuse(at) => {
            let hit = earlier[at];
            let row = AgentRow {
                status: WorkflowAgentStatus::Cached,
                child_name: None,
                child_session_id: hit.child_session_id.clone(),
                result: hit.result.clone(),
                note: hit.note.clone(),
                counted: false,
                ..fresh
            };
            run.agents.insert(ordinal, row.clone());
            Admission::Cached(row)
        }
        Decision::Spawn => {
            run.agents.insert(ordinal, fresh.clone());
            Admission::Run(fresh)
        }
        Decision::Refused => Admission::Exhausted(run.max_agents),
    }
}

fn note_of(text: &str) -> String {
    let compact = text.split_whitespace().collect::<Vec<_>>().join(" ");
    if compact.chars().count() <= NOTE_CHARS {
        return compact;
    }
    let kept: String = compact.chars().take(NOTE_CHARS - 1).collect();
    format!("{kept}…")
}

/// One `agent()` call as the script sends it.
struct Call {
    ordinal: u32,
    occurrence: u32,
    prompt: String,
    raw_options: Value,
    options: AgentOptions,
}

/// The call `args` of global `global` names.
fn call_of(args: &Value, global: &str) -> SessionResult<Call> {
    let number = |key: &str| {
        args.get(key)
            .and_then(Value::as_u64)
            .and_then(|number| u32::try_from(number).ok())
            .ok_or_else(|| {
                SessionError::type_error(format!("{global}: {key} must be a whole number"))
            })
    };
    let prompt = match args.get("prompt") {
        Some(Value::String(text)) => text.clone(),
        Some(_) | None => {
            return Err(SessionError::type_error(format!(
                "{global}: prompt must be a string"
            )))
        }
    };
    let raw_options = args.get("options").cloned().unwrap_or_else(|| json!({}));
    // The script sees the option error as a TypeError message.
    let options =
        agent_options(&raw_options).map_err(|error| SessionError::type_error(error.to_string()))?;
    Ok(Call {
        ordinal: number("ordinal")?,
        occurrence: number("occurrence")?,
        prompt,
        raw_options,
        options,
    })
}

/// The row a call that spawns gets.
fn fresh_row(run_id: &str, call: &Call) -> AgentRow {
    AgentRow {
        ordinal: call.ordinal,
        label: call
            .options
            .label
            .clone()
            .unwrap_or_else(|| note_of(&call.prompt).chars().take(48).collect()),
        phase: call.options.phase.clone(),
        status: WorkflowAgentStatus::Queued,
        key: resume_key(&call.prompt, &call.raw_options, call.occurrence),
        child_name: Some(format!("wf{run_id}-{}", call.ordinal)),
        retries: Vec::new(),
        child_session_id: None,
        result: None,
        note: None,
        counted: true,
        batch: None,
    }
}

fn exhausted(max_agents: u32) -> String {
    format!("WorkflowBudgetExhausted: this run may spawn at most {max_agents} agents")
}

fn no_record(run_id: &str) -> SessionError {
    SessionError::error(format!("workflow run {run_id} has no record"))
}

/// `wf.batch({agents})`: admit the writing agents a script started
/// together as one batch of the agent tree, all or none: plan the
/// balanced tree over the agents that run (an earlier run's answers serve
/// the rest), then lend the batch its nodes. `null`; a refusal throws.
async fn batch(
    services: &WorkflowServices,
    args: Option<JsonValue>,
    api: Arc<dyn ToolExecutionApi>,
    cx: Context,
) -> SessionResult<Option<JsonValue>> {
    let args = to_serde(args.as_ref())?;
    let calls = match args.get("agents") {
        Some(Value::Array(agents)) if !agents.is_empty() => agents
            .iter()
            .map(|agent| call_of(agent, "wf.batch"))
            .collect::<SessionResult<Vec<_>>>()?,
        Some(_) | None => {
            return Err(SessionError::type_error(
                "wf.batch: agents must be a non-empty list",
            ))
        }
    };
    let key = calls[0].ordinal;
    let run_id = api.task_id().to_string();
    let conversation_id = api.conversation_id();
    let mut writers = Vec::with_capacity(calls.len());
    for call in &calls {
        match &call.options.access {
            Access::Writes(scope) => writers.push((fresh_row(&run_id, call), scope.clone())),
            Access::ReadOnly => return Err(SessionError::type_error(NEEDS_FILES)),
        }
    }
    let facts = host_call(services, &api, "rlm.tree_facts", json!({}))
        .await
        .map_err(|error| SessionError::error(format!("{error:#}")))
        .and_then(|reply| {
            tree::facts(&reply).map_err(|error| SessionError::error(error.to_string()))
        })?;
    let planned = {
        let run_id = run_id.clone();
        api.commit(
            move |tx| async move {
                let runs = tx_runs(&tx, conversation_id).await?;
                let batches = tx_batches(&tx, conversation_id).await?;
                let run = runs.runs.get(&run_id).ok_or_else(|| no_record(&run_id))?;
                let lent = tree::lend_key(&run_id, key);
                if let Some(batch) = batches.batches.get(&lent) {
                    return Ok(Ok(Some(tree::nodes(batch.leaves.len()))));
                }
                let resumed = run
                    .resume_from
                    .as_ref()
                    .and_then(|from| runs.runs.get(from));
                let cache = match resumed {
                    Some(earlier) => Resumed::From(earlier),
                    None => Resumed::Fresh,
                };
                let mut trial = run.clone();
                let mut agents = Vec::new();
                for (row, scope) in writers {
                    let ordinal = row.ordinal;
                    match admit(&mut trial, cache, ordinal, row) {
                        Admission::Exhausted(max_agents) => return Ok(Err(exhausted(max_agents))),
                        Admission::Run(_) => agents.push((ordinal, scope)),
                        Admission::Cached(_) | Admission::Ended(_) => {}
                    }
                }
                if !agents.is_empty() {
                    let batch = match batches.admit(&facts, &agents) {
                        Ok(batch) => batch,
                        Err(refusal) => return Ok(Err(refusal.to_string())),
                    };
                    for (ordinal, _) in &agents {
                        if let Some(row) = trial.agents.get_mut(ordinal) {
                            row.batch = Some(key);
                        }
                    }
                    tx_put_batch(&tx, conversation_id, &lent, &batch).await?;
                }
                tx_put_run(&tx, conversation_id, &run_id, &mut trial).await?;
                Ok(Ok((!agents.is_empty()).then(|| tree::nodes(agents.len()))))
            },
            &cx,
        )
        .await?
    };
    let nodes = match planned {
        Err(refusal) => return Err(SessionError::error(refusal)),
        Ok(None) => return Ok(None),
        Ok(Some(nodes)) => nodes,
    };
    let lent = tree::lend_key(&run_id, key);
    let lent_reply = host_call(
        services,
        &api,
        "rlm.tree_lend",
        json!({ "key": lent, "nodes": nodes }),
    )
    .await;
    if let Err(error) = lent_reply {
        api.commit(
            move |tx| async move {
                tx_remove_batch(&tx, conversation_id, &lent).await?;
                let mut run = tx_run(&tx, conversation_id, &run_id)
                    .await?
                    .ok_or_else(|| no_record(&run_id))?;
                run.agents.retain(|_, row| row.batch != Some(key));
                tx_put_run(&tx, conversation_id, &run_id, &mut run).await
            },
            &cx,
        )
        .await?;
        return Err(SessionError::error(format!("{error:#}")));
    }
    Ok(None)
}

/// How an agent's child spawns.
pub(super) enum Spawn {
    /// A read-only help leaf of the session.
    Help,
    /// A leaf of writing batch `batch`, with these spawn kwargs.
    Leaf {
        /// The batch's key (`batch_doc`).
        batch: String,
        units: usize,
        kwargs: Map<String, Value>,
    },
}

/// `wf.agent({ordinal, occurrence, prompt, options})`: `{result, cached}`.
/// A writing agent's result is `{result, conflicts}`.
async fn agent(
    services: &WorkflowServices,
    args: Option<JsonValue>,
    api: Arc<dyn ToolExecutionApi>,
    cx: Context,
) -> SessionResult<Option<JsonValue>> {
    let call = call_of(&to_serde(args.as_ref())?, "wf.agent")?;
    let run_id = api.task_id().to_string();
    let conversation_id = api.conversation_id();
    let fresh = fresh_row(&run_id, &call);
    let ordinal = call.ordinal;
    let (admission, batch) = {
        let run_id = run_id.clone();
        api.commit(
            move |tx| async move {
                let mut run = tx_run(&tx, conversation_id, &run_id)
                    .await?
                    .ok_or_else(|| no_record(&run_id))?;
                let resumed = match &run.resume_from {
                    Some(from) => tx_run(&tx, conversation_id, from).await?,
                    None => None,
                };
                let cache = match &resumed {
                    Some(earlier) => Resumed::From(earlier),
                    None => Resumed::Fresh,
                };
                let admission = admit(&mut run, cache, ordinal, fresh);
                tx_put_run(&tx, conversation_id, &run_id, &mut run).await?;
                let key = run.agents.get(&ordinal).and_then(|row| row.batch);
                let batch = match key {
                    Some(first) => {
                        let key = tree::lend_key(&run_id, first);
                        let batch = tx_batches(&tx, conversation_id)
                            .await?
                            .batches
                            .get(&key)
                            .cloned();
                        batch.map(|batch| (key, batch))
                    }
                    None => None,
                };
                Ok((admission, batch))
            },
            &cx,
        )
        .await?
    };
    let row = match admission {
        Admission::Exhausted(max_agents) => return Err(SessionError::error(exhausted(max_agents))),
        Admission::Cached(row) => return Ok(Some(answer_value(row.result, Source::Cached)?)),
        Admission::Ended(row) => {
            let source = match row.status {
                WorkflowAgentStatus::Cached => Source::Cached,
                WorkflowAgentStatus::Queued
                | WorkflowAgentStatus::Running
                | WorkflowAgentStatus::Done
                | WorkflowAgentStatus::Failed
                | WorkflowAgentStatus::Cancelled => Source::Ran,
            };
            return Ok(Some(answer_value(row.result, source)?));
        }
        Admission::Run(row) => row,
    };
    let spawn = match (&call.options.access, batch) {
        (Access::ReadOnly, None) => Spawn::Help,
        (Access::Writes(_), Some((key, batch))) => {
            let place = batch_crown(&batch)
                .ok()
                .and_then(|crown| place(&batch, &crown, ordinal))
                .ok_or_else(|| {
                    SessionError::error(format!(
                        "wf.agent: agent {ordinal} has no place in its batch"
                    ))
                })?;
            Spawn::Leaf {
                batch: key,
                units: batch.units.len(),
                kwargs: tree::leaf_kwargs(&batch, &place),
            }
        }
        (Access::Writes(_), None) | (Access::ReadOnly, Some(_)) => {
            return Err(SessionError::error(format!(
                "wf.agent: agent {ordinal} was not admitted in a writing batch"
            )))
        }
    };
    let result = run_agent(services, &api, &cx, &row, &call, &spawn).await?;
    Ok(Some(answer_value(result, Source::Ran)?))
}

/// Whether an agent's answer came from an earlier run's cache.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Source {
    /// The agent ran in this run.
    Ran,
    /// An earlier run's answer served the agent.
    Cached,
}

fn answer_value(result: Option<Value>, source: Source) -> SessionResult<JsonValue> {
    let cached = match source {
        Source::Ran => false,
        Source::Cached => true,
    };
    let value = json!({ "result": result.unwrap_or(Value::Null), "cached": cached });
    serde_json::from_value(value).map_err(|error| SessionError::error(error.to_string()))
}

/// The task line that tells an agent what it may change.
pub(super) fn access_line(access: &Access) -> String {
    match access {
        Access::ReadOnly => READ_ONLY.to_owned(),
        Access::Writes(scope) => format!(
            "Write only inside: {}. Changes elsewhere return to the workflow as conflicts and are not applied.\n\n",
            scope.join(", ")
        ),
    }
}

/// Run the child of `row` to its end; what the script gets (`None`:
/// `null`). A writing agent's end goes into its batch, whose integrators
/// it completes; its result carries the paths that came back as
/// conflicts.
async fn run_agent(
    services: &WorkflowServices,
    api: &Arc<dyn ToolExecutionApi>,
    cx: &Context,
    row: &AgentRow,
    call: &Call,
    spawn: &Spawn,
) -> SessionResult<Option<Value>> {
    let Some(name) = row.child_name.clone() else {
        return Ok(row.result.clone());
    };
    let options = &call.options;
    let head = format!(
        "{AGENT_PREAMBLE}{}{}",
        access_line(&options.access),
        call.prompt
    );
    let full_prompt = match &options.schema {
        None => head,
        Some(schema) => format!(
            "{head}\n\nEnd your final message with one ```json fenced block holding a JSON value that matches this JSON Schema:\n{schema}"
        ),
    };
    let ordinal = row.ordinal;
    let host = Host { services, api, cx };
    let (first, wrote) = answer_of(host, &name, &full_prompt, options, spawn, ordinal).await?;
    let (outcome, written) = match first {
        Ok(answer) => match &options.schema {
            None => (Ok(Value::String(answer)), wrote),
            Some(schema) => match checked(&answer, schema) {
                Ok(value) => (Ok(value), wrote),
                Err(mismatch) => {
                    let retry = format!(
                        "{full_prompt}\n\nAn earlier attempt answered this, which does not match the schema ({mismatch}):\n{answer}\n\nAnswer again; end with the matching ```json block."
                    );
                    let retry_name = format!("{name}r");
                    record_child(api, cx, ordinal, retry_name.clone()).await?;
                    let (second, again) =
                        answer_of(host, &retry_name, &retry, options, spawn, ordinal).await?;
                    let checked = second.and_then(|second| {
                        checked(&second, schema).map_err(AgentFailure::MismatchAfterRetry)
                    });
                    (checked, wrote.then(again))
                }
            },
        },
        Err(error) => (Err(error), wrote),
    };
    let (status, result, note) = match outcome {
        Ok(value) => {
            let note = match &value {
                Value::String(text) => note_of(text),
                other => note_of(&other.to_string()),
            };
            let result = match spawn {
                Spawn::Help => value,
                Spawn::Leaf { .. } => json!({ "result": value, "conflicts": written.conflicts }),
            };
            (WorkflowAgentStatus::Done, Some(result), note)
        }
        // The row's note is where the failure becomes text.
        Err(error) => (
            WorkflowAgentStatus::Failed,
            None,
            note_of(&error.to_string()),
        ),
    };
    let end = match spawn {
        Spawn::Help => None,
        Spawn::Leaf { batch, units, .. } => {
            let outcome = match status {
                WorkflowAgentStatus::Done => Outcome::Finished,
                WorkflowAgentStatus::Queued
                | WorkflowAgentStatus::Running
                | WorkflowAgentStatus::Failed
                | WorkflowAgentStatus::Cancelled
                | WorkflowAgentStatus::Cached => Outcome::Failed,
            };
            Some((batch.clone(), outcome, written.patch_over(*units)))
        }
    };
    let stored = result.clone();
    let run_id = api.task_id().to_string();
    let conversation_id = api.conversation_id();
    let settled = api
        .commit(
            move |tx| async move {
                let mut run = tx_run(&tx, conversation_id, &run_id)
                    .await?
                    .ok_or_else(|| no_record(&run_id))?;
                if let Some(agent) = run.agents.get_mut(&ordinal) {
                    agent.status = status;
                    agent.result = stored;
                    agent.note = Some(note);
                }
                tx_put_run(&tx, conversation_id, &run_id, &mut run).await?;
                match end {
                    Some((key, outcome, patch)) => {
                        let settled =
                            tx_end(&tx, conversation_id, &key, ordinal, outcome, patch).await?;
                        Ok(settled.then_some(key))
                    }
                    None => Ok(None),
                }
            },
            cx,
        )
        .await?;
    if let Some(key) = settled {
        host_call(services, api, "rlm.tree_return", json!({ "key": key }))
            .await
            .map_err(|error| SessionError::error(format!("{error:#}")))?;
    }
    Ok(result)
}

/// Name `child` on agent `ordinal`'s row before it spawns, so a cancel of
/// the run reaches it.
async fn record_child(
    api: &Arc<dyn ToolExecutionApi>,
    cx: &Context,
    ordinal: u32,
    child: String,
) -> SessionResult<()> {
    update_run(api, cx, move |run| {
        if let Some(agent) = run.agents.get_mut(&ordinal) {
            if !agent.retries.contains(&child) {
                agent.retries.push(child);
            }
        }
    })
    .await
}

/// The answer of the agent's child `name`, or why it has none, and what
/// its children wrote. A child interrupted from outside (its parent's
/// worker crashed, or its own worker died) runs once more as `<name>i`.
async fn answer_of(
    host: Host<'_>,
    name: &str,
    prompt: &str,
    options: &AgentOptions,
    spawn: &Spawn,
    ordinal: u32,
) -> SessionResult<(Result<String, AgentFailure>, Written)> {
    let (interrupted, wrote) =
        match settle_child(host, name, prompt, options, spawn, ordinal).await? {
            (ChildEnd::Answered(answer), wrote) => return Ok((Ok(answer), wrote)),
            (ChildEnd::Failed(error), wrote) => return Ok((Err(error), wrote)),
            (ChildEnd::Interrupted(error), wrote) => (error, wrote),
        };
    let restart = format!("{name}i");
    record_child(host.api, host.cx, ordinal, restart.clone()).await?;
    let (end, again) = settle_child(host, &restart, prompt, options, spawn, ordinal).await?;
    let answer = match end {
        ChildEnd::Answered(answer) => Ok(answer),
        ChildEnd::Failed(error) => Err(error),
        ChildEnd::Interrupted(again) => Err(AgentFailure::InterruptedTwice {
            first: Box::new(interrupted),
            again: Box::new(again),
        }),
    };
    Ok((answer, wrote.then(again)))
}

fn checked(answer: &str, schema: &Value) -> Result<Value, AnswerCheckError> {
    let value = extract_json(answer).ok_or(AnswerCheckError::NoJson)?;
    validate(&value, schema)?;
    Ok(value)
}

/// Why an answer does not serve an `agent()` call with a schema.
#[derive(Debug, thiserror::Error)]
enum AnswerCheckError {
    #[error("the answer holds no JSON value")]
    NoJson,
    #[error(transparent)]
    Mismatch(#[from] SchemaMismatch),
}

/// Why an agent gave no answer the script can use.
#[derive(Debug, thiserror::Error)]
enum AgentFailure {
    /// A host request (`rlm.run`, `rlm.collect`, `rlm.answer`) failed.
    #[error("{0:#}")]
    Host(#[source] anyhow::Error),
    /// `rlm.answer` settled the child without a status.
    #[error("rlm.answer gave no status for agent {name}")]
    NoStatus { name: String },
    /// The child finished without an answer.
    #[error("the agent ended without an answer")]
    NoAnswer,
    /// The child ended with this error text from `rlm.answer`.
    #[error("{error}")]
    Reported { error: String },
    /// The child ended with this status and no error text.
    #[error("the agent ended {status}")]
    Ended { status: String },
    /// The child and its restart were both interrupted.
    #[error("the agent was interrupted twice: {first}; then: {again}")]
    InterruptedTwice {
        first: Box<AgentFailure>,
        #[source]
        again: Box<AgentFailure>,
    },
    /// The retry's answer did not serve the schema either.
    #[error("schema mismatch after a retry: {0}")]
    MismatchAfterRetry(#[source] AnswerCheckError),
}

/// How a child ended.
enum ChildEnd {
    Answered(String),
    /// The child never got its task, or it stopped mid-run for a reason
    /// outside its own work (its parent's worker crashed, or its own
    /// worker died): running it again can succeed.
    Interrupted(AgentFailure),
    Failed(AgentFailure),
}

async fn host_call(
    services: &WorkflowServices,
    api: &Arc<dyn ToolExecutionApi>,
    request_type: &str,
    data: Value,
) -> anyhow::Result<Value> {
    let handler = services.host_requests.get(request_type).ok_or_else(|| {
        anyhow::anyhow!("dynamic workflows need the eukhe daemon ({request_type} is not available)")
    })?;
    handler(HostCall {
        data,
        cell_source_code: None,
        call: Some(Arc::clone(api)),
        signal: None,
    })
    .await
}

fn aborted(cx: &Context) -> Option<SessionError> {
    cx.abort_signal()
        .and_then(|signal| signal.reason())
        .map(SessionError::Aborted)
}

/// Spawn (or find, after a restart) the silent child `name` and wait for
/// its end: how it ended and what it wrote.
async fn settle_child(
    host: Host<'_>,
    name: &str,
    prompt: &str,
    options: &AgentOptions,
    spawn: &Spawn,
    ordinal: u32,
) -> SessionResult<(ChildEnd, Written)> {
    Ok(
        match settled_state(host, name, prompt, options, spawn, ordinal).await? {
            Err(failure) => (ChildEnd::Failed(failure), Written::default()),
            Ok(state) => (end_of(name, &state)?, tree::written(&state)),
        },
    )
}

/// The spawn kwargs of the child `name`: a help leaf's, or a writing
/// leaf's with its place in the batch.
pub(super) fn spawn_kwargs(name: &str, options: &AgentOptions, spawn: &Spawn) -> Value {
    let mut kwargs = Map::new();
    kwargs.insert("name".to_owned(), json!(name));
    kwargs.insert("label".to_owned(), json!(options.label));
    kwargs.insert("phase".to_owned(), json!(options.phase));
    kwargs.insert("model".to_owned(), json!(options.model));
    kwargs.insert("thinking".to_owned(), json!(options.thinking));
    kwargs.insert("report".to_owned(), json!("silent"));
    match spawn {
        Spawn::Help => {}
        Spawn::Leaf { kwargs: leaf, .. } => kwargs.extend(leaf.clone()),
    }
    Value::Object(kwargs)
}

/// The settled `rlm.answer` state of the child `name`, spawned unless an
/// earlier attempt of this call did (a restart cut the call off: the
/// call reattaches to it); a host failure on the way.
async fn settled_state(
    host: Host<'_>,
    name: &str,
    prompt: &str,
    options: &AgentOptions,
    spawn: &Spawn,
    ordinal: u32,
) -> SessionResult<Result<Value, AgentFailure>> {
    let Host { services, api, cx } = host;
    let answer = || host_call(services, api, "rlm.answer", json!({ "target": name }));
    let found = match answer().await {
        Ok(found) => found,
        Err(error) if !format!("{error:#}").starts_with(NO_SUCH_CHILD) => {
            return Ok(Err(AgentFailure::Host(error)));
        }
        Err(_) => {
            let kwargs = spawn_kwargs(name, options, spawn);
            let spawned = host_call(
                services,
                api,
                "rlm.run",
                json!({ "prompt": prompt, "kwargs": kwargs }),
            )
            .await;
            if let Err(error) = spawned {
                return Ok(Err(AgentFailure::Host(error)));
            }
            match answer().await {
                Ok(found) => found,
                Err(error) => return Ok(Err(AgentFailure::Host(error))),
            }
        }
    };
    let session_id = found
        .get("sessionId")
        .and_then(Value::as_str)
        .map(str::to_owned);
    update_run(api, cx, move |run| {
        if let Some(agent) = run.agents.get_mut(&ordinal) {
            if !agent.status.is_terminal() {
                agent.status = WorkflowAgentStatus::Running;
            }
            agent.child_session_id = session_id;
        }
    })
    .await?;
    let mut state = found;
    loop {
        if state.get("settled") == Some(&Value::Bool(true)) {
            return Ok(Ok(state));
        }
        if let Some(error) = aborted(cx) {
            return Err(error);
        }
        let started = tokio::time::Instant::now();
        if let Err(error) = host_call(
            services,
            api,
            "rlm.collect",
            json!({ "targets": [name], "timeout_ms": COLLECT_WAIT_MS }),
        )
        .await
        {
            return Ok(Err(AgentFailure::Host(error)));
        }
        state = match answer().await {
            Ok(state) => state,
            Err(error) => return Ok(Err(AgentFailure::Host(error))),
        };
        // A collect that answers at once (its row settled, the answer not
        // yet kept, or a user message waits for the session's turn): pace
        // the polls.
        if started.elapsed() < Duration::from_millis(500)
            && state.get("settled") != Some(&Value::Bool(true))
        {
            tokio::time::sleep(Duration::from_millis(500)).await;
        }
    }
}

/// How the child `name` of the settled `state` ended.
fn end_of(name: &str, state: &Value) -> SessionResult<ChildEnd> {
    let Some(status) = state.get("status").and_then(Value::as_str) else {
        return Ok(ChildEnd::Failed(AgentFailure::NoStatus {
            name: name.to_owned(),
        }));
    };
    let answer = state
        .get("answer")
        .and_then(Value::as_str)
        .map(str::to_owned);
    let error = |other: &str| match state.get("error").and_then(Value::as_str) {
        Some(error) => AgentFailure::Reported {
            error: error.to_owned(),
        },
        None => AgentFailure::Ended {
            status: other.to_owned(),
        },
    };
    let failure = match state.get("failure") {
        None | Some(Value::Null) => None,
        Some(failure) => Some(
            serde_json::from_value::<ChildFailure>(failure.clone())
                .map_err(|error| SessionError::error(format!("rlm.answer failure: {error}")))?,
        ),
    };
    Ok(match (status, answer, failure) {
        ("done", Some(answer), _) => ChildEnd::Answered(answer),
        ("done", None, _) => ChildEnd::Failed(AgentFailure::NoAnswer),
        (
            other,
            _,
            Some(
                ChildFailure::Interrupted | ChildFailure::WorkerExited | ChildFailure::Undelivered,
            ),
        ) => ChildEnd::Interrupted(error(other)),
        (
            other,
            _,
            None
            | Some(
                ChildFailure::Provider { .. }
                | ChildFailure::Aborted
                | ChildFailure::Stalled
                | ChildFailure::Unreachable,
            ),
        ) => ChildEnd::Failed(error(other)),
    })
}
