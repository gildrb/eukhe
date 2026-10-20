//! The `wf.*` host globals behind the script API: `wf.agent` (admit,
//! spawn a silent child through `rlm.run`, wait through `rlm.collect`,
//! read the answer through `rlm.answer`), `wf.phase`, and `wf.log`. Each
//! result is journaled by code mode, so a replay never calls one twice;
//! a global cut off by a restart runs again and finds its agent row and
//! its child by name.

use std::sync::Arc;
use std::time::Duration;

use eukhe_chord::context::Context;
use eukhe_chord::json::JsonValue;
use eukhe_durable::codemode::CodemodeGlobal;
use eukhe_durable::harness::types::{ToolExecutionApi, ToolExecutionApiExt};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_types::workflow::WorkflowAgentStatus;
use futures::FutureExt;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

use super::run_doc::{tx_put_run, tx_run, AgentRow, RunRecord};
use super::schema::{extract_json, validate};
use crate::durable::deps::{HostCall, HostRequestRegistry};

/// What the globals need from the session.
pub(super) struct WorkflowServices {
    pub(super) host_requests: HostRequestRegistry,
}

/// The longest one `rlm.collect` wait asks for; the runtime clamps it to
/// its blocking budget.
const COLLECT_WAIT_MS: u64 = 60_000;
/// The pause before a spawn refused by the family's concurrency cap is
/// tried again, and how many times it is.
const SPAWN_RETRY_PAUSE: Duration = Duration::from_secs(2);
const SPAWN_RETRIES: u32 = 300;
/// Characters of an answer or error a row's note keeps.
const NOTE_CHARS: usize = 160;

const AGENT_PREAMBLE: &str = "You are one agent of a dynamic workflow. Do the task below completely. Your final message is returned verbatim to the orchestrating script, so end with the full result, not a summary of your process.\n\n";

/// The `wf.*` globals.
pub(super) fn globals(services: &Arc<WorkflowServices>) -> Vec<CodemodeGlobal> {
    let agent_services = Arc::clone(services);
    vec![
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
            tx_put_run(&tx, conversation_id, &run_id, &run).await
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
    pub(super) isolated: bool,
}

/// Validate `agent(prompt, opts)`'s `opts`.
///
/// # Errors
///
/// An unknown key or a value of the wrong type.
pub(super) fn agent_options(options: &Value) -> Result<AgentOptions, String> {
    let Value::Object(object) = options else {
        return Err("agent(prompt, opts): opts must be an object".to_owned());
    };
    const KEYS: [&str; 6] = ["label", "phase", "schema", "model", "effort", "isolation"];
    if let Some(key) = object.keys().find(|key| !KEYS.contains(&key.as_str())) {
        return Err(format!(
            "agent(prompt, opts): unknown option {key} (label, phase, schema, model, effort, isolation)"
        ));
    }
    let text = |key: &str| match object.get(key) {
        None | Some(Value::Null) => Ok(None),
        Some(Value::String(text)) if !text.trim().is_empty() => Ok(Some(text.trim().to_owned())),
        Some(_) => Err(format!(
            "agent(prompt, opts): {key} must be a non-empty string"
        )),
    };
    let schema = match object.get("schema") {
        None | Some(Value::Null) => None,
        Some(schema @ Value::Object(_)) => Some(schema.clone()),
        Some(_) => {
            return Err("agent(prompt, opts): schema must be a JSON Schema object".to_owned())
        }
    };
    let isolated = match text("isolation")?.as_deref() {
        None | Some("shared") => false,
        Some("worktree" | "isolated") => true,
        Some(other) => {
            return Err(format!(
                "agent(prompt, opts): isolation must be \"worktree\" or \"shared\", not {other}"
            ))
        }
    };
    Ok(AgentOptions {
        label: text("label")?,
        phase: text("phase")?,
        schema,
        model: text("model")?,
        thinking: text("effort")?,
        isolated,
    })
}

/// The resume key of an `agent()` call: the hash of its prompt and
/// options (as JSON, in the order the script wrote them), and its occurrence among the
/// run's calls with the same pair.
#[must_use]
pub(super) fn resume_key(prompt: &str, options: &Value, occurrence: u32) -> String {
    let canonical = json!([prompt, options]).to_string();
    let digest = Sha256::digest(canonical.as_bytes());
    let hex: String = digest[..16]
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect();
    format!("{hex}:{occurrence}")
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

/// Decide one `agent()` call against the run `run`, which may take the
/// cache of `resumed` (the run it resumes): the pure rule the `wf.agent`
/// global commits, and the Bend bridge replays.
pub(super) fn admit(
    run: &mut RunRecord,
    resumed: Option<&RunRecord>,
    ordinal: u32,
    fresh: AgentRow,
) -> Admission {
    if let Some(row) = run.agents.get(&ordinal) {
        return if row.status.is_terminal() {
            Admission::Ended(row.clone())
        } else {
            Admission::Run(row.clone())
        };
    }
    let hit = resumed.and_then(|resumed| {
        resumed.agents.values().find(|old| {
            old.key == fresh.key
                && matches!(
                    old.status,
                    WorkflowAgentStatus::Done | WorkflowAgentStatus::Cached
                )
        })
    });
    if let Some(hit) = hit {
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
        return Admission::Cached(row);
    }
    if run.spawned() >= run.max_agents {
        return Admission::Exhausted(run.max_agents);
    }
    run.agents.insert(ordinal, fresh.clone());
    Admission::Run(fresh)
}

fn note_of(text: &str) -> String {
    let compact = text.split_whitespace().collect::<Vec<_>>().join(" ");
    if compact.chars().count() <= NOTE_CHARS {
        return compact;
    }
    let kept: String = compact.chars().take(NOTE_CHARS - 1).collect();
    format!("{kept}…")
}

/// `wf.agent({ordinal, occurrence, prompt, options})`: `{result, cached}`.
async fn agent(
    services: &WorkflowServices,
    args: Option<JsonValue>,
    api: Arc<dyn ToolExecutionApi>,
    cx: Context,
) -> SessionResult<Option<JsonValue>> {
    let args = to_serde(args.as_ref())?;
    let ordinal = args
        .get("ordinal")
        .and_then(Value::as_u64)
        .and_then(|ordinal| u32::try_from(ordinal).ok())
        .ok_or_else(|| SessionError::type_error("wf.agent: ordinal must be a whole number"))?;
    let occurrence = args
        .get("occurrence")
        .and_then(Value::as_u64)
        .and_then(|occurrence| u32::try_from(occurrence).ok())
        .ok_or_else(|| SessionError::type_error("wf.agent: occurrence must be a whole number"))?;
    let prompt = string_field_of(&args, "prompt")?;
    let raw_options = args.get("options").cloned().unwrap_or_else(|| json!({}));
    let options = agent_options(&raw_options).map_err(SessionError::type_error)?;
    let run_id = api.task_id().to_string();
    let conversation_id = api.conversation_id();
    let fresh = AgentRow {
        ordinal,
        label: options
            .label
            .clone()
            .unwrap_or_else(|| note_of(&prompt).chars().take(48).collect()),
        phase: options.phase.clone(),
        status: WorkflowAgentStatus::Queued,
        key: resume_key(&prompt, &raw_options, occurrence),
        child_name: Some(format!("wf{run_id}-{ordinal}")),
        child_session_id: None,
        result: None,
        note: None,
        counted: true,
    };
    let admission = {
        let run_id = run_id.clone();
        api.commit(
            move |tx| async move {
                let mut run = tx_run(&tx, conversation_id, &run_id)
                    .await?
                    .ok_or_else(|| {
                        SessionError::error(format!("workflow run {run_id} has no record"))
                    })?;
                let resumed = match &run.resume_from {
                    Some(from) => tx_run(&tx, conversation_id, from).await?,
                    None => None,
                };
                let admission = admit(&mut run, resumed.as_ref(), ordinal, fresh);
                tx_put_run(&tx, conversation_id, &run_id, &run).await?;
                Ok(admission)
            },
            &cx,
        )
        .await?
    };
    let row = match admission {
        Admission::Exhausted(max_agents) => {
            return Err(SessionError::error(format!(
                "WorkflowBudgetExhausted: this run may spawn at most {max_agents} agents"
            )));
        }
        Admission::Cached(row) => return Ok(Some(answer_value(row.result, true)?)),
        Admission::Ended(row) => {
            let cached = row.status == WorkflowAgentStatus::Cached;
            return Ok(Some(answer_value(row.result, cached)?));
        }
        Admission::Run(row) => row,
    };
    let result = run_agent(services, &api, &cx, &row, &prompt, &options).await?;
    Ok(Some(answer_value(result, false)?))
}

fn string_field_of(args: &Value, key: &str) -> SessionResult<String> {
    match args.get(key) {
        Some(Value::String(text)) => Ok(text.clone()),
        Some(_) | None => Err(SessionError::type_error(format!(
            "wf.agent: {key} must be a string"
        ))),
    }
}

fn answer_value(result: Option<Value>, cached: bool) -> SessionResult<JsonValue> {
    let value = json!({ "result": result.unwrap_or(Value::Null), "cached": cached });
    serde_json::from_value(value).map_err(|error| SessionError::error(error.to_string()))
}

/// Run the child of `row` to its end; what the script gets (`None`:
/// `null`).
async fn run_agent(
    services: &WorkflowServices,
    api: &Arc<dyn ToolExecutionApi>,
    cx: &Context,
    row: &AgentRow,
    prompt: &str,
    options: &AgentOptions,
) -> SessionResult<Option<Value>> {
    let Some(name) = row.child_name.clone() else {
        return Ok(row.result.clone());
    };
    let full_prompt = match &options.schema {
        None => format!("{AGENT_PREAMBLE}{prompt}"),
        Some(schema) => format!(
            "{AGENT_PREAMBLE}{prompt}\n\nEnd your final message with one ```json fenced block holding a JSON value that matches this JSON Schema:\n{schema}"
        ),
    };
    let ordinal = row.ordinal;
    let outcome = match settle_child(services, api, cx, &name, &full_prompt, options, ordinal)
        .await?
    {
        ChildEnd::Answered(answer) => match &options.schema {
            None => Ok(Value::String(answer)),
            Some(schema) => match checked(&answer, schema) {
                Ok(value) => Ok(value),
                Err(mismatch) => {
                    let retry = format!(
                        "{full_prompt}\n\nAn earlier attempt answered this, which does not match the schema ({mismatch}):\n{answer}\n\nAnswer again; end with the matching ```json block."
                    );
                    match settle_child(
                        services,
                        api,
                        cx,
                        &format!("{name}r"),
                        &retry,
                        options,
                        ordinal,
                    )
                    .await?
                    {
                        ChildEnd::Answered(second) => {
                            checked(&second, schema).map_err(|mismatch| {
                                format!("schema mismatch after a retry: {mismatch}")
                            })
                        }
                        ChildEnd::Failed(error) => Err(error),
                    }
                }
            },
        },
        ChildEnd::Failed(error) => Err(error),
    };
    let (status, result, note) = match outcome {
        Ok(value) => {
            let note = match &value {
                Value::String(text) => note_of(text),
                other => note_of(&other.to_string()),
            };
            (WorkflowAgentStatus::Done, Some(value), note)
        }
        Err(error) => (WorkflowAgentStatus::Failed, None, note_of(&error)),
    };
    let stored = result.clone();
    update_run(api, cx, move |run| {
        if let Some(agent) = run.agents.get_mut(&ordinal) {
            agent.status = status;
            agent.result = stored;
            agent.note = Some(note);
        }
    })
    .await?;
    Ok(result)
}

fn checked(answer: &str, schema: &Value) -> Result<Value, String> {
    let value = extract_json(answer).ok_or_else(|| "the answer holds no JSON value".to_owned())?;
    validate(&value, schema)?;
    Ok(value)
}

/// How a child ended.
enum ChildEnd {
    Answered(String),
    Failed(String),
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
    })
    .await
}

fn aborted(cx: &Context) -> Option<SessionError> {
    cx.abort_signal()
        .and_then(|signal| signal.reason())
        .map(SessionError::Aborted)
}

/// Spawn (or find, after a restart) the silent child `name` and wait for
/// its end.
async fn settle_child(
    services: &WorkflowServices,
    api: &Arc<dyn ToolExecutionApi>,
    cx: &Context,
    name: &str,
    prompt: &str,
    options: &AgentOptions,
    ordinal: u32,
) -> SessionResult<ChildEnd> {
    let existing = host_call(services, api, "rlm.answer", json!({ "target": name }))
        .await
        .ok();
    let found = match existing {
        Some(found) => found,
        None => {
            let kwargs = json!({
                "name": name,
                "label": options.label,
                "phase": options.phase,
                "model": options.model,
                "thinking": options.thinking,
                "workspace": if options.isolated { "isolated" } else { "shared" },
                "report": "silent",
            });
            let mut tries = 0;
            loop {
                match host_call(
                    services,
                    api,
                    "rlm.run",
                    json!({ "prompt": prompt, "kwargs": kwargs }),
                )
                .await
                {
                    Ok(_) => break,
                    Err(error)
                        if format!("{error:#}").contains("concurrency limit")
                            && tries < SPAWN_RETRIES =>
                    {
                        tries += 1;
                        if let Some(error) = aborted(cx) {
                            return Err(error);
                        }
                        tokio::time::sleep(SPAWN_RETRY_PAUSE).await;
                    }
                    Err(error) => return Ok(ChildEnd::Failed(format!("{error:#}"))),
                }
            }
            match host_call(services, api, "rlm.answer", json!({ "target": name })).await {
                Ok(found) => found,
                Err(error) => return Ok(ChildEnd::Failed(format!("{error:#}"))),
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
            break;
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
            return Ok(ChildEnd::Failed(format!("{error:#}")));
        }
        state = match host_call(services, api, "rlm.answer", json!({ "target": name })).await {
            Ok(state) => state,
            Err(error) => return Ok(ChildEnd::Failed(format!("{error:#}"))),
        };
        // A runtime with no blocking budget answers at once: pace the
        // polls.
        if started.elapsed() < Duration::from_millis(500)
            && state.get("settled") != Some(&Value::Bool(true))
        {
            tokio::time::sleep(Duration::from_millis(500)).await;
        }
    }
    let status = state
        .get("status")
        .and_then(Value::as_str)
        .unwrap_or("error");
    let answer = state
        .get("answer")
        .and_then(Value::as_str)
        .map(str::to_owned);
    Ok(match (status, answer) {
        ("done", Some(answer)) => ChildEnd::Answered(answer),
        ("done", None) => ChildEnd::Failed("the agent ended without an answer".to_owned()),
        (other, _) => ChildEnd::Failed(
            state
                .get("error")
                .and_then(Value::as_str)
                .map_or_else(|| format!("the agent ended {other}"), str::to_owned),
        ),
    })
}
