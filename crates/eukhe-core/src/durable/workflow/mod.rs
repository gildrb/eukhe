//! `eukhe.workflow`: dynamic workflows. The `workflow` tool starts a run of
//! a model-written JavaScript orchestration script and returns at once with
//! the run's id. The run is a background `eukhe.workflow.run` task of the
//! calling conversation ([`run_task`]): the script runs on the code mode
//! sandbox (`eukhe_durable::codemode`), deterministic, journaled, and
//! replayed after a worker restart, and its end reaches the conversation as
//! a `[job-settled job:workflow-<id> ...]` report that wakes the model. The
//! script's `agent()` calls spawn silent RLM children (`eukhe.children`), at
//! most the run size's concurrency at once and its `max_agents` in total;
//! each run's progress lives in the `eukhe.workflow.runs` document the
//! `/workflows` view reads.

pub(crate) mod command;
mod globals;
mod meta;
mod run_doc;
mod run_task;
mod schema;
mod size;

#[cfg(test)]
mod tests;

use std::sync::Arc;

use eukhe_ai::typebox::{Options, TSchema, Type};
use eukhe_chord::context::Context;
use eukhe_chord::json::to_json;
use eukhe_durable::codemode::sandbox::{CodemodeSandbox, CodemodeSandboxOptions};
use eukhe_durable::codemode::{ClassifierDefault, CodemodeModels, CodemodeToolOptions};
use eukhe_durable::harness::define::{define_extension, define_tool};
use eukhe_durable::harness::types::{
    Extension, ToolCaller, ToolExecutionApi, ToolExecutionApiExt, ToolExecutionResult,
    ToolRegistration, ToolReplay,
};
use eukhe_durable::harness::Harness;
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::{ConversationId, TaskOptions, TaskOwnership};
use eukhe_types::pi_ai::{JsonValue as PiJsonValue, TextContent, UserContentBlock};
use eukhe_types::workflow::{WorkflowRunState, WorkflowSize};

pub use run_doc::{snapshots, unsettled_run_tasks, unsettled_runs, UnsettledRuns};
pub use size::effective_limits;

use super::deps::{HarnessCell, HostDeps, HostRequestRegistry, SessionClosing};
use super::settings::EukheSettings;
use globals::WorkflowServices;
use meta::parse_script;
use run_doc::{read_runs, run_task_id, tx_put_run, tx_run, tx_run_of_call, RunRecord};
use run_task::{run_task, RunServices, RunTask, RunTaskInput};

/// The extension name.
pub const EXTENSION_NAME: &str = "eukhe.workflow";
/// The tool name.
pub const WORKFLOW_TOOL_NAME: &str = "workflow";
/// Version of the script the tool builds (prelude and header) and of the
/// run's contract: a run started by another version is not replayed by
/// this one. Version 2 runs in a background task.
pub const WORKFLOW_MODULE_VERSION: u32 = 2;

const WORKFLOW_DESCRIPTION: &str = include_str!("../../prompts/layers/workflow.md");
const PRELUDE: &str = include_str!("prelude.js");
const NO_RUNTIME: &str =
    "dynamic workflows need the eukhe daemon: this session has no subagent runtime";

struct Shared {
    settings: Arc<EukheSettings>,
    has_runtime: bool,
    task: RunTask,
}

/// The `eukhe.workflow` extension of a session: the `workflow` tool and the
/// `eukhe.workflow.run` task.
#[must_use]
pub fn extension(deps: &Arc<HostDeps>) -> Arc<Extension> {
    install(&WorkflowConfig {
        host_requests: deps.host_requests.clone(),
        harness: deps.harness.clone(),
        settings: Arc::clone(&deps.settings),
        has_runtime: deps.children.is_some(),
        closing: deps.closing.clone(),
    })
}

/// Inputs of [`install`].
pub(crate) struct WorkflowConfig {
    /// The `rlm.*` host requests the `wf.*` globals send.
    pub(crate) host_requests: HostRequestRegistry,
    pub(crate) harness: HarnessCell,
    pub(crate) settings: Arc<EukheSettings>,
    /// Whether the session has a real subagent runtime (a daemon host).
    pub(crate) has_runtime: bool,
    /// The session's closing gate: a closing conversation admits no report.
    pub(crate) closing: SessionClosing,
}

/// The extension over `config`.
pub(crate) fn install(config: &WorkflowConfig) -> Arc<Extension> {
    let services = Arc::new(WorkflowServices {
        host_requests: config.host_requests.clone(),
    });
    let options = CodemodeToolOptions {
        models: CodemodeModels::Excluded,
        classifier: ClassifierDefault::Unset,
        globals: globals::globals(&services),
        ..CodemodeToolOptions::new(CodemodeSandbox::new(CodemodeSandboxOptions::default()))
    };
    let task = run_task(&Arc::new(RunServices {
        options: Arc::new(options),
        harness: config.harness.clone(),
        closing: config.closing.clone(),
    }));
    let erased = task.erase();
    let shared = Arc::new(Shared {
        settings: Arc::clone(&config.settings),
        has_runtime: config.has_runtime,
        task,
    });
    define_extension(Extension {
        tools: vec![workflow_tool(shared)],
        tasks: vec![erased],
        ..Extension::named(EXTENSION_NAME)
    })
}

fn described(description: &str) -> Options {
    Options::new().set("description", description)
}

fn parameters() -> TSchema {
    let fields: Vec<(&str, TSchema)> = vec![
        (
            "script",
            Type::string_with(described(
                "The workflow script: `export const meta = {...}` first, then an async function body.",
            )),
        ),
        (
            "args",
            Type::optional(Type::string_with(described(
                "The user's request; the script reads it as `args`.",
            ))),
        ),
        (
            "size",
            Type::optional(Type::string_with(described(
                "small, medium, or large; default: the workflow.size setting.",
            ))),
        ),
        (
            "resume",
            Type::optional(Type::string_with(described(
                "The run id of an earlier run whose finished agents this run reuses.",
            ))),
        ),
    ];
    Type::object(fields)
}

fn workflow_tool(shared: Arc<Shared>) -> Arc<ToolRegistration> {
    let mut tool = ToolRegistration::new(
        WORKFLOW_TOOL_NAME,
        WORKFLOW_DESCRIPTION,
        parameters(),
        move |args: PiJsonValue, api: Arc<dyn ToolExecutionApi>, cx: Context| {
            let shared = Arc::clone(&shared);
            async move { execute(&shared, &args, &api, &cx).await }
        },
    );
    tool.callers = Some(vec![ToolCaller::Model]);
    tool.replay = Some(ToolReplay::Safe);
    define_tool(tool)
}

fn optional_text(args: &PiJsonValue, key: &str) -> SessionResult<Option<String>> {
    match args.get(key) {
        None | Some(PiJsonValue::Null) => Ok(None),
        Some(PiJsonValue::String(text)) => Ok(Some(text.clone())),
        Some(_) => Err(SessionError::type_error(format!(
            "workflow {key} must be a string"
        ))),
    }
}

#[expect(
    clippy::cast_precision_loss,
    reason = "epoch milliseconds stay below 2^53"
)]
fn now_ms() -> f64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0.0, |elapsed| elapsed.as_millis() as f64)
}

/// The source the code mode sandbox runs: the header (`args`, the
/// limits), the prelude, then the script's body in its own async
/// function, whose result returns once every `phase()` and `log()` update
/// landed.
fn source(record: &RunRecord, request: &str, body: &str) -> String {
    let request = serde_json::Value::String(request.to_owned());
    format!(
        "// eukhe workflow v{WORKFLOW_MODULE_VERSION}\nconst args = {request};\nconst __wfLimits = Object.freeze({{ size: \"{size}\", concurrency: {concurrency}, maxAgents: {max_agents} }});\n{PRELUDE}\nconst __wfResult = await (async () => {{\n{body}\n}})();\nawait __wfSettled();\nreturn __wfResult;",
        size = record.size.as_str(),
        concurrency = record.concurrency.max(1),
        max_agents = record.max_agents,
    )
}

/// What the tool answers once the run of `run_id` started.
fn started(run_id: &str, record: &RunRecord) -> SessionResult<ToolExecutionResult> {
    let text = format!(
        "workflow run {run_id} ({name}): started in the background. Watch it with /workflows. Its result arrives as a [job-settled job:workflow-{run_id} ...] message that starts a new turn: do not poll and do not wait; continue with other work or end your turn.",
        name = record.meta.name
    );
    let details = serde_json::json!({ "status": "detached", "run": run_id });
    Ok(ToolExecutionResult {
        output: Some(vec![UserContentBlock::Text(TextContent::new(text))]),
        details: Some(to_json(&details)?),
        ..ToolExecutionResult::default()
    })
}

/// Start a run: validate the call, then, in one commit, create the run's
/// background task and its record. A rerun of the call (a restart cut it
/// off) finds the run it started and answers the same.
async fn execute(
    shared: &Shared,
    args: &PiJsonValue,
    api: &Arc<dyn ToolExecutionApi>,
    cx: &Context,
) -> SessionResult<ToolExecutionResult> {
    if !shared.has_runtime {
        return Err(SessionError::error(NO_RUNTIME));
    }
    let script = optional_text(args, "script")?
        .ok_or_else(|| SessionError::type_error("workflow expects a script string"))?;
    let request = optional_text(args, "args")?.unwrap_or_default();
    let size = match optional_text(args, "size")? {
        None => shared.settings.manager().get_workflow_size(),
        Some(name) => WorkflowSize::parse(name.trim()).ok_or_else(|| {
            SessionError::type_error(format!(
                "workflow size must be small, medium, or large, not {name}"
            ))
        })?,
    };
    let resume = optional_text(args, "resume")?
        .map(|run| run.trim().to_owned())
        .filter(|run| !run.is_empty());
    let parsed = parse_script(&script).map_err(SessionError::type_error)?;
    let limits = effective_limits(
        size,
        shared.settings.manager().get_subagent_max_concurrency(),
    );
    let call_task = api.task_id().to_string();
    let conversation_id = api.conversation_id();
    let definition = shared.task.as_definition_ref();
    let (run_id, record) = api
        .commit(
            move |tx| async move {
                if let Some(found) = tx_run_of_call(&tx, conversation_id, &call_task).await? {
                    return Ok(found);
                }
                if let Some(from) = &resume {
                    if tx_run(&tx, conversation_id, from).await?.is_none() {
                        return Err(SessionError::type_error(format!(
                            "workflow resume: no run {from} in this conversation"
                        )));
                    }
                }
                let mut record =
                    RunRecord::start(parsed.meta, size, limits, now_ms(), resume, call_task);
                let input = RunTaskInput::Run {
                    code: source(&record, &request, &parsed.body),
                };
                let run = tx
                    .create_task(
                        definition,
                        to_json(&input)?,
                        TaskOptions {
                            ownership: TaskOwnership::Conversation,
                            conversation_id: Some(conversation_id),
                            background: Some(true),
                            abandon_on_restart: None,
                        },
                    )
                    .await?;
                let run_id = run.to_string();
                tx_put_run(&tx, conversation_id, &run_id, &mut record).await?;
                Ok((run_id, record))
            },
            cx,
        )
        .await?;
    started(&run_id, &record)
}

/// Cancel the live children of run `run_id`: every child of each agent
/// that did not end, its schema retries included.
pub(crate) async fn cancel_agents(
    harness: &Harness,
    conversation_id: ConversationId,
    run_id: &str,
    cx: &Context,
) -> anyhow::Result<()> {
    let runs = read_runs(harness, conversation_id, cx).await?;
    let Some(record) = runs.runs.get(run_id) else {
        return Ok(());
    };
    for agent in record.agents.values() {
        if agent.status.is_terminal() {
            continue;
        }
        for name in agent.child_names() {
            super::children::cancel_child(harness, conversation_id, name, cx).await?;
        }
    }
    Ok(())
}

/// Cancel the run `run_id` of `conversation_id`: abort its background task
/// (whose abort reports the cancel to the conversation), cancel its live
/// agents, and mark it cancelled. `false` when no running run has that id.
///
/// # Errors
///
/// Document, task, or child-cancel failures.
pub async fn cancel_run(
    harness: &Harness,
    conversation_id: ConversationId,
    run_id: &str,
    cx: &Context,
) -> anyhow::Result<bool> {
    let runs = read_runs(harness, conversation_id, cx).await?;
    let Some(record) = runs.runs.get(run_id) else {
        return Ok(false);
    };
    if record.state.is_terminal() {
        return Ok(false);
    }
    harness.abort_task(run_task_id(run_id)?, cx).await?;
    cancel_agents(harness, conversation_id, run_id, cx).await?;
    let conversation = harness
        .conversation(conversation_id, cx)
        .await?
        .ok_or_else(|| anyhow::anyhow!("conversation {conversation_id} does not exist"))?;
    let run_id = run_id.to_owned();
    conversation
        .commit(
            move |tx| async move {
                if let Some(mut record) = tx_run(&tx, conversation_id, &run_id).await? {
                    if !record.state.is_terminal() {
                        record.state = WorkflowRunState::Cancelled;
                    }
                    record.cancel_live_agents();
                    tx_put_run(&tx, conversation_id, &run_id, &mut record).await?;
                }
                Ok(())
            },
            cx,
        )
        .await?;
    Ok(true)
}
