//! `eukhe.workflow`: dynamic workflows. The `workflow` tool runs a
//! model-written JavaScript orchestration script on the code mode sandbox
//! (`eukhe_durable::codemode`): deterministic, journaled, and replayed
//! after a worker restart. The script's `agent()` calls spawn silent RLM
//! children (`eukhe.children`), at most the run size's concurrency at once
//! and its `max_agents` in total; each run's progress lives in the
//! `eukhe.workflow.runs` document the `/workflows` view reads.

pub(crate) mod command;
mod globals;
mod meta;
mod run_doc;
mod schema;
mod size;

#[cfg(test)]
mod tests;

use std::sync::Arc;

use eukhe_ai::typebox::{Options, TSchema, Type};
use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_chord::json::JsonValue;
use eukhe_durable::codemode::sandbox::{CodemodeSandbox, CodemodeSandboxOptions};
use eukhe_durable::codemode::{
    run_codemode_source, ClassifierDefault, CodemodeModels, CodemodeToolOptions,
};
use eukhe_durable::harness::define::{define_extension, define_tool};
use eukhe_durable::harness::types::{
    Extension, OutputRetain, ToolCaller, ToolExecutionApi, ToolExecutionApiExt,
    ToolExecutionResult, ToolRegistration, ToolReplay,
};
use eukhe_durable::harness::{Harness, OutputLimits, Truncation};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::{ConversationId, TaskId};
use eukhe_types::pi_ai::{JsonValue as PiJsonValue, TextContent, UserContentBlock};
use eukhe_types::workflow::{WorkflowAgentStatus, WorkflowRunState, WorkflowSize};

pub use run_doc::snapshots;
pub use size::effective_limits;

use super::deps::{HarnessCell, HostDeps};
use super::settings::EukheSettings;
use globals::WorkflowServices;
use meta::parse_script;
use run_doc::{read_runs, tx_put_run, tx_run, RunRecord};

/// The extension name.
pub const EXTENSION_NAME: &str = "eukhe.workflow";
/// The tool name.
pub const WORKFLOW_TOOL_NAME: &str = "workflow";
/// Version of the script the tool builds (prelude and header): a call
/// started by another version is not replayed by this one.
pub const WORKFLOW_MODULE_VERSION: u32 = 1;

const WORKFLOW_DESCRIPTION: &str = include_str!("../../prompts/layers/workflow.md");
const PRELUDE: &str = include_str!("prelude.js");
const NO_RUNTIME: &str =
    "dynamic workflows need the eukhe daemon: this session has no subagent runtime";

/// Outputs are the script's own; the limits only stop a runaway.
const OUTPUT_LIMITS: OutputLimits = OutputLimits {
    max_bytes: 1024 * 1024,
    max_lines: 20_000,
    retain: OutputRetain::Head,
};

struct Shared {
    options: Arc<CodemodeToolOptions>,
    harness: HarnessCell,
    settings: Arc<EukheSettings>,
    has_runtime: bool,
}

/// The `eukhe.workflow` extension of a session: the `workflow` tool.
#[must_use]
pub fn extension(deps: &Arc<HostDeps>) -> Arc<Extension> {
    let services = Arc::new(WorkflowServices {
        host_requests: deps.host_requests.clone(),
    });
    let options = CodemodeToolOptions {
        models: CodemodeModels::Excluded,
        classifier: ClassifierDefault::Unset,
        globals: globals::globals(&services),
        ..CodemodeToolOptions::new(CodemodeSandbox::new(CodemodeSandboxOptions::default()))
    };
    let shared = Arc::new(Shared {
        options: Arc::new(options),
        harness: deps.harness.clone(),
        settings: Arc::clone(&deps.settings),
        has_runtime: deps.children.is_some(),
    });
    define_extension(Extension {
        tools: vec![workflow_tool(shared)],
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
            async move { execute(&shared, &args, api, cx).await }
        },
    );
    tool.truncation = Truncation::On(OUTPUT_LIMITS);
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
/// landed. A rerun builds the same
/// source from the run's record.
fn source(record: &RunRecord, request: &str, body: &str) -> String {
    let request = serde_json::Value::String(request.to_owned());
    format!(
        "// eukhe workflow v{WORKFLOW_MODULE_VERSION}\nconst args = {request};\nconst __wfLimits = Object.freeze({{ size: \"{size}\", concurrency: {concurrency}, maxAgents: {max_agents} }});\n{PRELUDE}\nconst __wfResult = await (async () => {{\n{body}\n}})();\nawait __wfSettled();\nreturn __wfResult;",
        size = record.size.as_str(),
        concurrency = record.concurrency.max(1),
        max_agents = record.max_agents,
    )
}

async fn execute(
    shared: &Shared,
    args: &PiJsonValue,
    api: Arc<dyn ToolExecutionApi>,
    cx: Context,
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
    let run_id = api.task_id().to_string();
    let conversation_id = api.conversation_id();
    let record = {
        let (run_id, meta) = (run_id.clone(), parsed.meta.clone());
        api.commit(
            move |tx| async move {
                if let Some(existing) = tx_run(&tx, conversation_id, &run_id).await? {
                    return Ok(existing);
                }
                if let Some(from) = &resume {
                    if tx_run(&tx, conversation_id, from).await?.is_none() {
                        return Err(SessionError::type_error(format!(
                            "workflow resume: no run {from} in this conversation"
                        )));
                    }
                }
                let record = RunRecord::start(meta, size, limits, now_ms(), resume);
                tx_put_run(&tx, conversation_id, &run_id, &record).await?;
                Ok(record)
            },
            &cx,
        )
        .await?
    };
    let code = source(&record, &request, &parsed.body);
    let outcome = run_codemode_source(
        Arc::clone(&shared.options),
        Arc::clone(&api),
        cx.clone(),
        &code,
    )
    .await;
    let state = match &outcome {
        _ if cx.aborted() => WorkflowRunState::Cancelled,
        Err(error) => WorkflowRunState::Failed {
            error: error.to_string(),
        },
        Ok(result) if result.is_error == Some(true) => WorkflowRunState::Failed {
            error: output_text(result),
        },
        Ok(_) => WorkflowRunState::Done,
    };
    if state == WorkflowRunState::Cancelled {
        if let Some(harness) = shared.harness.get() {
            cancel_agents(&harness, conversation_id, &run_id, &BACKGROUND_CONTEXT)
                .await
                .map_err(|error| SessionError::error(format!("{error:#}")))?;
        }
    }
    let ended = state.clone();
    api.commit(
        move |tx| async move {
            if let Some(mut record) = tx_run(&tx, conversation_id, &run_id).await? {
                if !record.state.is_terminal() {
                    record.state = ended;
                }
                tx_put_run(&tx, conversation_id, &run_id, &record).await?;
            }
            Ok(())
        },
        &BACKGROUND_CONTEXT,
    )
    .await?;
    let mut result = outcome?;
    let header = format!(
        "workflow run {} ({}): {}",
        api.task_id(),
        record.meta.name,
        match &state {
            WorkflowRunState::Running => "running",
            WorkflowRunState::Done => "done",
            WorkflowRunState::Failed { .. } => "failed",
            WorkflowRunState::Cancelled => "cancelled",
        }
    );
    let mut output = vec![UserContentBlock::Text(TextContent::new(header))];
    output.extend(result.output.take().unwrap_or_default());
    result.output = Some(output);
    Ok(result)
}

fn output_text(result: &ToolExecutionResult) -> String {
    result
        .output
        .iter()
        .flatten()
        .filter_map(|block| match block {
            UserContentBlock::Text(text) => Some(text.text.as_str()),
            UserContentBlock::Image(_) => None,
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Cancel the live agents of run `run_id`.
async fn cancel_agents(
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
        if let Some(name) = &agent.child_name {
            super::children::cancel_child(harness, conversation_id, name, cx).await?;
        }
    }
    Ok(())
}

/// Cancel the run `run_id` of `conversation_id`: abort its `workflow`
/// call, cancel its live agents, and mark it cancelled. `false` when no
/// running run has that id.
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
    let task: u64 = run_id
        .parse()
        .map_err(|_| anyhow::anyhow!("workflow run id {run_id} is not a task id"))?;
    harness
        .abort_task(TaskId::<JsonValue>::from_number(task).erase(), cx)
        .await?;
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
                    record.state = WorkflowRunState::Cancelled;
                    for agent in record.agents.values_mut() {
                        if !agent.status.is_terminal() {
                            agent.status = WorkflowAgentStatus::Cancelled;
                        }
                    }
                    tx_put_run(&tx, conversation_id, &run_id, &record).await?;
                }
                Ok(())
            },
            cx,
        )
        .await?;
    Ok(true)
}
