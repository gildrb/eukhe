//! `rlm.query_batch` (the kernel's `rlm.query` and `rlm.query_batch`): the
//! Recursive Language Model's sub-call. Each query is one model call with
//! no tools, no session and no transcript entry; its answer goes back to
//! the cell as a value and reaches the conversation only if the cell
//! prints it.
//!
//! A batch is admitted whole by the compiled core (`eukhe_bend::rules::
//! rlm_query::plan`, laws `laws/rlm_query.bend`): the session's
//! `rlm.queryBudgetBytes` bounds the input bytes its queries send in all,
//! and `rlm.queryConcurrency` bounds the queries in flight at once across
//! every batch of the session. An admitted batch runs in the planned
//! waves, one after another, each wave's calls at once. A refused batch
//! runs nothing and its refusal text goes back as a value.
//!
//! The calls go through the session's model collection, so each takes an
//! interactive provider slot like the turn it serves (the turn waits on the
//! cell): the chat-memory compactor yields to them (H3.1), and the cap
//! bounds how many slots one session's queries hold, so another session's
//! request waits behind at most that many (H3.4). Each call's usage counts
//! into the calling `ipython` call's usage, hence the session's. An answer
//! cut by `max_bytes` is cut at a character boundary the core picks
//! (`rlm_query::cut`).

use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use anyhow::{anyhow, bail};
use eukhe_ai::types::SimpleStreamOptions;
use eukhe_bend::rules::rlm_query::{self, Cut, Plan, PlanFacts};
use eukhe_chord::context::AbortController;
use eukhe_durable::harness::types::ToolExecutionApi;
use eukhe_types::model_roles::ModelRole;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, Context, Message, StopReason, TextContent,
    ThinkingLevel, UserContent, UserContentBlock, UserMessage,
};
use futures::future::join_all;
use futures::FutureExt;
use serde_json::{json, Value};

use super::history::serve;
use super::{background, now_millis, RlmRuntime};
use crate::kernel::rlm_runtime::normalize_requested_rlm_subagent_thinking_level;
use crate::models::roles::role_model;
use crate::models::{model_allowed, ModelAllowlistRefusal};

const REQUEST: &str = "rlm.query_batch";

/// The keys one call of a batch may carry.
const CALL_KEYS: [&str; 5] = ["prompt", "context", "model", "thinking", "max_bytes"];

/// What the session's queries hold: the slots of the batches running now
/// and the input bytes sent so far (this worker's run of the session).
#[derive(Debug, Default)]
pub(crate) struct QueryLedger {
    state: Mutex<Ledger>,
}

#[derive(Debug, Default)]
struct Ledger {
    running: u64,
    used: u64,
}

impl QueryLedger {
    fn lock(&self) -> MutexGuard<'_, Ledger> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }
}

/// The slots one admitted batch holds; dropping it frees them.
struct Slots {
    runtime: Arc<RlmRuntime>,
    width: u64,
}

impl Drop for Slots {
    fn drop(&mut self) {
        let mut ledger = self.runtime.queries.lock();
        ledger.running = ledger.running.saturating_sub(self.width);
    }
}

/// Cancels a call's request when the call is dropped (a cancelled cell):
/// the provider streams on a task of its own, which only the signal stops.
struct AbortOnDrop(AbortController);

impl Drop for AbortOnDrop {
    fn drop(&mut self) {
        self.0.abort(None);
    }
}

/// One call of a batch, as the kernel sent it.
struct QueryCall {
    prompt: String,
    context: Option<Arc<str>>,
    model: Option<String>,
    thinking: Option<ThinkingLevel>,
    /// The call asked for thinking `off`: its reasoning is turned off.
    thinking_off: bool,
    max_bytes: Option<u64>,
}

impl QueryCall {
    /// The input bytes the call sends.
    fn size(&self) -> u64 {
        let context = self.context.as_deref().map_or(0, str::len);
        u64::try_from(self.prompt.len() + context).unwrap_or(u64::MAX)
    }
}

pub(super) fn register(runtime: &Arc<RlmRuntime>) {
    runtime.deps.host_requests.register(
        "rlm.query_batch",
        serve(runtime, |runtime, call| {
            async move {
                let api = call.call.clone().ok_or_else(|| {
                    anyhow!("rlm.query runs inside an ipython cell: this request has no running cell to count its usage on")
                })?;
                query_batch(runtime, api, &call.data).await
            }
            .boxed()
        }),
    );
}

fn optional_text(
    call: &serde_json::Map<String, Value>,
    key: &str,
    index: usize,
) -> anyhow::Result<Option<String>> {
    match call.get(key) {
        None | Some(Value::Null) => Ok(None),
        Some(Value::String(text)) => Ok(Some(text.clone())),
        Some(_) => bail!("{REQUEST} call {index}: {key} must be a string"),
    }
}

fn positive(value: Option<&Value>, what: &str) -> anyhow::Result<Option<u64>> {
    match value {
        None | Some(Value::Null) => Ok(None),
        Some(value) => match value.as_u64() {
            Some(number) if number >= 1 => Ok(Some(number)),
            Some(_) | None => bail!("{what} must be a positive integer"),
        },
    }
}

/// The calls of a batch payload `{calls, contexts, concurrency?}`.
fn read_calls(data: &Value) -> anyhow::Result<Vec<QueryCall>> {
    let contexts: Vec<Arc<str>> = match data.get("contexts") {
        None | Some(Value::Null) => Vec::new(),
        Some(Value::Array(contexts)) => contexts
            .iter()
            .map(|context| {
                context
                    .as_str()
                    .map(Arc::from)
                    .ok_or_else(|| anyhow!("{REQUEST} contexts must be strings"))
            })
            .collect::<anyhow::Result<_>>()?,
        Some(_) => bail!("{REQUEST} contexts must be a list of strings"),
    };
    let Some(calls) = data.get("calls").and_then(Value::as_array) else {
        bail!("{REQUEST} calls must be a non-empty list");
    };
    if calls.is_empty() {
        bail!("{REQUEST} calls must be a non-empty list");
    }
    calls
        .iter()
        .enumerate()
        .map(|(index, call)| {
            let Some(call) = call.as_object() else {
                bail!("{REQUEST} call {index} must be an object");
            };
            let unknown: Vec<&str> = call
                .keys()
                .map(String::as_str)
                .filter(|key| !CALL_KEYS.contains(key))
                .collect();
            if !unknown.is_empty() {
                bail!(
                    "{REQUEST} call {index}: unsupported keys: {}",
                    unknown.join(", ")
                );
            }
            let Some(prompt) = optional_text(call, "prompt", index)? else {
                bail!("{REQUEST} call {index}: prompt must be a string");
            };
            let context = match call.get("context") {
                None | Some(Value::Null) => None,
                Some(at) => Some(
                    at.as_u64()
                        .and_then(|at| contexts.get(usize::try_from(at).ok()?))
                        .cloned()
                        .ok_or_else(|| {
                            anyhow!("{REQUEST} call {index}: context must index contexts")
                        })?,
                ),
            };
            let thinking = optional_text(call, "thinking", index)?;
            let thinking =
                normalize_requested_rlm_subagent_thinking_level(thinking.as_deref(), "rlm.query")?;
            Ok(QueryCall {
                prompt,
                context,
                model: optional_text(call, "model", index)?,
                thinking: thinking.and_then(ThinkingLevel::parse),
                thinking_off: thinking == Some("off"),
                max_bytes: positive(
                    call.get("max_bytes"),
                    &format!("{REQUEST} call {index}: max_bytes"),
                )?,
            })
        })
        .collect()
}

#[tracing::instrument(name = "rlm.query_batch", skip_all)]
async fn query_batch(
    runtime: Arc<RlmRuntime>,
    api: Arc<dyn ToolExecutionApi>,
    data: &Value,
) -> anyhow::Result<Value> {
    let calls = read_calls(data)?;
    let width = positive(data.get("concurrency"), &format!("{REQUEST} concurrency"))?.unwrap_or(0);
    let settings = runtime.deps.settings.manager();
    let sizes: Vec<u64> = calls.iter().map(QueryCall::size).collect();
    let (waves, slots) = {
        let mut ledger = runtime.queries.lock();
        let plan = rlm_query::plan(&PlanFacts {
            running: ledger.running,
            cap: settings.get_rlm_query_concurrency(),
            width,
            budget: settings.get_rlm_query_budget_bytes(),
            used: ledger.used,
            sizes: &sizes,
        })?;
        match plan {
            Plan::Refuse(text) => return Ok(json!({ "refused": text })),
            Plan::Admit { waves } => {
                let held = waves.iter().copied().max().unwrap_or(0);
                let held = u64::try_from(held).unwrap_or(u64::MAX);
                ledger.running = ledger.running.saturating_add(held);
                ledger.used = sizes
                    .iter()
                    .fold(ledger.used, |used, size| used.saturating_add(*size));
                (
                    waves,
                    Slots {
                        runtime: Arc::clone(&runtime),
                        width: held,
                    },
                )
            }
        }
    };
    let cx = background();
    let session_model = api
        .agent(&cx)
        .await?
        .model
        .as_ref()
        .map(|model| format!("{}/{}", model.provider, model.model_id));
    // The query role's model (`rlm.queryModel`, else `modelRoles.all`),
    // else the session's.
    let default_model = role_model(settings.cvars(), ModelRole::Query)
        .selector
        .or(session_model);
    let planned = calls.len();
    let mut calls = calls.into_iter();
    let mut results = Vec::with_capacity(planned);
    for wave in waves {
        let answers = join_all(
            calls
                .by_ref()
                .take(wave)
                .map(|call| run_call(&runtime, &*api, call, default_model.as_deref())),
        )
        .await;
        for answer in answers {
            results.push(answer?);
        }
    }
    drop(slots);
    if results.len() != planned || calls.next().is_some() {
        bail!(
            "the compiled core planned {} of {planned} rlm.query calls",
            results.len()
        );
    }
    Ok(json!({ "results": results }))
}

/// Why an `rlm.query` has no model to ask; its text is the call's error.
#[derive(Debug, thiserror::Error)]
enum ModelError {
    #[error("rlm.query has no model: the session has none and rlm.queryModel is unset; pass model=\"provider/id\"")]
    Unset,
    #[error("rlm.query model {0:?} is not available: pass an exact provider/id selector from rlm.find_models()")]
    Unavailable(String),
    #[error(transparent)]
    Blocked(#[from] ModelAllowlistRefusal),
}

/// The catalog model an `rlm.query` asks: `selector` (exact
/// `provider/id`), checked against `allowedModels`.
fn resolve_model(
    runtime: &RlmRuntime,
    selector: Option<&str>,
) -> Result<eukhe_types::pi_ai::Model, ModelError> {
    let selector = selector.ok_or(ModelError::Unset)?;
    let model = selector
        .split_once('/')
        .and_then(|(provider, id)| runtime.deps.models.get_model(provider, id))
        .ok_or_else(|| ModelError::Unavailable(selector.to_owned()))?;
    if let Some(allowlist) = runtime.deps.settings.manager().get_allowed_models() {
        if !model_allowed(selector, &allowlist) {
            return Err(ModelAllowlistRefusal {
                selector: selector.to_owned(),
            }
            .into());
        }
    }
    Ok(model)
}

/// One query: its answer `{text, truncated, model}`, or `{error}` when it
/// produced none. Fails only when its usage cannot be counted.
async fn run_call(
    runtime: &RlmRuntime,
    api: &dyn ToolExecutionApi,
    call: QueryCall,
    default_model: Option<&str>,
) -> anyhow::Result<Value> {
    let model = match resolve_model(runtime, call.model.as_deref().or(default_model)) {
        Ok(model) => model,
        Err(error) => return Ok(json!({ "error": error.to_string() })),
    };
    let mut blocks = Vec::with_capacity(2);
    if let Some(context) = &call.context {
        blocks.push(UserContentBlock::Text(TextContent::new(format!(
            "<context>\n{context}\n</context>"
        ))));
    }
    blocks.push(UserContentBlock::Text(TextContent::new(call.prompt)));
    let context = Context {
        system_prompt: None,
        messages: vec![Message::User(UserMessage {
            content: UserContent::Blocks(blocks),
            timestamp: now_millis(),
        })],
        tools: None,
    };
    let abort = AbortOnDrop(AbortController::new());
    let options = SimpleStreamOptions {
        reasoning: call.thinking,
        disable_reasoning: call.thinking_off,
        thinking_budgets: runtime.deps.settings.manager().get_thinking_budgets(),
        ..SimpleStreamOptions::default()
    };
    let mut options: eukhe_ai::models::ModelsSimpleStreamOptions = options.into();
    options.options.stream.request.signal = Some(abort.0.signal());
    let reply = runtime
        .deps
        .models
        .complete_simple(&model, context, options)
        .await;
    drop(abort);
    api.usage(reply.usage)?;
    Ok(answer(&reply, call.max_bytes))
}

/// The value of a reply: its text (cut at `max_bytes` by the core) with
/// whether it was cut (by `max_bytes`, or by the model's output limit), or
/// the error of a reply that has no answer.
fn answer(reply: &AssistantMessage, max_bytes: Option<u64>) -> Value {
    let complete = match reply.stop_reason {
        StopReason::Stop | StopReason::ToolUse => true,
        StopReason::Length => false,
        StopReason::Error | StopReason::Aborted => {
            let error = reply
                .error_message
                .clone()
                .unwrap_or_else(|| format!("rlm.query call ended {}", reply.stop_reason.as_str()));
            return json!({ "error": error });
        }
        StopReason::Pending | StopReason::Deferred => {
            return json!({
                "error": "rlm.query got a deferred response, which it cannot wait for"
            });
        }
    };
    let mut text: String = reply
        .content
        .iter()
        .filter_map(|block| match block {
            AssistantContentBlock::Text(text) => Some(text.text.as_str()),
            AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => None,
        })
        .collect();
    let cut = match max_bytes {
        Some(max_bytes) => match rlm_query::cut(max_bytes, &text) {
            Cut::Fits => false,
            Cut::At(at) => {
                text.truncate(at);
                true
            }
        },
        None => false,
    };
    json!({
        "text": text,
        "truncated": cut || !complete,
        "model": format!("{}/{}", reply.provider, reply.model),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_batch_payload_reads_its_shared_contexts() {
        let calls = read_calls(&json!({
            "calls": [
                { "prompt": "a", "context": 0, "max_bytes": 3 },
                { "prompt": "bb", "context": 0, "thinking": "low", "model": "p/m" },
                { "prompt": "c" },
            ],
            "contexts": ["héllo"],
        }))
        .unwrap();
        assert_eq!(
            calls.iter().map(QueryCall::size).collect::<Vec<_>>(),
            vec![7, 8, 1]
        );
        assert_eq!(
            (
                calls[0].max_bytes,
                calls[1].thinking,
                calls[1].model.as_deref()
            ),
            (Some(3), Some(ThinkingLevel::Low), Some("p/m"))
        );
        assert_eq!(
            read_calls(&json!({ "calls": [{ "prompt": "a", "context": 1 }], "contexts": [] }))
                .err()
                .map(|error| error.to_string()),
            Some("rlm.query_batch call 0: context must index contexts".to_owned())
        );
        assert_eq!(
            read_calls(&json!({ "calls": [{ "prompt": "a", "colour": 1 }] }))
                .err()
                .map(|error| error.to_string()),
            Some("rlm.query_batch call 0: unsupported keys: colour".to_owned())
        );
    }
}
