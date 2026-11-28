//! Writing batches for kernel callers (the factory executor), under the
//! same rules as a workflow's writing `agent()` calls ([`super::batch`]):
//! each agent names its files; the harness builds the balanced tree and
//! runs its integrators. The caller does the session's IO itself
//! (`rlm.tree_facts`, `rlm.tree_lend`, `rlm.run`, `rlm.answer`,
//! `rlm.tree_return`); these requests keep the batch:
//! - `tree.batch {key, facts, agents: [{scope}]}`: admit the agents as one
//!   batch, all or none; `{key, nodes, leaves: [{kwargs, head}]}`: the
//!   nodes to lend, and per agent the spawn kwargs (`node`, `budget`) and
//!   the task line that names its files;
//! - `tree.batch_end {key, ordinal, state}`: record agent `ordinal`'s end
//!   from its settled `rlm.answer` state; `{conflicts, settled}`;
//! - `tree.batch_drop {key}`: drop a batch whose nodes were refused.

use std::sync::Arc;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_durable::harness::types::{ToolExecutionApi, ToolExecutionApiExt};
use futures::FutureExt;
use serde_json::{json, Value};

use super::batch::{crown, place, Outcome, NEEDS_FILES};
use super::batch_doc::{tx_batches, tx_end, tx_put_batch, tx_remove_batch};
use super::globals::{access_line, Access};
use super::tree;
use crate::durable::deps::{HostCall, HostRequestRegistry};

/// The scopes of a `tree.batch` request's agents, in order.
fn scopes(data: &Value) -> anyhow::Result<Vec<Vec<String>>> {
    data.get("agents")
        .and_then(Value::as_array)
        .filter(|agents| !agents.is_empty())
        .ok_or_else(|| anyhow::anyhow!("tree.batch: agents must be a non-empty list"))?
        .iter()
        .map(|agent| {
            agent
                .get("scope")
                .and_then(Value::as_array)
                .filter(|paths| !paths.is_empty())
                .and_then(|paths| {
                    paths
                        .iter()
                        .map(|path| {
                            path.as_str()
                                .filter(|path| !path.trim().is_empty())
                                .map(str::to_owned)
                        })
                        .collect::<Option<Vec<_>>>()
                })
                .ok_or_else(|| anyhow::anyhow!(NEEDS_FILES))
        })
        .collect()
}

/// The batch key of a kernel caller's `key`.
fn batch_key(data: &Value) -> anyhow::Result<String> {
    data.get("key")
        .and_then(Value::as_str)
        .filter(|key| !key.is_empty())
        .map(|key| format!("kernel:{key}"))
        .ok_or_else(|| anyhow::anyhow!("tree.batch: key must be a non-empty string"))
}

fn caller(call: &HostCall) -> anyhow::Result<Arc<dyn ToolExecutionApi>> {
    call.call
        .clone()
        .ok_or_else(|| anyhow::anyhow!("tree.batch runs only from a python tool call"))
}

/// `tree.batch`: see the module doc.
async fn admit(call: HostCall) -> anyhow::Result<Value> {
    let api = caller(&call)?;
    let key = batch_key(&call.data)?;
    let scopes = scopes(&call.data)?;
    let facts = tree::facts(call.data.get("facts").unwrap_or(&Value::Null))?;
    let agents: Vec<(u32, Vec<String>)> = (1..).zip(scopes.iter().cloned()).collect();
    let conversation_id = api.conversation_id();
    let stored = key.clone();
    let batch = api
        .commit(
            move |tx| async move {
                let batches = tx_batches(&tx, conversation_id).await?;
                if batches.batches.contains_key(&stored) {
                    return Ok(Err(format!("tree.batch: batch {stored} exists")));
                }
                let batch = match batches.admit(&facts, &agents) {
                    Ok(batch) => batch,
                    Err(refusal) => return Ok(Err(refusal.to_string())),
                };
                tx_put_batch(&tx, conversation_id, &stored, &batch).await?;
                Ok(Ok(batch))
            },
            &BACKGROUND_CONTEXT,
        )
        .await?
        .map_err(anyhow::Error::msg)?;
    let crowned = crown(&batch)?;
    let leaves = (1_u32..)
        .zip(scopes)
        .map(|(ordinal, scope)| {
            let leaf = place(&batch, &crowned, ordinal)
                .ok_or_else(|| anyhow::anyhow!("tree.batch: agent {ordinal} has no place"))?;
            Ok(json!({
                "kwargs": tree::leaf_kwargs(&batch, &leaf),
                "head": access_line(&Access::Writes(scope)),
            }))
        })
        .collect::<anyhow::Result<Vec<_>>>()?;
    Ok(json!({ "key": key, "nodes": tree::nodes(batch.leaves.len()), "leaves": leaves }))
}

/// `tree.batch_end`: see the module doc.
async fn end(call: HostCall) -> anyhow::Result<Value> {
    let api = caller(&call)?;
    let key = batch_key(&call.data)?;
    let ordinal = call
        .data
        .get("ordinal")
        .and_then(Value::as_u64)
        .and_then(|ordinal| u32::try_from(ordinal).ok())
        .ok_or_else(|| anyhow::anyhow!("tree.batch_end: ordinal must be a whole number"))?;
    let state = call.data.get("state").unwrap_or(&Value::Null);
    if state.get("settled") != Some(&Value::Bool(true)) {
        anyhow::bail!("tree.batch_end: agent {ordinal} has not settled");
    }
    let outcome = match state.get("status").and_then(Value::as_str) {
        Some("done") => Outcome::Finished,
        Some(_) | None => Outcome::Failed,
    };
    let tree::Written { patch, conflicts } = tree::written(state);
    let conversation_id = api.conversation_id();
    let settled = api
        .commit(
            move |tx| async move { tx_end(&tx, conversation_id, &key, ordinal, outcome, patch).await },
            &BACKGROUND_CONTEXT,
        )
        .await?;
    Ok(json!({ "conflicts": conflicts, "settled": settled }))
}

/// `tree.batch_drop`: see the module doc.
async fn drop_batch(call: HostCall) -> anyhow::Result<Value> {
    let api = caller(&call)?;
    let key = batch_key(&call.data)?;
    let conversation_id = api.conversation_id();
    api.commit(
        move |tx| async move { tx_remove_batch(&tx, conversation_id, &key).await },
        &BACKGROUND_CONTEXT,
    )
    .await?;
    Ok(Value::Null)
}

/// Register `tree.batch`, `tree.batch_end` and `tree.batch_drop` onto
/// `registry`.
pub(super) fn register(registry: &HostRequestRegistry) {
    registry.register("tree.batch", Arc::new(|call: HostCall| admit(call).boxed()));
    registry.register(
        "tree.batch_end",
        Arc::new(|call: HostCall| end(call).boxed()),
    );
    registry.register(
        "tree.batch_drop",
        Arc::new(|call: HostCall| drop_batch(call).boxed()),
    );
}
