//! The RPC command surface, the budget: `get_budget`, `set_budget`,
//! `add_budget` and `audit_budget` over the live session's budget gate,
//! with the daemon wire's reply shapes ([`BudgetReply`],
//! [`BudgetAuditReply`]). Each change of the budget also goes out as one
//! `budget_update` frame (the event pump's budget watch).

use std::sync::Arc;

use eukhe_core::durable::budget::BudgetGate;
use eukhe_types::budget::{BudgetAmounts, RunLimits};
use eukhe_types::daemon::{BudgetAudit, BudgetAuditReply, BudgetReply};
use serde_json::Value;

use super::commands::RpcState;
use super::error::RpcCommandError;
use super::protocol::ResponseData;
use super::reads::{is_busy, rpc_context};

/// `get_budget`: the session's budget, `budget` null without one.
///
/// # Errors
///
/// The ledger read did not finish.
pub(crate) async fn get_budget(state: &Arc<RpcState>) -> Result<ResponseData, RpcCommandError> {
    reply(state, |gate| {
        Ok::<_, eukhe_core::durable::budget::BudgetError>(BudgetReply {
            budget: gate.report(),
        })
    })
    .await
}

/// `set_budget { limits }`: the limits of the session's running run, or,
/// while it runs nothing, of its next run; a number or `unlimited` per
/// dimension.
///
/// # Errors
///
/// A missing `limits`, the ledger's refusal or failure.
pub(crate) async fn set_budget(
    state: &Arc<RpcState>,
    payload: &Value,
) -> Result<ResponseData, RpcCommandError> {
    let limits: RunLimits = field("set_budget", payload, "limits")?;
    let live = run_live(state).await?;
    reply(state, move |gate| {
        let report = if live {
            gate.set(limits).map_err(RpcCommandError::from)
        } else {
            gate.set_next(limits).map_err(RpcCommandError::from)
        };
        report.map(|report| BudgetReply {
            budget: Some(report),
        })
    })
    .await
}

/// `add_budget { amounts }`: more budget (`timeMs` moves the deadline) for
/// the session's running run, or, while it runs nothing, for its next
/// run; a session without a budget gets `amounts` as its budget.
///
/// # Errors
///
/// A missing `amounts`, the ledger's refusal or failure.
pub(crate) async fn add_budget(
    state: &Arc<RpcState>,
    payload: &Value,
) -> Result<ResponseData, RpcCommandError> {
    let amounts: BudgetAmounts = field("add_budget", payload, "amounts")?;
    let live = run_live(state).await?;
    reply(state, move |gate| {
        let report = if live {
            gate.add(amounts).map_err(RpcCommandError::from)
        } else {
            gate.add_next(amounts).map_err(RpcCommandError::from)
        };
        report.map(|report| BudgetReply {
            budget: Some(report),
        })
    })
    .await
}

/// Whether a run is live on the session's main conversation: limits set
/// or added meanwhile are its own, else the next run's.
async fn run_live(state: &Arc<RpcState>) -> Result<bool, RpcCommandError> {
    let handle = state.session.handle().await;
    let session = &handle.session;
    Ok(is_busy(session.harness(), session.main().id(), &rpc_context()).await?)
}

/// `audit_budget`: the ledger replayed record by record, and its settled
/// spends against the total it reports.
///
/// # Errors
///
/// The session has no budget, or the ledger does not read.
pub(crate) async fn audit_budget(state: &Arc<RpcState>) -> Result<ResponseData, RpcCommandError> {
    reply(state, |gate| {
        gate.audit().map(|audit| BudgetAuditReply {
            audit: BudgetAudit {
                records: audit.records,
                settled: audit.settled,
                spent: audit.spent,
                exact: audit.exact(),
                first_mismatch: audit.first_mismatch,
            },
        })
    })
    .await
}

/// What `call` reads from or does to the live session's budget, on the
/// blocking pool (ledger file IO), as the response data.
async fn reply<T: serde::Serialize + Send + 'static, E: Send + 'static>(
    state: &Arc<RpcState>,
    call: impl FnOnce(&BudgetGate) -> Result<T, E> + Send + 'static,
) -> Result<ResponseData, RpcCommandError>
where
    RpcCommandError: From<E>,
{
    let gate = state.session.session().await.budget();
    let reply = tokio::task::spawn_blocking(move || call(&gate)).await??;
    Ok(ResponseData::Present(serde_json::to_value(reply)?))
}

/// The field `key` of the budget command `command`.
fn field<T: serde::de::DeserializeOwned>(
    command: &str,
    payload: &Value,
    key: &'static str,
) -> Result<T, RpcCommandError> {
    payload
        .get(key)
        .and_then(|value| serde_json::from_value(value.clone()).ok())
        .ok_or_else(|| RpcCommandError::missing(command, key))
}
