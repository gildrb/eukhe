//! The session's budget on the wire: `get_budget`, `set_budget`,
//! `add_budget` and `audit_budget` answer from the session's budget gate
//! (`eukhe_core::durable::budget`: ledger file IO, so each call runs on the
//! blocking pool), and each change of the budget goes out as one
//! `budget_update` session event. The last report sent stays on the session
//! core, where the attach snapshot reads its `state.budget`. A create (and
//! a fork that replaces the session) gives the session its budget before
//! its first turn ([`CreateBudget`]).

use std::sync::{Arc, Mutex};

use eukhe_core::durable::budget::{BudgetError, BudgetGate};
use eukhe_types::budget::{BudgetAmounts, BudgetLimits};
use eukhe_types::daemon::{BudgetAudit, BudgetAuditReply, BudgetReply, SessionEvent};
use serde_json::Value;

use super::{emit_event_locked, EventPump, HostedSession, SessionCore, Worker};
use crate::protocol::{response_failure, response_success, DaemonResponse};

/// What a create does to its session's budget before the first turn.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CreateBudget {
    /// Nothing: the session spends from the budget its ledger (or its
    /// parent's) gives it, if any.
    Keep,
    /// The create config's `budget`: the session's limits. A session that
    /// has a budget keeps its own.
    Set(BudgetLimits),
    /// A fork of the session `source`: it draws from the source's budget,
    /// a shared member of its account below the source. A source without a
    /// budget leaves the fork without one.
    Share { source: String },
}

/// Apply `budget` to the session `hosted` (ledger file IO, on the blocking
/// pool).
///
/// # Errors
///
/// The ledger's failure (its text): the session would spend without the
/// budget its creator gave it.
pub(crate) async fn apply_create_budget(
    hosted: &HostedSession,
    budget: &CreateBudget,
) -> Result<(), String> {
    if *budget == CreateBudget::Keep {
        return Ok(());
    }
    let gate = hosted
        .session()
        .map_err(|error| error.to_string())?
        .budget();
    let budget = budget.clone();
    tokio::task::spawn_blocking(move || match budget {
        CreateBudget::Keep => Ok(()),
        CreateBudget::Set(limits) => match gate.set(limits) {
            Ok(_) | Err(BudgetError::AlreadyOpen(_)) => Ok(()),
            Err(error) => Err(error),
        },
        CreateBudget::Share { source } => match gate.ledger().join(&source) {
            // A source without a budget; a fork that already draws from it
            // or has a budget of its own (a reopen).
            Ok(_) | Err(BudgetError::NoBudget(_) | BudgetError::AlreadyOpen(_)) => Ok(()),
            Err(error) => Err(error),
        },
    })
    .await
    .map_err(|error| error.to_string())?
    .map_err(|error| error.to_string())
}

impl Worker {
    /// Follow the budget of `hosted` (the installed session; `None` for
    /// none): the previous forwarder stops, and a new one sends the
    /// session's budget, then each change of it, as `budget_update` events
    /// until the next follow.
    pub(crate) fn follow_budget(&self, hosted: Option<&HostedSession>) {
        let epoch = {
            let mut core = self
                .core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            core.budget_epoch += 1;
            core.budget_epoch
        };
        let task = hosted
            .and_then(|hosted| hosted.session().ok())
            .map(|session| {
                tokio::spawn(forward_budget(
                    session.budget(),
                    epoch,
                    Arc::clone(&self.core),
                    Arc::clone(&self.events),
                ))
            });
        let previous = std::mem::replace(
            &mut *self
                .budget_updates
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner),
            task,
        );
        if let Some(previous) = previous {
            previous.abort();
        }
    }

    /// `get_budget` (Rust-native): the session's budget, `budget` null for
    /// a session without one.
    pub(crate) async fn handle_get_budget(&self) -> DaemonResponse {
        self.answer_budget("get_budget", |gate| {
            Ok(BudgetReply {
                budget: gate.report(),
            })
        })
        .await
    }

    /// `set_budget { limits }` (Rust-native): the budget of a root session
    /// that has none. A session that has one answers the ledger's refusal.
    pub(crate) async fn handle_set_budget(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "set_budget";
        let limits: BudgetLimits = match field(COMMAND, payload, "limits") {
            Ok(limits) => limits,
            Err(response) => return response,
        };
        self.answer_budget(COMMAND, move |gate| {
            gate.set(limits).map(|report| BudgetReply {
                budget: Some(report),
            })
        })
        .await
    }

    /// `add_budget { amounts }` (Rust-native): `amounts` more budget; a
    /// session without a budget gets them as its budget.
    pub(crate) async fn handle_add_budget(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "add_budget";
        let amounts: BudgetAmounts = match field(COMMAND, payload, "amounts") {
            Ok(amounts) => amounts,
            Err(response) => return response,
        };
        self.answer_budget(COMMAND, move |gate| {
            gate.add(amounts).map(|report| BudgetReply {
                budget: Some(report),
            })
        })
        .await
    }

    /// `audit_budget` (Rust-native): the ledger replayed record by record,
    /// and its settled spends against the total it reports.
    pub(crate) async fn handle_audit_budget(&self) -> DaemonResponse {
        self.answer_budget("audit_budget", |gate| {
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

    /// Answer `command` with what `call` reads from or does to the
    /// session's budget, or with the ledger's error.
    async fn answer_budget<T: serde::Serialize + Send + 'static>(
        &self,
        command: &'static str,
        call: impl FnOnce(&BudgetGate) -> Result<T, BudgetError> + Send + 'static,
    ) -> DaemonResponse {
        let hosted = match self.hosted(command) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let session = match hosted.session() {
            Ok(session) => session,
            Err(error) => return response_failure(None, command, &error.to_string(), None),
        };
        let gate = session.budget();
        let reply = match tokio::task::spawn_blocking(move || call(&gate)).await {
            Ok(Ok(reply)) => reply,
            Ok(Err(error)) => return response_failure(None, command, &error.to_string(), None),
            Err(error) => {
                return response_failure(
                    None,
                    command,
                    &format!("the budget ledger call did not finish: {error}"),
                    None,
                )
            }
        };
        match serde_json::to_value(reply) {
            Ok(data) => response_success(None, command, Some(data)),
            Err(error) => response_failure(None, command, &error.to_string(), None),
        }
    }
}

/// The field `key` of a budget command, or the refusal that names it.
// DaemonResponse is the wire response struct and is deliberately wide;
// the error channel carries the whole response.
#[allow(clippy::result_large_err)]
fn field<T: serde::de::DeserializeOwned>(
    command: &str,
    payload: &Value,
    key: &str,
) -> Result<T, DaemonResponse> {
    let Some(value) = payload.get(key) else {
        return Err(response_failure(
            None,
            command,
            &format!("{key} is required"),
            None,
        ));
    };
    serde::Deserialize::deserialize(value)
        .map_err(|error| response_failure(None, command, &format!("invalid {key}: {error}"), None))
}

/// Send the budget `gate` reports, then each change of it: the report
/// lands on the core (the attach snapshot's `state.budget`) and goes out as
/// one `budget_update` event. A session without a budget sends nothing
/// until it gets one. The forwarder ends with the session's gate, or when
/// another follow took its place (`epoch` is no longer the core's).
#[tracing::instrument(skip_all)]
#[expect(
    clippy::assigning_clones,
    reason = "a changed budget was moved into its event: nothing to clone into"
)]
async fn forward_budget(
    gate: Arc<BudgetGate>,
    epoch: u64,
    core: Arc<Mutex<SessionCore>>,
    events: Arc<EventPump>,
) {
    // Subscribed before the first read: a change the read misses is
    // delivered after it.
    let mut updates = gate.watch();
    let mut budget = match tokio::task::spawn_blocking(move || gate.report()).await {
        Ok(budget) => budget,
        Err(error) => {
            eprintln!("eukhe-daemon worker: reading the session's budget did not finish: {error}");
            return;
        }
    };
    loop {
        {
            let mut core = core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            if core.budget_epoch != epoch {
                return;
            }
            if core.budget != budget {
                core.budget.clone_from(&budget);
                emit_event_locked(&mut core, &events, SessionEvent::BudgetUpdate { budget });
            }
        }
        if updates.changed().await.is_err() {
            return;
        }
        budget = updates.borrow_and_update().clone();
    }
}

#[cfg(test)]
mod tests;
