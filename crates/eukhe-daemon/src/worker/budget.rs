//! The session's budget on the wire: `get_budget`, `set_budget`,
//! `add_budget` and `audit_budget` answer from the session's budget gate
//! (`eukhe_core::durable::budget`: ledger file IO, so each call runs on the
//! blocking pool), and each change of the budget goes out as one
//! `budget_update` session event. The last report sent stays on the session
//! core, where the attach snapshot reads its `state.budget`. A create (and
//! a fork that replaces the session) gives the session its budget before
//! its first turn ([`CreateBudget`]).

use std::sync::{Arc, Mutex};

use eukhe_core::durable::budget::{BudgetError, BudgetGate, RunStart};
use eukhe_core::durable::cvar_agent::CvarLineScope;
use eukhe_core::settings::cvar::table;
use eukhe_core::settings::BudgetLimitsMode;
use eukhe_types::budget::{BudgetAmounts, RunKind, RunLimits};
use eukhe_types::daemon::{
    BudgetAudit, BudgetAuditReply, BudgetLimitsReply, BudgetReply, SessionEvent,
};
use serde_json::Value;

use super::{emit_event_locked, EventPump, HostedSession, SessionCore, Worker};
use crate::protocol::{response_failure, response_success, DaemonResponse};

/// What a create does to its session's budget before the first turn.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CreateBudget {
    /// Nothing: the session spends from the budget its ledger (or its
    /// parent's) gives it, if any.
    Keep,
    /// The create config's `budget`: the session's standing limits, each
    /// run's set limits from now on (the current run's included).
    Set(RunLimits),
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
        CreateBudget::Set(limits) => gate
            .set_standing(limits)
            .map(|_| ())
            .map_err(|error| error.to_string()),
        CreateBudget::Share { source } => match gate.ledger().join(&source) {
            // A source without a budget; a fork that already draws from it
            // or has a budget of its own (a reopen).
            Ok(_) | Err(BudgetError::NoBudget(_) | BudgetError::AlreadyOpen(_)) => Ok(()),
            Err(error) => Err(error.to_string()),
        },
    })
    .await
    .map_err(|error| error.to_string())?
}

/// What the `/b` prefix of a prompt asks of its run (the prompt's
/// `runLimits`): presets in order and the limits its pairs set.
#[derive(Debug, Clone, Default, PartialEq, Eq, serde::Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub(crate) struct RunAsk {
    pub(crate) presets: Vec<String>,
    pub(crate) set: RunLimits,
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

    /// A message of the principal: sent while the session is idle it
    /// starts a fresh interactive run, its limits filled with what its
    /// `/b` prefix asks (`ask`); one that joins the running run (queued or
    /// steering) sets what its prefix asks on that run. Ledger file IO, on
    /// the blocking pool.
    ///
    /// # Errors
    ///
    /// The response that names why the run did not start (a profile or
    /// preset that is no limit, the ledger's failure): nothing is sent.
    #[allow(clippy::result_large_err)] // the error is the wire response itself
    pub(crate) async fn begin_message_run(
        &self,
        hosted: &HostedSession,
        command: &str,
        ask: Option<RunAsk>,
    ) -> Result<(), DaemonResponse> {
        let busy = self
            .core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .is_busy();
        let session = hosted
            .session()
            .map_err(|error| response_failure(None, command, &error.to_string(), None))?;
        let gate = session.budget();
        let started = tokio::task::spawn_blocking(move || match (busy, ask) {
            (false, ask) => {
                let ask = ask.unwrap_or_default();
                gate.start_run(RunStart {
                    kind: RunKind::Interactive,
                    set: ask.set,
                    presets: ask.presets,
                    standing: None,
                })
                .map(|_| ())
            }
            (true, Some(ask)) => gate.set_asked(ask.set, ask.presets).map(|_| ()),
            (true, None) => Ok(()),
        })
        .await;
        match started {
            Ok(Ok(())) => Ok(()),
            Ok(Err(error)) => Err(response_failure(None, command, &error.to_string(), None)),
            Err(error) => Err(response_failure(
                None,
                command,
                &format!("the budget ledger call did not finish: {error}"),
                None,
            )),
        }
    }

    /// `get_budget` (Rust-native): the session's budget, `budget` null for
    /// a session without one.
    pub(crate) async fn handle_get_budget(&self) -> DaemonResponse {
        self.answer_budget("get_budget", |gate| {
            Ok::<_, BudgetError>(BudgetReply {
                budget: gate.report(),
            })
        })
        .await
    }

    /// `set_budget { limits }` (Rust-native): the limits of the session's
    /// current run, a number or `unlimited` per dimension.
    pub(crate) async fn handle_set_budget(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "set_budget";
        let limits: RunLimits = match field(COMMAND, payload, "limits") {
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

    /// `set_budget_limits { on }` (Rust-native): write `budget.limits` to
    /// the global config.cfg and answer the line of the toggle: with
    /// limits on, the numbers the active profile enforces for this
    /// session's login.
    pub(crate) async fn handle_set_budget_limits(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "set_budget_limits";
        let on: bool = match field(COMMAND, payload, "on") {
            Ok(on) => on,
            Err(response) => return response,
        };
        match self.set_budget_limits(COMMAND, on).await {
            Ok(text) => response_success(
                None,
                COMMAND,
                serde_json::to_value(BudgetLimitsReply { text }).ok(),
            ),
            Err(response) => response,
        }
    }

    /// Turn the principal's limits on or off; the line that says so.
    #[allow(clippy::result_large_err)] // the error is the wire response itself
    pub(crate) async fn set_budget_limits(
        &self,
        command: &str,
        on: bool,
    ) -> Result<String, DaemonResponse> {
        let mode = if on {
            BudgetLimitsMode::On
        } else {
            BudgetLimitsMode::Off
        };
        let line = eukhe_types::cvar::Command::Set {
            id: table::BUDGET_LIMITS.id.to_string(),
            value: mode.word().to_string(),
        }
        .to_string();
        self.cvar_line(command, &line, CvarLineScope::Global)
            .await?;
        if !on {
            return Ok(crate::limits_text::LIMITS_OFF.to_owned());
        }
        let hosted = self.hosted(command)?;
        let session = hosted
            .session()
            .map_err(|error| response_failure(None, command, &error.to_string(), None))?;
        let auth = session.budget().auth();
        let settings = hosted.deps().settings.manager();
        Ok(crate::limits_text::on_line(
            auth,
            settings.get_budget_plan_reserve(),
            &settings.get_budget_profile(),
        ))
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
    async fn answer_budget<
        T: serde::Serialize + Send + 'static,
        E: std::fmt::Display + Send + 'static,
    >(
        &self,
        command: &'static str,
        call: impl FnOnce(&BudgetGate) -> Result<T, E> + Send + 'static,
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
/// until it gets one. Each plan notice of the gate (limits off, a plan
/// window past the reserve line) goes out as one `plan_usage` event with
/// its text in local time. The forwarder ends with the session's gate, or
/// when another follow took its place (`epoch` is no longer the core's).
#[tracing::instrument(skip_all)]
async fn forward_budget(
    gate: Arc<BudgetGate>,
    epoch: u64,
    core: Arc<Mutex<SessionCore>>,
    events: Arc<EventPump>,
) {
    // Subscribed before the first read: a change the read misses is
    // delivered after it.
    let mut updates = gate.watch();
    let mut notices = gate.plan_notices();
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
                emit_event_locked(
                    &mut core,
                    &events,
                    SessionEvent::BudgetUpdate {
                        budget: budget.clone(),
                    },
                );
            }
        }
        tokio::select! {
            changed = updates.changed() => {
                if changed.is_err() {
                    return;
                }
                budget.clone_from(&updates.borrow_and_update());
            }
            notice = notices.recv() => match notice {
                Ok(notice) => {
                    let text = crate::limits_text::plan_usage_line(
                        &notice.window,
                        notice.reserve_percent,
                        crate::util::now_ms(),
                        &crate::limits_text::local_clock,
                    );
                    let mut core = core
                        .lock()
                        .unwrap_or_else(std::sync::PoisonError::into_inner);
                    if core.budget_epoch != epoch {
                        return;
                    }
                    emit_event_locked(&mut core, &events, SessionEvent::PlanUsage { notice, text });
                }
                // A notice missed while the forwarder lagged is not sent
                // again: the next reading past the line is.
                Err(tokio::sync::broadcast::error::RecvError::Lagged(_)) => {}
                Err(tokio::sync::broadcast::error::RecvError::Closed) => return,
            },
        }
    }
}

#[cfg(test)]
mod tests;
