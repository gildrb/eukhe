//! A task's budget (spec/README.md B1-B9): money, tokens, model requests,
//! tool calls and a wall-clock deadline the task tree may spend, as a hard
//! limit.
//!
//! The budget is an account in a ledger file ([`eukhe_budget::Ledger`],
//! `<agent dir>/budgets/<owner session>.jsonl`): its owner's session, every
//! child that draws from it as a shared member (a link file), and every
//! child carved an allotment of its own (its own file). A session that
//! belongs to no account passes every request and tool call through
//! untouched. In one that does, every provider request ([`rows`]:
//! [`wrap_models_with_budget`]) and every tool call
//! (`BudgetGate::wrap_tool`, `tools`) reserves its worst case before it
//! runs and settles what it spent after; a reservation a crash left open is
//! charged at what it held when the session opens again
//! ([`BudgetGate::open`]). A provider request that belongs to no task
//! passes the daemon's account ([`BudgetGate::daemon`]). What the agent
//! and the user are told is in `notices`.
//!
//! Every ledger operation is blocking file IO of a few milliseconds: the
//! public methods of [`BudgetGate`] run it on the calling thread, so async
//! code calls them inside `tokio::task::spawn_blocking`.

mod gate;
mod notices;
mod rows;
mod tools;

#[cfg(test)]
mod paths_tests;
#[cfg(test)]
mod tests;

use std::collections::{BTreeMap, HashMap};
use std::path::Path;
use std::sync::{Arc, Mutex, OnceLock, PoisonError};

use eukhe_budget::{
    CarveOutcome, Ledger, LedgerError, Member, ReclaimOutcome, Reserved, Use, REQUEST_MIN_MS,
    TOOL_MIN_MS,
};
use eukhe_types::budget::{BudgetAmounts, BudgetLimits, BudgetPhase, BudgetReport};
use tokio::sync::watch;

use super::deps::{HostCall, HostCallHandler, HostDeps};
use super::settings::EukheSettings;

pub use notices::BUDGET_NOTICE_CUSTOM_TYPE;
pub use rows::wrap_models_with_budget;

/// Why a budget operation failed. Every failure refuses the spend.
pub type BudgetError = LedgerError;

/// The account of every provider request that belongs to no task: the
/// shared chat's compactor, `eukhe chat`, `eukhe provider` and the
/// tiny-model commands. Without its ledger file they pass through, like a
/// session without a budget.
pub const DAEMON_ACCOUNT: &str = "daemon";

/// What an agent's turn asks first before a work request of its own told
/// the gate more: one model request, for as long as a request may run.
const FIRST_TURN: BudgetAmounts = BudgetAmounts {
    cost_micros: 0,
    tokens: 0,
    time_ms: gate::DEFAULT_DEADLINE_MS,
    tool_calls: 0,
    requests: 1,
};

/// The budget one agent (a session) spends from: its ledger, the report
/// every surface watches, the final-answer reserve its last agent turn
/// computed, which notices the agent was given, and the reservations of
/// its deferred responses until they are fetched.
pub struct BudgetGate {
    ledger: Ledger,
    /// The session's settings (the tool blocking budget). `None` for a
    /// side gate, which wraps no tool.
    settings: Option<Arc<EukheSettings>>,
    reports: watch::Sender<Option<BudgetReport>>,
    keep: Mutex<BudgetAmounts>,
    told: Mutex<notices::Told>,
    notices: OnceLock<notices::NoticeSink>,
    /// The open reservation of each deferred response (by
    /// `<provider>/<handle id>`): it settles when its fetch ends.
    deferred: Mutex<HashMap<String, Held>>,
    /// The agent's steps as actually spent: what a grant's `low` (the Low
    /// notice) is judged against, and its longest model request, which
    /// its final answer's time reserve follows.
    steps: Mutex<Steps>,
    /// The smallest offer of the agent's last work request (one model
    /// request before its first): the least its next turn asks first, as
    /// its context only grows.
    turn: Mutex<BudgetAmounts>,
}

/// What the agent's steps actually spent, as this process saw them.
#[derive(Debug, Default)]
struct Steps {
    /// Per spent dimension, the largest actual spend of one of the agent's
    /// work requests or tool calls; `time_ms`: the longest time from the
    /// start of one of its work requests to the start of the next.
    largest: BudgetAmounts,
    /// When its last work request started (Unix ms).
    started_ms: Option<u64>,
    /// The longest wall time of one of its own model requests (work or
    /// its final answer) that ended with its response, from when it was
    /// sent, on the clock that stops a request at its granted time;
    /// `None` before the first (B14).
    longest_request_ms: Option<u64>,
}

impl BudgetGate {
    /// The gate of the session `session_id`, made when the session's
    /// process opens it. A session with its own account or a link to one
    /// spends from it; a child session (`parent_session_id`) without either
    /// takes the allotment its parent carved for it, else joins its
    /// parent's account as a shared member, else has no budget. Then every
    /// reservation of this session a crash left open is settled at what it
    /// held (never another agent's). Only the process that runs the
    /// session opens its gate: the recovery would settle the requests
    /// another process has in flight. A ledger that cannot be read is
    /// logged; the gate then refuses every request and tool call.
    ///
    /// Blocking file IO.
    #[must_use]
    pub fn open(
        agent_dir: &Path,
        session_id: &str,
        parent_session_id: Option<&str>,
        settings: Arc<EukheSettings>,
    ) -> Arc<BudgetGate> {
        let gate = Self::over(agent_dir, session_id, Some(settings));
        if let Some(parent) = parent_session_id {
            let entered = match gate.ledger.ensure_child(parent) {
                Ok(Some(_)) => Ok(()),
                Ok(None) => gate.ledger.join(parent).map(drop),
                Err(error) => Err(error),
            };
            match entered {
                // A parent without a budget; a session with an account of
                // its own.
                Ok(()) | Err(LedgerError::NoBudget(_) | LedgerError::AlreadyOpen(_)) => {}
                Err(error) => {
                    tracing::warn!(session_id, parent, %error, "the budget of the parent session was not joined");
                }
            }
        }
        if gate.ledger.exists() {
            match gate.ledger.recover(session_id) {
                Ok(report) => gate.publish(&report),
                // A file without a record, or an account this session left.
                Err(LedgerError::NoBudget(_) | LedgerError::NotMember(_)) => {}
                Err(error) => {
                    tracing::warn!(session_id, %error, "the budget ledger did not recover: its requests and tool calls are refused");
                }
            }
            match gate.ledger.members() {
                Ok(members) => {
                    if let Some(member) = members.get(session_id) {
                        gate.set_keep(member.keep);
                    }
                }
                Err(error) => {
                    tracing::warn!(session_id, %error, "the budget members were not read");
                }
            }
        }
        gate
    }

    /// A gate over the session's account for a model collection the
    /// session's side requests go through in a process that did not open
    /// the session (or before it did): no recovery, no notices. Pass it to
    /// [`wrap_models_with_budget`]. No IO.
    #[must_use]
    pub fn side(agent_dir: &Path, session_id: &str) -> Arc<BudgetGate> {
        Self::over(agent_dir, session_id, None)
    }

    /// The gate of the provider requests that belong to no task: the
    /// [`DAEMON_ACCOUNT`]. Several processes spend from it at once, so none
    /// recovers its reservations. No IO.
    #[must_use]
    pub fn daemon(agent_dir: &Path) -> Arc<BudgetGate> {
        Self::side(agent_dir, DAEMON_ACCOUNT)
    }

    fn over(
        agent_dir: &Path,
        session_id: &str,
        settings: Option<Arc<EukheSettings>>,
    ) -> Arc<BudgetGate> {
        Arc::new(BudgetGate {
            ledger: Ledger::of(&agent_dir.join("budgets"), session_id),
            settings,
            reports: watch::Sender::new(None),
            keep: Mutex::new(BudgetAmounts::default()),
            told: Mutex::new(notices::Told::default()),
            notices: OnceLock::new(),
            deferred: Mutex::new(HashMap::new()),
            steps: Mutex::default(),
            turn: Mutex::new(FIRST_TURN),
        })
    }

    /// The session's ledger.
    #[must_use]
    pub fn ledger(&self) -> &Ledger {
        &self.ledger
    }

    /// The agent this gate spends for: its session id.
    #[must_use]
    pub fn agent(&self) -> &str {
        self.ledger.session_id()
    }

    /// The budget's state as this agent sees it, read from the ledger;
    /// `None`: the session has no budget. A ledger that cannot be read is
    /// logged and reads as `None` (the gates refuse; [`Self::funds_turn`]
    /// is `false`).
    #[must_use]
    pub fn report(&self) -> Option<BudgetReport> {
        match self.read() {
            Ok(report) => report,
            Err(error) => {
                tracing::warn!(session_id = self.agent(), %error, "the budget ledger was not read");
                None
            }
        }
    }

    /// What the budget still admits for this agent; `None`: the session
    /// has no budget.
    #[must_use]
    pub fn phase(&self) -> Option<BudgetPhase> {
        self.report().map(|report| report.phase)
    }

    /// Whether the budget funds one more turn of this agent: it has no
    /// budget, or the compiled core would grant the agent, as work, both
    /// the smallest offer of its last work request and one tool call
    /// ([`Ledger::admits`]). An agent wrapping up or exhausted, or one
    /// whose account has no tool call, model request, money, tokens or
    /// time left for a step past its final-answer reserve, is funded no
    /// turn. A ledger that cannot be read funds none.
    ///
    /// Blocking file IO.
    #[must_use]
    pub fn funds_turn(&self) -> bool {
        let keep = self.keep();
        let request = *self.turn.lock().unwrap_or_else(PoisonError::into_inner);
        let admits = |offer: BudgetAmounts, min_ms: u64| {
            self.ledger
                .admits(self.agent(), Use::Work, keep, &[offer], min_ms)
        };
        let funded = admits(request, REQUEST_MIN_MS).and_then(|funded| {
            if funded {
                admits(self.tool_offer(), TOOL_MIN_MS)
            } else {
                Ok(false)
            }
        });
        match funded {
            Ok(funded) => funded,
            Err(LedgerError::NoBudget(_)) => true,
            Err(error) => {
                tracing::warn!(session_id = self.agent(), %error, "the budget ledger was not read");
                false
            }
        }
    }

    /// Every change of the budget's state this gate made or read: a
    /// reservation, a settlement, a carve, a reclaim, a set or an added
    /// budget. `None` until the session has a budget.
    #[must_use]
    pub fn watch(&self) -> watch::Receiver<Option<BudgetReport>> {
        self.reports.subscribe()
    }

    /// Sets the budget of a session that belongs to no account: it becomes
    /// the owner of a new one.
    ///
    /// # Errors
    ///
    /// [`LedgerError::AlreadyOpen`] when the session has a budget (add to
    /// it instead), and the ledger's or the compiled core's failures.
    pub fn set(&self, limits: BudgetLimits) -> Result<BudgetReport, BudgetError> {
        let report = self.ledger.open_root(limits)?;
        self.changed(&report);
        Ok(report)
    }

    /// Adds budget: an overrun is repaid first, every agent of the account
    /// works again, and time moves the deadline. A session without a budget
    /// gets one, limited in the dimensions `amounts` names.
    ///
    /// # Errors
    ///
    /// [`LedgerError::NotRoot`] for a budget carved from a parent's,
    /// [`LedgerError::TooLarge`], and the ledger's or the compiled core's
    /// failures.
    pub fn add(&self, amounts: BudgetAmounts) -> Result<BudgetReport, BudgetError> {
        let report = match self.ledger.fund(amounts) {
            Ok(report) => report,
            Err(LedgerError::NoBudget(_)) => {
                self.ledger.open_root(eukhe_budget::limits_of(amounts))?
            }
            Err(error) => return Err(error),
        };
        self.changed(&report);
        Ok(report)
    }

    /// Limits each dimension `limits` names that the budget leaves
    /// unlimited (a limited one keeps its limit: [`Self::add`] raises it);
    /// a session without a budget gets one of `limits`.
    ///
    /// # Errors
    ///
    /// The ledger's or the compiled core's failures.
    pub fn limit(&self, limits: BudgetLimits) -> Result<BudgetReport, BudgetError> {
        let report = match self.ledger.limit(limits) {
            Ok(report) => report,
            Err(LedgerError::NoBudget(_)) => self.ledger.open_root(limits)?,
            Err(error) => return Err(error),
        };
        self.changed(&report);
        Ok(report)
    }

    /// Replays the ledger through the compiled core (B9).
    ///
    /// # Errors
    ///
    /// [`LedgerError::NoBudget`], and the ledger's or the compiled core's
    /// failures.
    pub fn audit(&self) -> Result<eukhe_budget::Audit, BudgetError> {
        self.ledger.audit()
    }

    /// The final-answer reserve this agent's last turn computed (zero
    /// before the first): what its tool calls and side requests leave
    /// free.
    #[must_use]
    pub fn keep(&self) -> BudgetAmounts {
        *self.keep.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// The agent's largest step as actually spent (zero before its
    /// first): what a side request's `low` is judged against, and the
    /// actual part of [`Self::work_step`].
    fn step(&self) -> BudgetAmounts {
        self.steps
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .largest
    }

    /// What a work grant's `low` is judged against (B7): per dimension the
    /// larger of the agent's largest step as actually spent and the
    /// smallest hold its next work can be granted, a model request (the
    /// smallest offer of its last work request; one model request before
    /// the first) or a tool call ([`Self::tool_offer`]); in time, the
    /// shortest such a request or call is clipped to, or what it asks when
    /// that is less. So a grant not low funds one more step of the work
    /// the agent asks, and it is told its budget runs low before its work
    /// is refused.
    fn work_step(&self) -> BudgetAmounts {
        let actual = self.step();
        let request = *self.turn.lock().unwrap_or_else(PoisonError::into_inner);
        let tool = self.tool_offer();
        BudgetAmounts {
            cost_micros: actual
                .cost_micros
                .max(request.cost_micros)
                .max(tool.cost_micros),
            tokens: actual.tokens.max(request.tokens).max(tool.tokens),
            time_ms: actual
                .time_ms
                .max(request.time_ms.min(REQUEST_MIN_MS))
                .max(tool.time_ms.min(TOOL_MIN_MS)),
            tool_calls: actual
                .tool_calls
                .max(request.tool_calls)
                .max(tool.tool_calls),
            requests: actual.requests.max(request.requests).max(tool.requests),
        }
    }

    /// A work request of the agent starts at `now_ms`: the time since the
    /// last one started is the length of a step.
    fn step_started(&self, now_ms: u64) {
        let mut steps = self.steps.lock().unwrap_or_else(PoisonError::into_inner);
        if let Some(started) = steps.started_ms.replace(now_ms) {
            steps.largest.time_ms = steps.largest.time_ms.max(now_ms.saturating_sub(started));
        }
    }

    /// One of the agent's own model requests ended with its response
    /// `ms` after it was sent.
    fn request_ended(&self, ms: u64) {
        let mut steps = self.steps.lock().unwrap_or_else(PoisonError::into_inner);
        let longest = steps
            .longest_request_ms
            .map_or(ms, |longest| longest.max(ms));
        steps.longest_request_ms = Some(longest);
    }

    /// The longest of the agent's own model requests that ended with
    /// their response; `None` before the first (B14).
    fn longest_request_ms(&self) -> Option<u64> {
        self.steps
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .longest_request_ms
    }

    /// A work request or tool call of the agent spent `spend`.
    fn step_spent(&self, spend: BudgetAmounts) {
        let mut steps = self.steps.lock().unwrap_or_else(PoisonError::into_inner);
        let largest = steps.largest;
        steps.largest = BudgetAmounts {
            cost_micros: largest.cost_micros.max(spend.cost_micros),
            tokens: largest.tokens.max(spend.tokens),
            time_ms: largest.time_ms,
            tool_calls: largest.tool_calls.max(spend.tool_calls),
            requests: largest.requests.max(spend.requests),
        };
    }

    /// The agents of the account and the agent above each one.
    ///
    /// # Errors
    ///
    /// [`LedgerError::NoBudget`], and the ledger's failures.
    pub fn members(&self) -> Result<BTreeMap<String, Member>, BudgetError> {
        self.ledger.members()
    }

    /// The children this agent carved an allotment for that did not come
    /// back yet.
    ///
    /// # Errors
    ///
    /// [`LedgerError::NoBudget`], and the ledger's failures.
    pub fn lent_children(&self) -> Result<Vec<String>, BudgetError> {
        self.ledger.lent_children(self.agent())
    }

    /// Carves an allotment of `limits` for the child session
    /// `child_session_id` out of this account (a time limit of `None`: what
    /// is left before the deadline); the reserves of this agent and the
    /// agents above it stay free.
    ///
    /// # Errors
    ///
    /// [`LedgerError::NoBudget`] when this session has no budget,
    /// [`LedgerError::NeedsAllotment`] when `limits` leaves out a
    /// dimension the account limits, and the ledger's or the compiled
    /// core's failures.
    pub fn carve(
        &self,
        child_session_id: &str,
        limits: BudgetLimits,
    ) -> Result<CarveOutcome, BudgetError> {
        let outcome = self.ledger.carve(self.agent(), child_session_id, limits)?;
        match &outcome {
            CarveOutcome::Carved { report } | CarveOutcome::Refused { report, .. } => {
                self.publish(report);
            }
        }
        Ok(outcome)
    }

    /// Takes back what the child session `child_session_id` was lent
    /// ([`Ledger::reclaim`]): a child with a request in flight is busy
    /// unless `force` (the child has ended).
    ///
    /// # Errors
    ///
    /// [`LedgerError::NoBudget`] when this session has no budget, and the
    /// ledger's or the compiled core's failures.
    pub fn reclaim(
        &self,
        child_session_id: &str,
        force: bool,
    ) -> Result<ReclaimOutcome, BudgetError> {
        let outcome = self.ledger.reclaim(child_session_id, force)?;
        match &outcome {
            ReclaimOutcome::Reclaimed { report, .. } => self.publish(report),
            ReclaimOutcome::NotLent | ReclaimOutcome::Busy => {}
        }
        Ok(outcome)
    }

    /// The shared child `child_session_id` ended: what it holds settles at
    /// what it held and it leaves the account (its reserve no longer
    /// counts above anyone).
    ///
    /// # Errors
    ///
    /// The ledger's or the compiled core's failures.
    pub fn release(&self, child_session_id: &str) -> Result<(), BudgetError> {
        self.ledger.release(child_session_id)?;
        drop(self.read()?);
        Ok(())
    }

    /// The child session `child_session_id` joins this agent's account as
    /// a shared member (it was released when its last task ended and is
    /// given work again). Idempotent.
    ///
    /// # Errors
    ///
    /// [`LedgerError::AlreadyOpen`] when the child holds a live account of
    /// its own, and the ledger's or the compiled core's failures.
    pub fn admit_child(&self, child_session_id: &str) -> Result<(), BudgetError> {
        let own = self.ledger.path();
        let dir = own.parent().unwrap_or_else(|| Path::new("."));
        Ledger::of(dir, child_session_id).join(self.agent())?;
        drop(self.read()?);
        Ok(())
    }

    /// The report of the ledger for this agent, published to the watchers;
    /// `None` without a budget (one `stat`).
    fn read(&self) -> Result<Option<BudgetReport>, BudgetError> {
        if !self.ledger.exists() {
            return Ok(None);
        }
        let report = self.ledger.report(self.agent())?;
        if let Some(report) = &report {
            self.publish(report);
        }
        Ok(report)
    }

    fn publish(&self, report: &BudgetReport) {
        self.reports.send_if_modified(|current| {
            if current.as_ref() == Some(report) {
                return false;
            }
            *current = Some(report.clone());
            true
        });
    }

    /// The budget was set or added to: the agent is told again.
    fn changed(&self, report: &BudgetReport) {
        *self.told.lock().unwrap_or_else(PoisonError::into_inner) = notices::Told::default();
        self.publish(report);
    }

    fn set_keep(&self, keep: BudgetAmounts) {
        *self.keep.lock().unwrap_or_else(PoisonError::into_inner) = keep;
    }

    /// A blocking task of the gate that did not finish, as a ledger
    /// failure: it refuses the spend like one.
    fn task_failed(&self, error: tokio::task::JoinError) -> BudgetError {
        LedgerError::Io {
            path: self.ledger.path(),
            source: std::io::Error::other(error),
        }
    }

    /// [`Ledger::reserve`] for this agent on a blocking thread, its report
    /// published. `None`: the session has no budget (its ledger holds no
    /// record), so the caller passes its request or tool call through.
    async fn reserve(
        self: &Arc<Self>,
        use_: Use,
        label: String,
        keep: BudgetAmounts,
        offers: Vec<BudgetAmounts>,
        min_ms: u64,
    ) -> Result<Option<Reserved>, BudgetError> {
        let step = match use_ {
            Use::Work => self.work_step(),
            Use::Side | Use::Final => self.step(),
        };
        let gate = Arc::clone(self);
        let reserved = tokio::task::spawn_blocking(move || {
            gate.ledger
                .reserve(gate.agent(), use_, &label, keep, step, &offers, min_ms)
        })
        .await
        .map_err(|error| self.task_failed(error))?;
        match reserved {
            Ok(reserved) => {
                match &reserved {
                    Reserved::Granted { report, .. } | Reserved::Refused { report, .. } => {
                        self.publish(report);
                    }
                }
                Ok(Some(reserved))
            }
            Err(LedgerError::NoBudget(_)) => Ok(None),
            Err(error) => Err(error),
        }
    }

    /// [`Ledger::settle`], its report published. A failure is logged: the
    /// reservation then stays held until the session opens again, which
    /// settles it at what it held.
    fn settle(&self, id: u64, spend: BudgetAmounts) {
        match self.ledger.settle(id, spend) {
            Ok(report) => self.publish(&report),
            Err(error) => {
                tracing::warn!(session_id = self.agent(), id, %error, "a budget reservation did not settle");
            }
        }
    }

    /// Keep the reservation of the deferred response `key` open until its
    /// fetch settles it.
    fn park_deferred(&self, key: String, held: Held) {
        let replaced = self
            .deferred
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .insert(key, held);
        // A handle parked twice: the older reservation settles in full.
        drop(replaced);
    }

    /// The open reservation of the deferred response `key`, if this
    /// process holds one.
    fn take_deferred(&self, key: &str) -> Option<Held> {
        self.deferred
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .remove(key)
    }
}

/// A granted reservation until it settles. [`Held::settle`] replaces it
/// with the actual spend. Dropped before that (the task that ran the
/// request or the tool call was cancelled), it settles at everything it
/// holds: the outcome is not known, as after a crash.
struct Held {
    gate: Arc<BudgetGate>,
    id: u64,
    /// What the reservation holds, time aside (time is a deadline, not a
    /// spend).
    full: BudgetAmounts,
    /// What it is for: a settled work request or tool call is a step of
    /// the agent.
    use_: Use,
    settled: bool,
}

impl Held {
    /// The reservation `id` of `gate` for `use_`, holding `amount`.
    fn start(gate: &Arc<BudgetGate>, id: u64, amount: BudgetAmounts, use_: Use) -> Held {
        Held {
            gate: Arc::clone(gate),
            id,
            full: BudgetAmounts {
                time_ms: 0,
                ..amount
            },
            use_,
            settled: false,
        }
    }

    /// Settles at `spend` on a blocking thread. A reservation that held no
    /// model request (a side request's, a tool call's) is charged none: a
    /// side request is no turn of the agent. The spend of work is a step
    /// of the agent; one dropped unsettled is not (its spend is unknown).
    async fn settle(mut self, mut spend: BudgetAmounts) {
        // The blocking task runs to its end even when this future is
        // dropped while it waits.
        self.settled = true;
        if self.full.requests == 0 {
            spend.requests = 0;
        }
        match self.use_ {
            Use::Work => self.gate.step_spent(spend),
            Use::Final | Use::Side => {}
        }
        let gate = Arc::clone(&self.gate);
        let id = self.id;
        if let Err(error) = tokio::task::spawn_blocking(move || gate.settle(id, spend)).await {
            tracing::warn!(id, %error, "a budget reservation did not settle");
        }
    }
}

impl Drop for Held {
    fn drop(&mut self) {
        if self.settled {
            return;
        }
        let spend = self.full;
        let gate = Arc::clone(&self.gate);
        let id = self.id;
        match tokio::runtime::Handle::try_current() {
            Ok(runtime) => drop(runtime.spawn_blocking(move || gate.settle(id, spend))),
            // No runtime is left to run it on: settle here.
            Err(_) => gate.settle(id, spend),
        }
    }
}

/// Connects a session to its budget once its deps exist: registers the
/// `budget.status` kernel host request (the budget's report as JSON, `null`
/// without a budget) and delivers the gate's notices to the session's main
/// conversation.
pub(crate) fn install(deps: &Arc<HostDeps>) {
    let gate = Arc::clone(&deps.budget);
    let status: HostCallHandler = Arc::new(move |_call: HostCall| {
        let gate = Arc::clone(&gate);
        Box::pin(async move {
            let report = tokio::task::spawn_blocking(move || gate.report()).await?;
            anyhow::Ok(serde_json::to_value(report)?)
        })
    });
    deps.host_requests.register("budget.status", status);
    let harness = deps.harness.clone();
    let closing = deps.closing.clone();
    deps.budget.deliver_notices(Arc::new(move |notice| {
        tokio::spawn(notices::deliver(harness.clone(), closing.clone(), notice));
    }));
}
