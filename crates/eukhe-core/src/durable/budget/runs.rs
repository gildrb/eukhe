//! Runs (spec/README.md B15-B21): what one fill of a session's limits
//! lasts for. Every session has a budget: its first effect starts a run
//! when it has none, and each new run (a message sent while the session
//! is idle, a scheduled fire, a `/loop`, an `/autoresearch`, a `-p`
//! prompt, an SDK prompt: [`BudgetGate::start_run`]) renews it. The
//! limits of a run fill in the compiled core (`eukhe_bend::rules::limits`)
//! from, in order: what the principal set (for this run, then for the
//! session), the run's `/b` presets, and with `budget.limits` on the
//! principal's profile, else the limits profile; with it off an unset
//! dimension stays unlimited, the run going until finished.
//!
//! A plan login's quota (the provider's last reading on the
//! [`QuotaBoard`]) is read before each work request of the agent: with
//! limits on, a window at or past its share (`100 - budget.planReserve`
//! percent used) wraps the run up; with limits off, the window is told
//! once as a [`PlanNotice`] until a reading below the line.

use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, LazyLock, Mutex, OnceLock, PoisonError};

use eukhe_ai::quota::{PlanQuota, QuotaBoard};
use eukhe_bend::rules::limits as core;
use eukhe_budget::{LedgerError, RunRecord, REQUEST_MIN_MS};
use eukhe_types::budget::{
    AuthClass, BudgetAmounts, BudgetDimension, BudgetReport, BudgetSources, LimitSource,
    LimitValue, NextRun, PlanNotice, PlanShare, RunKind, RunLimits,
};
use serde_json::{Map, Value};
use tokio::sync::broadcast;

use super::BudgetGate;
use crate::settings::BudgetLimitsMode;

/// What a run's limits fill from besides what the principal set, read
/// when the run starts.
#[derive(Debug, Clone, PartialEq)]
pub struct RunFacts {
    /// How the session's model is paid for.
    pub auth: AuthClass,
    /// `budget.limits`.
    pub limits: BudgetLimitsMode,
    /// `budget.planReserve`: percent of each plan window left to the user.
    pub plan_reserve: u64,
    /// `budget.profile` as written.
    pub profile: Value,
    /// `budget.presets` as written.
    pub presets: Value,
}

impl RunFacts {
    /// The facts of a gate whose runs do not fill (a side gate): the
    /// principal's limits only.
    fn side() -> RunFacts {
        RunFacts {
            auth: AuthClass::ApiKey,
            limits: BudgetLimitsMode::Off,
            plan_reserve: 0,
            profile: Value::Null,
            presets: Value::Null,
        }
    }
}

/// The model of one of the session's provider requests, as the gate saw
/// it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SeenModel {
    pub provider: String,
    /// Whether the catalog prices its tokens.
    pub priced: bool,
}

/// Reads the [`RunFacts`] of the session: its settings and the auth of
/// `model` (`None` before the session's first request). Implementations
/// read local files only; no network IO.
pub type RunFactsFn = Arc<dyn Fn(Option<&SeenModel>) -> RunFacts + Send + Sync>;

/// How the session's runs fill: the kind of run its first effect starts
/// and where the facts come from.
struct RunFill {
    kind: RunKind,
    facts: RunFactsFn,
}

/// The runs of a gate: how they fill, one start at a time, the model of
/// the session's last request, whether the current run's first work
/// request is still to come, the plan notices, and what the principal set
/// or added for the next run while the session was idle.
pub(super) struct Runs {
    fill: OnceLock<RunFill>,
    starting: Mutex<()>,
    seen: Mutex<Option<SeenModel>>,
    fresh: AtomicBool,
    notices: broadcast::Sender<PlanNotice>,
    pub(super) next: Mutex<NextRun>,
}

impl Default for Runs {
    fn default() -> Self {
        Runs {
            fill: OnceLock::new(),
            starting: Mutex::new(()),
            seen: Mutex::new(None),
            fresh: AtomicBool::new(false),
            notices: broadcast::Sender::new(16),
            next: Mutex::new(NextRun::default()),
        }
    }
}

/// One run's start.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RunStart {
    pub kind: RunKind,
    /// What the principal set for this run only (`/budget set`, a `/b`
    /// pair).
    pub set: RunLimits,
    /// The `/b` presets of the run's message, in order (the last one
    /// that limits a dimension decides it).
    pub presets: Vec<String>,
    /// Replaces what the principal set for every run of the session
    /// (flags, a create config, the SDK); `None` keeps it.
    pub standing: Option<RunLimits>,
}

/// Which run a fill is for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Begin {
    /// A new run: its spend counts from now.
    New,
    /// The current run: its spend still counts from its start, what the
    /// principal set for it stays under the new set.
    Current,
}

/// Why a run did not start. The session's budget is as it was.
#[derive(Debug, thiserror::Error)]
pub enum RunError {
    #[error(transparent)]
    Ledger(#[from] LedgerError),
    #[error(transparent)]
    Core(#[from] eukhe_bend::Error),
    /// A `budget.profile` or `budget.presets` value that is no limit.
    #[error("budget.{key}: {reason}")]
    Settings { key: String, reason: String },
    /// A `/b` preset that is neither shipped nor in `budget.presets`.
    #[error("no budget preset named `{0}` (shipped: quick, deep; others: budget.presets)")]
    Preset(String),
}

/// What the checks before an agent's work request decided.
pub(super) enum Checked {
    /// The request goes on.
    Go,
    /// The run's first request cannot fit beside its final answer:
    /// nothing is sent; the error text.
    Floor(String),
    /// The run reached its plan share: its final answer is due.
    Plan(PlanShare),
}

/// The settings keys of one layer, each with its dimension and the scale
/// of its number (dollars and seconds as written).
const LAYER_KEYS: [(&str, BudgetDimension, f64); 5] = [
    ("cost", BudgetDimension::Cost, 1_000_000.0),
    ("tokens", BudgetDimension::Tokens, 1.0),
    ("time", BudgetDimension::Time, 1_000.0),
    ("toolCalls", BudgetDimension::ToolCalls, 1.0),
    ("requests", BudgetDimension::Requests, 1.0),
];

/// One layer as the settings write it: `{"cost": 2.5, "time": 3600,
/// "toolCalls": "unlimited", "untilFinished": true}`; `untilFinished`
/// makes money and tokens unlimited where the layer names neither.
fn layer(key: &str, value: &Value) -> Result<RunLimits, RunError> {
    let wrong = |reason: String| RunError::Settings {
        key: key.to_owned(),
        reason,
    };
    let object = match value {
        Value::Null => return Ok(RunLimits::default()),
        Value::Object(object) => object,
        other => return Err(wrong(format!("an object of limits, not {other}"))),
    };
    if let Some(unknown) = object
        .keys()
        .find(|name| *name != "untilFinished" && !LAYER_KEYS.iter().any(|(k, ..)| k == name))
    {
        return Err(wrong(format!(
            "`{unknown}` is no limit (cost, tokens, time, toolCalls, requests, untilFinished)"
        )));
    }
    let limits =
        LAYER_KEYS
            .iter()
            .try_fold(RunLimits::default(), |limits, (name, dimension, scale)| {
                let asked = match object.get(*name) {
                    None | Some(Value::Null) => None,
                    Some(Value::String(word)) if word == LimitValue::UNLIMITED => {
                        Some(LimitValue::Unlimited)
                    }
                    Some(Value::Number(number)) => match number.as_f64() {
                        Some(amount) if amount > 0.0 && (amount * scale).is_finite() => {
                            // Whole units of the ledger, at least one.
                            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                            // positive and finite, saturating
                            let at = (amount * scale).ceil() as u64;
                            Some(LimitValue::At(at))
                        }
                        _ => {
                            return Err(wrong(format!(
                                "{name}: a positive number or \"unlimited\", not {number}"
                            )))
                        }
                    },
                    Some(other) => {
                        return Err(wrong(format!(
                            "{name}: a positive number or \"unlimited\", not {other}"
                        )))
                    }
                };
                Ok(limits.with(*dimension, asked))
            })?;
    Ok(match object.get("untilFinished") {
        None | Some(Value::Null | Value::Bool(false)) => limits,
        Some(Value::Bool(true)) => limits.over(RunLimits {
            cost_micros: Some(LimitValue::Unlimited),
            tokens: Some(LimitValue::Unlimited),
            ..RunLimits::default()
        }),
        Some(other) => {
            return Err(wrong(format!("untilFinished: true or false, not {other}")));
        }
    })
}

/// The entry `name` of a settings object (`null` when absent).
fn entry<'a>(object: &'a Value, name: &str) -> &'a Value {
    object
        .as_object()
        .and_then(|object: &Map<String, Value>| object.get(name))
        .unwrap_or(&Value::Null)
}

fn core_kind(kind: RunKind) -> core::Kind {
    match kind {
        RunKind::Interactive => core::Kind::Interactive,
        RunKind::Headless => core::Kind::Headless,
        RunKind::Sdk => core::Kind::Sdk,
        RunKind::Scheduled => core::Kind::Scheduled,
        RunKind::Loop => core::Kind::Loop,
        RunKind::Autoresearch => core::Kind::Autoresearch,
    }
}

fn core_auth(auth: AuthClass) -> core::Auth {
    match auth {
        AuthClass::Plan => core::Auth::Plan,
        AuthClass::ApiKey => core::Auth::ApiKey,
        AuthClass::Local => core::Auth::Local,
    }
}

fn core_lims(limits: &RunLimits) -> core::Lims {
    let val = |value: Option<LimitValue>| match value {
        None => core::Val::Unset,
        Some(LimitValue::At(at)) => core::Val::At(at),
        Some(LimitValue::Unlimited) => core::Val::Unlimited,
    };
    core::Lims {
        cost: val(limits.cost_micros),
        tok: val(limits.tokens),
        ms: val(limits.time_ms),
        calls: val(limits.tool_calls),
        reqs: val(limits.requests),
    }
}

fn run_limits(lims: &core::Lims) -> RunLimits {
    let value = |val: core::Val| match val {
        core::Val::Unset => None,
        core::Val::At(at) => Some(LimitValue::At(at)),
        core::Val::Unlimited => Some(LimitValue::Unlimited),
    };
    RunLimits {
        cost_micros: value(lims.cost),
        tokens: value(lims.tok),
        time_ms: value(lims.ms),
        tool_calls: value(lims.calls),
        requests: value(lims.reqs),
    }
}

/// The limits a run of `kind` paid by `auth` gets with limits on when the
/// principal sets none: `profile` (`budget.profile`) for the kind, else
/// the limits profile; unlimited where neither fills.
///
/// # Errors
///
/// A profile value that is no limit, and the compiled core's failures.
pub fn active_profile(
    kind: RunKind,
    auth: AuthClass,
    profile: &Value,
) -> Result<RunLimits, RunError> {
    let own = layer(
        &format!("profile.{}", kind.slug()),
        entry(profile, kind.slug()),
    )?;
    let filled = core::fill(
        core::Toggle::On,
        core_kind(kind),
        core_auth(auth),
        &core::Lims::default(),
        &[],
        &core_lims(&own),
    )?;
    Ok(run_limits(&filled.lims))
}

/// The plan windows told of per provider, in this process: a window is
/// told once until a reading below the line.
static TOLD: LazyLock<Mutex<HashMap<String, Vec<String>>>> = LazyLock::new(Mutex::default);

impl BudgetGate {
    /// Makes the session's runs fill: its first effect starts a run of
    /// `kind` when it has no budget, and each run reads `facts`. The first
    /// call stays.
    pub fn fill_runs(&self, kind: RunKind, facts: RunFactsFn) {
        // A second fill is dropped: the session's first stays.
        let _ = self.runs.fill.set(RunFill { kind, facts });
    }

    /// The session sends a request to `model`: its next run reads its
    /// auth.
    pub(super) fn saw(&self, model: SeenModel) {
        *self
            .runs
            .seen
            .lock()
            .unwrap_or_else(PoisonError::into_inner) = Some(model);
    }

    /// Whether the session's runs fill ([`Self::fill_runs`]).
    pub(super) fn fills_runs(&self) -> bool {
        self.runs.fill.get().is_some()
    }

    /// The kind of run the session's first effect starts.
    #[must_use]
    pub fn run_kind(&self) -> Option<RunKind> {
        self.runs.fill.get().map(|fill| fill.kind)
    }

    /// How the model of the session's last request is paid for: a plan
    /// login, an API key or a local model; an API key before the
    /// session's first request and for a gate whose runs do not fill.
    /// Blocking file IO.
    #[must_use]
    pub fn auth(&self) -> AuthClass {
        self.facts().auth
    }

    /// The plan notices of the session's requests: a plan window's last
    /// reading passed the line while limits are off.
    #[must_use]
    pub fn plan_notices(&self) -> broadcast::Receiver<PlanNotice> {
        self.runs.notices.subscribe()
    }

    /// The facts of the session now.
    pub(super) fn facts(&self) -> RunFacts {
        match self.runs.fill.get() {
            None => RunFacts::side(),
            Some(fill) => {
                let seen = self
                    .runs
                    .seen
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .clone();
                (fill.facts)(seen.as_ref())
            }
        }
    }

    /// Starts a new run: fills its limits and opens or renews the
    /// session's account with them, the run's spend counted from now. A
    /// session that draws from another account (a child) runs in its
    /// parent's: nothing changes (`None`). Blocking file IO.
    ///
    /// # Errors
    ///
    /// A profile or preset that is no limit, an unknown preset, and the
    /// ledger's or the compiled core's failures: the budget is as it was.
    pub fn start_run(&self, start: RunStart) -> Result<Option<BudgetReport>, RunError> {
        let _serial = self
            .runs
            .starting
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        self.begin(start, Begin::New)
    }

    /// Sets the limits of the session's current run, as the principal asks
    /// them over what was set for it before (a dimension left unset fills
    /// as at the run's start): the run's budget is replaced from now, its
    /// spend still counted from its start. Blocking file IO.
    ///
    /// # Errors
    ///
    /// [`LedgerError::NotRoot`] for a session that draws from another
    /// account, and the failures of [`Self::start_run`].
    pub fn set(&self, limits: impl Into<RunLimits>) -> Result<BudgetReport, RunError> {
        self.set_current(limits.into(), Vec::new(), None)
    }

    /// [`Self::set`] with `/b` presets after the run's own (a `/b`
    /// message that joins the running run).
    ///
    /// # Errors
    ///
    /// As [`Self::set`].
    pub fn set_asked(
        &self,
        limits: RunLimits,
        presets: Vec<String>,
    ) -> Result<BudgetReport, RunError> {
        self.set_current(limits, presets, None)
    }

    /// Sets what the principal asks of every run of the session (flags, a
    /// create config, the SDK); the current run fills with it now.
    /// Blocking file IO.
    ///
    /// # Errors
    ///
    /// As [`Self::set`].
    pub fn set_standing(&self, limits: impl Into<RunLimits>) -> Result<BudgetReport, RunError> {
        self.set_current(RunLimits::default(), Vec::new(), Some(limits.into()))
    }

    /// Sets limits for the session's next run, as the principal asks them
    /// while the session runs nothing (`/budget set` while idle) over what
    /// was set for it before: the next run starts with them, the `/b`
    /// pairs of its message over them. Returns the report that shows them.
    /// Blocking file IO.
    ///
    /// # Errors
    ///
    /// The ledger does not read.
    pub fn set_next(&self, limits: RunLimits) -> Result<BudgetReport, LedgerError> {
        self.change_next(|next| next.limits = limits.over(next.limits))
    }

    /// Adds `amounts` to the session's next run (`/budget add` while
    /// idle): a dimension the run leaves unlimited takes the amount as its
    /// limit. Returns the report that shows them. Blocking file IO.
    ///
    /// # Errors
    ///
    /// The ledger does not read.
    pub fn add_next(&self, amounts: BudgetAmounts) -> Result<BudgetReport, LedgerError> {
        self.change_next(|next| {
            next.added = BudgetDimension::ALL
                .into_iter()
                .fold(next.added, |sum, dimension| {
                    sum.with(
                        dimension,
                        sum.get(dimension).saturating_add(amounts.get(dimension)),
                    )
                });
        })
    }

    /// Change what the next run starts with while no run starts; the
    /// report that shows it ([`Self::shown_report`]), published.
    fn change_next(&self, change: impl FnOnce(&mut NextRun)) -> Result<BudgetReport, LedgerError> {
        {
            let _serial = self
                .runs
                .starting
                .lock()
                .unwrap_or_else(PoisonError::into_inner);
            change(
                &mut self
                    .runs
                    .next
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner),
            );
        }
        if let Some(report) = self.read()? {
            return Ok(report);
        }
        let report = self.next_only();
        self.publish(&report);
        Ok(report)
    }

    /// What `/budget` shows: the budget's report ([`Self::report`]), or,
    /// for a session without a budget yet, a report of nothing but the
    /// limits set or added for its next run; `None` without either.
    /// Blocking file IO.
    #[must_use]
    pub fn shown_report(&self) -> Option<BudgetReport> {
        self.report()
            .or_else(|| Some(self.next_only()).filter(|report| report.next.is_some()))
    }

    /// A report of nothing but what the next run starts with.
    fn next_only(&self) -> BudgetReport {
        self.with_next(BudgetReport {
            session_id: self.agent().to_owned(),
            agent_session_id: self.agent().to_owned(),
            ..BudgetReport::default()
        })
    }

    fn set_current(
        &self,
        set: RunLimits,
        presets: Vec<String>,
        standing: Option<RunLimits>,
    ) -> Result<BudgetReport, RunError> {
        let _serial = self
            .runs
            .starting
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        let kind = self
            .ledger
            .run()?
            .map(|run| run.kind)
            .or_else(|| self.run_kind())
            .unwrap_or_default();
        self.begin(
            RunStart {
                kind,
                set,
                presets,
                standing,
            },
            Begin::Current,
        )?
        .ok_or_else(|| LedgerError::NotRoot(self.agent().to_owned()).into())
    }

    /// [`Self::start_run`] or [`Self::set`] while this gate starts no
    /// other run.
    fn begin(&self, start: RunStart, begin: Begin) -> Result<Option<BudgetReport>, RunError> {
        let facts = self.facts();
        let current = self.ledger.run()?;
        let standing = start
            .standing
            .or_else(|| current.as_ref().map(|run| run.standing))
            .unwrap_or_default();
        // A new run starts with what the principal set or added while the
        // session was idle (its message's `/b` pairs over it); it is used
        // up once the run started.
        let next = match begin {
            Begin::New => self
                .runs
                .next
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .clone(),
            Begin::Current => NextRun::default(),
        };
        let (mut asked, names) = match (begin, &current) {
            (Begin::Current, Some(run)) => (
                start.set.over(run.asked),
                run.presets.iter().cloned().chain(start.presets).collect(),
            ),
            (Begin::New | Begin::Current, _) => (start.set.over(next.limits), start.presets),
        };
        let kind = core_kind(start.kind);
        let auth = core_auth(facts.auth);
        let presets = names
            .iter()
            .map(|name| match entry(&facts.presets, name) {
                Value::Null => match name.as_str() {
                    "quick" => Ok(run_limits(&core::preset(core::Scale::Quick, kind, auth)?)),
                    "deep" => Ok(run_limits(&core::preset(core::Scale::Deep, kind, auth)?)),
                    _ => Err(RunError::Preset(name.clone())),
                },
                preset => layer(&format!("presets.{name}"), preset),
            })
            .collect::<Result<Vec<RunLimits>, RunError>>()?;
        let own = layer(
            &format!("profile.{}", start.kind.slug()),
            entry(&facts.profile, start.kind.slug()),
        )?;
        let fill = |asked: &RunLimits| {
            core::fill(
                match facts.limits {
                    BudgetLimitsMode::Off => core::Toggle::Off,
                    BudgetLimitsMode::On => core::Toggle::On,
                },
                kind,
                auth,
                &core_lims(&asked.over(standing)),
                &presets.iter().map(core_lims).collect::<Vec<_>>(),
                &core_lims(&own),
            )
        };
        let mut filled = fill(&asked)?;
        // What was added for the next run: a dimension the run leaves
        // unlimited takes the amount as its limit, set by the principal; a
        // limited one grows by it.
        let first_fill = run_limits(&filled.lims).counted();
        let taken = BudgetDimension::ALL
            .into_iter()
            .filter(|dimension| {
                next.added.get(*dimension) > 0 && first_fill.get(*dimension).is_none()
            })
            .fold(RunLimits::default(), |taken, dimension| {
                taken.with(dimension, Some(LimitValue::At(next.added.get(dimension))))
            });
        if !taken.is_unset() {
            asked = taken.over(asked);
            filled = fill(&asked)?;
        }
        let source = |src: core::Src| match src {
            core::Src::UntilFinished => LimitSource::UntilFinished,
            core::Src::Set => LimitSource::Set,
            core::Src::LimitsProfile => LimitSource::LimitsProfile,
            core::Src::Profile => LimitSource::Profile,
            core::Src::Preset(place) => {
                LimitSource::Preset(names.get(place).cloned().unwrap_or_default())
            }
        };
        let sources = BudgetSources {
            cost_micros: source(filled.srcs.cost),
            tokens: source(filled.srcs.tok),
            time_ms: source(filled.srcs.ms),
            tool_calls: source(filled.srcs.calls),
            requests: source(filled.srcs.reqs),
        };
        let first = current.is_none();
        let run = RunRecord {
            kind: start.kind,
            sources,
            standing,
            asked,
            presets: names,
        };
        let limits = BudgetDimension::ALL.into_iter().fold(
            run_limits(&filled.lims).counted(),
            |limits, dimension| match (limits.get(dimension), taken.get(dimension)) {
                (Some(limit), None) => limits.with(
                    dimension,
                    Some(limit.saturating_add(next.added.get(dimension))),
                ),
                (None, _) | (Some(_), Some(_)) => limits,
            },
        );
        let started = match begin {
            Begin::New => self.ledger.start_run(limits, run),
            Begin::Current => self.ledger.set_run(limits, run),
        };
        match started {
            Ok(report) => {
                if begin == Begin::New {
                    *self
                        .runs
                        .next
                        .lock()
                        .unwrap_or_else(PoisonError::into_inner) = NextRun::default();
                }
                if begin == Begin::New || first {
                    self.runs.fresh.store(true, Ordering::Relaxed);
                }
                self.changed(&report);
                Ok(Some(report))
            }
            // A child runs in its parent's account.
            Err(LedgerError::NotRoot(_)) => Ok(None),
            Err(error) => Err(error.into()),
        }
    }

    /// The first effect of a session that fills its runs and has no
    /// budget starts its first run. Blocking file IO.
    pub(super) fn ensure_run(&self) -> Result<(), RunError> {
        if let Some(fill) = self.runs.fill.get() {
            let _serial = self
                .runs
                .starting
                .lock()
                .unwrap_or_else(PoisonError::into_inner);
            if !self.ledger.exists() {
                self.begin(
                    RunStart {
                        kind: fill.kind,
                        ..RunStart::default()
                    },
                    Begin::New,
                )?;
            }
        }
        Ok(())
    }

    /// Before a work request of the agent to `model` that asks at least
    /// `first` beside its final-answer reserve `keep`: the session's first
    /// run starts; the run's first work request must fit its limits (the
    /// floor); a plan login's quota at its share wraps the run up (limits
    /// on) or is told once (limits off). Blocking file IO.
    pub(super) fn check_work(
        &self,
        model: &SeenModel,
        first: BudgetAmounts,
        keep: BudgetAmounts,
    ) -> Result<Checked, RunError> {
        self.ensure_run()?;
        if self.runs.fresh.swap(false, Ordering::Relaxed) {
            if let Some(report) = self.read()? {
                let first = clipped(first, &report, keep);
                if let Some(short) = eukhe_budget::floor(&report.limits, first, keep)? {
                    return Ok(Checked::Floor(super::notices::floor_text(
                        short,
                        &report.limits,
                        first,
                        keep,
                    )));
                }
            }
        }
        let Some(fill) = self.runs.fill.get() else {
            return Ok(Checked::Go);
        };
        let facts = (fill.facts)(Some(model));
        if facts.auth != AuthClass::Plan {
            return Ok(Checked::Go);
        }
        let Some(quota) = QuotaBoard::latest(&model.provider) else {
            return Ok(Checked::Go);
        };
        let reserve = facts.plan_reserve.saturating_mul(10);
        match facts.limits {
            BudgetLimitsMode::On => {
                let used: Vec<u64> = quota
                    .windows
                    .iter()
                    .map(|window| u64::from(window.used_permille))
                    .collect();
                let Some(wrapped_by) = core::plan_wraps(&used, reserve)? else {
                    return Ok(Checked::Go);
                };
                let plan = PlanShare {
                    reserve_percent: facts.plan_reserve,
                    windows: quota.windows,
                    wrapped_by,
                };
                match self.ledger.plan_wrap(self.agent(), plan.clone()) {
                    Ok(report) => {
                        self.publish(&report);
                        Ok(Checked::Plan(plan))
                    }
                    // A ledger without the agent: nothing to wrap up.
                    Err(LedgerError::NoBudget(_) | LedgerError::NotMember(_)) => Ok(Checked::Go),
                    Err(error) => Err(error.into()),
                }
            }
            BudgetLimitsMode::Off => {
                self.tell_plan(&quota, reserve, facts.plan_reserve)?;
                Ok(Checked::Go)
            }
        }
    }

    /// Tells each window of `quota` at or past `1000 - reserve` permille
    /// used that was not told since a reading below it.
    fn tell_plan(
        &self,
        quota: &PlanQuota,
        reserve: u64,
        reserve_percent: u64,
    ) -> Result<(), RunError> {
        let windows: Vec<core::Window> = quota
            .windows
            .iter()
            .map(|window| core::Window {
                label: window.label.clone(),
                used_permille: u64::from(window.used_permille),
            })
            .collect();
        let now = {
            let mut told = TOLD.lock().unwrap_or_else(PoisonError::into_inner);
            let labels = told.entry(quota.provider.clone()).or_default();
            let answer = core::plan_notice(&windows, reserve, labels)?;
            *labels = answer.told;
            answer.now
        };
        for place in now {
            if let Some(window) = quota.windows.get(place) {
                // No subscriber is no error: the surfaces that show
                // notices subscribe at their start.
                let _ = self.runs.notices.send(PlanNotice {
                    provider: quota.provider.clone(),
                    window: window.clone(),
                    reserve_percent,
                });
            }
        }
        Ok(())
    }
}

/// `first` as the ledger reserves it on an account holding exactly the
/// limits of `report` (B2, B17): with a time limit, its duration cut to
/// the time the final-answer reserve `keep` leaves, never below the
/// request's floor (an ask below the floor keeps its own).
fn clipped(first: BudgetAmounts, report: &BudgetReport, keep: BudgetAmounts) -> BudgetAmounts {
    match report.limits.time_ms {
        Some(limit) if first.time_ms > REQUEST_MIN_MS => BudgetAmounts {
            time_ms: first
                .time_ms
                .min(limit.saturating_sub(keep.time_ms).max(REQUEST_MIN_MS)),
            ..first
        },
        Some(_) | None => first,
    }
}

/// The [`RunFacts`] of a session whose settings are `settings`, its
/// credentials in `<agent_dir>/auth.json`: a provider logged in by OAuth
/// is a plan, one with a key (stored or from the environment) an API key,
/// a model the catalog prices at nothing without a stored credential a
/// local model. Before the session's first request: an API key.
pub(crate) fn session_facts(
    settings: Arc<crate::durable::settings::EukheSettings>,
    agent_dir: std::path::PathBuf,
) -> RunFactsFn {
    Arc::new(move |model: Option<&SeenModel>| {
        let manager = settings.manager();
        let stored = model.and_then(|model| {
            let text = std::fs::read_to_string(agent_dir.join("auth.json")).ok()?;
            let document: Value = serde_json::from_str(&text).ok()?;
            document
                .get(&model.provider)?
                .get("type")?
                .as_str()
                .map(str::to_owned)
        });
        let auth = match (stored.as_deref(), model) {
            (Some("oauth"), _) => AuthClass::Plan,
            (None, Some(model)) if !model.priced => AuthClass::Local,
            (Some(_) | None, _) => AuthClass::ApiKey,
        };
        RunFacts {
            auth,
            limits: manager.get_budget_limits(),
            plan_reserve: manager.get_budget_plan_reserve(),
            profile: manager.get_budget_profile(),
            presets: manager.get_budget_presets(),
        }
    })
}

#[cfg(test)]
mod tests;
