//! Runs of a root account: a new run renews the account's limits from
//! now and counts the spend since its start; the principal's limits for
//! the current run replace them and keep its start; a plan share reached
//! wraps the run up.

use eukhe_bend::rules::limits::{self as limits_core, renew, Lims, Val};
use eukhe_types::budget::{
    BudgetAmounts, BudgetDimension, BudgetLimits, BudgetPhase, BudgetReport, LimitSource, NextRun,
    PlanShare, BUDGET_AMOUNT_MAX,
};

use super::{resume, standing, Ledger, LedgerError, Locked, OpenMode, Standing};
use crate::amounts::{add, dimension, limits_amounts, mask, to_amt, to_ask, unlimited};
use crate::record::{Account, Op, RunRecord, State};

/// Where a renewal counts the run's spend from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Mark {
    /// A new run: from the account's spend now.
    Now,
    /// The current run: from its start.
    Kept,
}

/// `limits` as the core's limits: a dimension without a limit is
/// unlimited.
fn lims(limits: &BudgetLimits) -> Lims {
    let val = |limit: Option<u64>| limit.map_or(Val::Unlimited, Val::At);
    Lims {
        cost: val(limits.cost_micros),
        tok: val(limits.tokens),
        ms: val(limits.time_ms),
        calls: val(limits.tool_calls),
        reqs: val(limits.requests),
    }
}

/// The first dimension in which `limits` cannot hold a run's first work
/// request `first` beside its final-answer reserve `keep` (time: their
/// durations), if any: a run that starts below this floor sends nothing.
///
/// # Errors
///
/// A failure of the compiled core.
pub fn floor(
    limits: &BudgetLimits,
    first: BudgetAmounts,
    keep: BudgetAmounts,
) -> Result<Option<BudgetDimension>, eukhe_bend::Error> {
    Ok(limits_core::floor(&lims(limits), to_ask(first), to_ask(keep))?.map(dimension))
}

/// `state` renewed to `limits` at `now_ms` for `run`: the spend moves to
/// where the new limits count it (limited: the account, unlimited: the
/// tally); in each limited dimension what is free is the limit less what
/// the run used since `mark` (with what is held and lent); a time limit
/// puts the deadline `time_ms` from now, none removes it; every agent of
/// the account works again.
pub(super) fn renewed(
    state: &State,
    limits: &BudgetLimits,
    run: &RunRecord,
    now_ms: u64,
    mark: BudgetAmounts,
    program_runs: u64,
) -> Result<State, LedgerError> {
    let amounts = limits_amounts(limits);
    let until = limits
        .time_ms
        .map_or(BUDGET_AMOUNT_MAX, |ms| now_ms.saturating_add(ms));
    if until > BUDGET_AMOUNT_MAX
        || BudgetDimension::ALL
            .into_iter()
            .any(|dimension| amounts.get(dimension) > BUDGET_AMOUNT_MAX)
    {
        return Err(LedgerError::TooLarge);
    }
    let total = add(state.account.spent, state.tally);
    let account = Account {
        free: mask(state.account.free, limits),
        spent: mask(total, limits),
        over: mask(state.account.over, limits),
        until: BUDGET_AMOUNT_MAX,
        ..state.account.clone()
    };
    let acct = renew(
        &lims(limits),
        to_amt(mask(mark, limits)),
        now_ms,
        &account.to_acct(),
    )?;
    let mut next = state.clone();
    let members = resume(std::mem::take(&mut next.members));
    let account = Account::from_acct(&acct, std::mem::take(&mut next.account.holds), None);
    Ok(State {
        account,
        limits: *limits,
        members,
        run: Some(run.clone()),
        tally: unlimited(total, limits),
        mark,
        program_runs,
        plan: None,
        ..next
    })
}

/// `run` with each dimension that `before` leaves unlimited and `after`
/// limits recorded as set by the principal: budget added to or limits put
/// on the run (B16).
pub(super) fn set_where_limited(
    run: Option<&RunRecord>,
    before: &BudgetLimits,
    after: &BudgetLimits,
) -> Option<RunRecord> {
    run.map(|run| RunRecord {
        sources: BudgetDimension::ALL
            .into_iter()
            .filter(|dimension| before.get(*dimension).is_none() && after.get(*dimension).is_some())
            .fold(run.sources.clone(), |sources, dimension| {
                sources.with(dimension, LimitSource::Set)
            }),
        ..run.clone()
    })
}

/// `state` with `agent` wrapping up at the plan share `plan`.
pub(super) fn plan_wrapped(
    state: &State,
    agent: &str,
    plan: &PlanShare,
) -> Result<State, LedgerError> {
    if !state.members.contains_key(agent) {
        return Err(LedgerError::NotMember(agent.to_owned()));
    }
    let members = state
        .members
        .iter()
        .map(|(name, current)| {
            let member = if name == agent && current.phase == BudgetPhase::Working {
                crate::record::Member {
                    phase: BudgetPhase::WrapUp,
                    short: None,
                    ..current.clone()
                }
            } else {
                current.clone()
            };
            (name.clone(), member)
        })
        .collect();
    Ok(State {
        members,
        plan: Some(plan.clone()),
        ..state.clone()
    })
}

fn renew_op(
    state: Option<&State>,
    session_id: &str,
    limits: BudgetLimits,
    run: RunRecord,
    mark: Mark,
    now: u64,
) -> Result<Op, LedgerError> {
    match state {
        None => Ok(Op::Open {
            agent: session_id.to_owned(),
            limits,
            deadline_ms: limits.time_ms.map(|ms| now.saturating_add(ms)),
            parent: None,
            run: Some(run),
        }),
        Some(state) if !matches!(standing(state), Standing::Root) => {
            Err(LedgerError::NotRoot(session_id.to_owned()))
        }
        Some(state) => {
            let (mark, program_runs, next_run) = match mark {
                Mark::Now => (add(state.account.spent, state.tally), 0, NextRun::default()),
                Mark::Kept => (state.mark, state.program_runs, state.next_run.clone()),
            };
            Ok(Op::Renew {
                limits,
                run,
                now_ms: now,
                mark,
                program_runs,
                next_run,
            })
        }
    }
}

fn next_run_op(
    state: Option<&State>,
    session_id: &str,
    change: impl FnOnce(&NextRun) -> NextRun,
) -> Result<(Option<Op>, Op), LedgerError> {
    let current = match state {
        None => None,
        Some(state) if !matches!(standing(state), Standing::Root) => {
            return Err(LedgerError::NotRoot(session_id.to_owned()));
        }
        Some(state) => Some(state.next_run.clone()),
    };
    let open = current.is_none().then(|| Op::Open {
        agent: session_id.to_owned(),
        limits: BudgetLimits::default(),
        deadline_ms: None,
        parent: None,
        run: None,
    });
    let next_run = change(&current.unwrap_or_default());
    Ok((open, Op::NextRun { next_run }))
}

impl Ledger {
    /// Starts a run of a root session with `limits` (a deadline
    /// `limits.time_ms` from now): opens its account when it has none,
    /// else renews it, the run's spend counted from now.
    ///
    /// # Errors
    ///
    /// [`LedgerError::NotRoot`] for a session that draws from another
    /// account or was given a budget by its parent,
    /// [`LedgerError::TooLarge`], and the file's or the core's failures.
    pub fn start_run(
        &self,
        limits: BudgetLimits,
        run: RunRecord,
    ) -> Result<BudgetReport, LedgerError> {
        self.renew(limits, run, Mark::Now)
    }

    /// Sets the limits of the session's current run (its account opens
    /// when it has none): the run's spend still counts from its start, its
    /// program runs stay.
    ///
    /// # Errors
    ///
    /// As [`Self::start_run`].
    pub fn set_run(
        &self,
        limits: BudgetLimits,
        run: RunRecord,
    ) -> Result<BudgetReport, LedgerError> {
        self.renew(limits, run, Mark::Kept)
    }

    fn renew(
        &self,
        limits: BudgetLimits,
        run: RunRecord,
        mark: Mark,
    ) -> Result<BudgetReport, LedgerError> {
        if self.link_path().is_file() {
            return Err(LedgerError::NotRoot(self.session_id.clone()));
        }
        let Some(locked) = Locked::open(&self.path(), OpenMode::Create)? else {
            return Err(LedgerError::NoBudget(self.session_id.clone()));
        };
        let now = (self.clock)();
        let op = renew_op(locked.state(), &self.session_id, limits, run, mark, now)?;
        let (locked, _) = locked.apply(op, now)?;
        Ok(locked.report(&self.session_id, &self.session_id, now))
    }

    /// The run the session's own account records, if any.
    ///
    /// # Errors
    ///
    /// The file's failures.
    pub fn run(&self) -> Result<Option<RunRecord>, LedgerError> {
        Ok(Locked::open(&self.path(), OpenMode::Existing)?
            .and_then(|locked| locked.state().and_then(|state| state.run.clone())))
    }

    /// What the principal set or added for the session's next run, as its
    /// own account records it; nothing without one.
    ///
    /// # Errors
    ///
    /// The file's failures.
    pub fn next_run(&self) -> Result<NextRun, LedgerError> {
        Ok(Locked::open(&self.path(), OpenMode::Existing)?
            .and_then(|locked| locked.state().map(|state| state.next_run.clone()))
            .unwrap_or_default())
    }

    /// Whether the session's first effect starts a run: it has no budget,
    /// or owns a root account that no run started yet (one opened by
    /// limits set for its next run while it was idle, or written before
    /// runs were recorded).
    ///
    /// # Errors
    ///
    /// The file's failures.
    pub fn awaits_run(&self) -> Result<bool, LedgerError> {
        if self.link_path().is_file() {
            return Ok(false);
        }
        Ok(Locked::open(&self.path(), OpenMode::Existing)?
            .and_then(|locked| {
                locked
                    .state()
                    .map(|state| state.run.is_none() && matches!(standing(state), Standing::Root))
            })
            .unwrap_or(true))
    }

    /// Sets what the session's next run starts with to `change` of what
    /// was set for it before, while the session runs nothing; a session
    /// without a budget first opens its account, unlimited and without a
    /// run. The record is on disk before this returns: a crash before the
    /// next run never loses it, and the run that starts takes it in its own
    /// record ([`Self::start_run`]).
    ///
    /// # Errors
    ///
    /// [`LedgerError::NotRoot`] for a session that draws from another
    /// account or was given a budget by its parent, and the file's or the
    /// core's failures.
    pub fn change_next_run(
        &self,
        change: impl FnOnce(&NextRun) -> NextRun,
    ) -> Result<BudgetReport, LedgerError> {
        if self.link_path().is_file() {
            return Err(LedgerError::NotRoot(self.session_id.clone()));
        }
        let Some(locked) = Locked::open(&self.path(), OpenMode::Create)? else {
            return Err(LedgerError::NoBudget(self.session_id.clone()));
        };
        let now = (self.clock)();
        let (open, op) = next_run_op(locked.state(), &self.session_id, change)?;
        let locked = locked.apply_all(open.into_iter().chain([op]), now)?;
        Ok(locked.report(&self.session_id, &self.session_id, now))
    }

    /// `agent`'s run reached its share of a plan's quota (`plan`): the
    /// agent wraps up (its final answer still admitted) until its next
    /// run.
    ///
    /// # Errors
    ///
    /// [`LedgerError::NoBudget`], [`LedgerError::NotMember`], and the
    /// file's or the core's failures.
    pub fn plan_wrap(&self, agent: &str, plan: PlanShare) -> Result<BudgetReport, LedgerError> {
        let (owner, locked) = self.lock()?;
        let now = (self.clock)();
        let (locked, _) = locked.apply(
            Op::PlanWrap {
                agent: agent.to_owned(),
                plan,
            },
            now,
        )?;
        Ok(locked.report(&owner.session_id, agent, now))
    }
}
