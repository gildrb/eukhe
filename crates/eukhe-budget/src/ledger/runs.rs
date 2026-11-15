//! Runs of a root account: a new run renews the account's limits from
//! now and counts the spend since its start; the principal's limits for
//! the current run replace them and keep its start; a plan share reached
//! wraps the run up.

use eukhe_bend::rules::limits::{self as limits_core, renew, Lims, Val};
use eukhe_types::budget::{
    BudgetAmounts, BudgetDimension, BudgetLimits, BudgetPhase, BudgetReport, LimitSource, NextRun,
    PlanShare, BUDGET_AMOUNT_MAX,
};

use super::{resume, Ledger, LedgerError, Locked};
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
    Ok(State {
        account: Account::from_acct(&acct, |id| state.account.holder(id)),
        limits: *limits,
        members: resume(&state.members),
        run: Some(run.clone()),
        tally: unlimited(total, limits),
        mark,
        program_runs,
        plan: None,
        ..state.clone()
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
    let mut next = state.clone();
    let member = next
        .members
        .get_mut(agent)
        .ok_or_else(|| LedgerError::NotMember(agent.to_owned()))?;
    if member.phase == BudgetPhase::Working {
        member.phase = BudgetPhase::WrapUp;
        member.short = None;
    }
    next.plan = Some(plan.clone());
    Ok(next)
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
        let Some(mut locked) = Locked::open(&self.path(), true)? else {
            return Err(LedgerError::NoBudget(self.session_id.clone()));
        };
        let now = (self.clock)();
        let op = match locked.state() {
            None => Op::Open {
                agent: self.session_id.clone(),
                limits,
                deadline_ms: limits.time_ms.map(|ms| now.saturating_add(ms)),
                parent: None,
                run: Some(run),
            },
            Some(state) if state.parent.is_some() || state.returned.is_some() => {
                return Err(LedgerError::NotRoot(self.session_id.clone()));
            }
            Some(state) => {
                // A new run takes what was set for it; a set of the
                // current run leaves that for the next one.
                let (mark, program_runs, next_run) = match mark {
                    Mark::Now => (add(state.account.spent, state.tally), 0, NextRun::default()),
                    Mark::Kept => (state.mark, state.program_runs, state.next_run.clone()),
                };
                Op::Renew {
                    limits,
                    run,
                    now_ms: now,
                    mark,
                    program_runs,
                    next_run,
                }
            }
        };
        locked.apply(op, now)?;
        Ok(locked.report(&self.session_id, &self.session_id, now))
    }

    /// The run the session's own account records, if any.
    ///
    /// # Errors
    ///
    /// The file's failures.
    pub fn run(&self) -> Result<Option<RunRecord>, LedgerError> {
        Ok(Locked::open(&self.path(), false)?
            .and_then(|locked| locked.state().and_then(|state| state.run.clone())))
    }

    /// What the principal set or added for the session's next run, as its
    /// own account records it; nothing without one.
    ///
    /// # Errors
    ///
    /// The file's failures.
    pub fn next_run(&self) -> Result<NextRun, LedgerError> {
        Ok(Locked::open(&self.path(), false)?
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
        Ok(Locked::open(&self.path(), false)?
            .and_then(|locked| {
                locked.state().map(|state| {
                    state.run.is_none() && state.parent.is_none() && state.returned.is_none()
                })
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
        let Some(mut locked) = Locked::open(&self.path(), true)? else {
            return Err(LedgerError::NoBudget(self.session_id.clone()));
        };
        let now = (self.clock)();
        let set = match locked.state() {
            None => None,
            Some(state) if state.parent.is_some() || state.returned.is_some() => {
                return Err(LedgerError::NotRoot(self.session_id.clone()));
            }
            Some(state) => Some(state.next_run.clone()),
        };
        if set.is_none() {
            locked.apply(
                Op::Open {
                    agent: self.session_id.clone(),
                    limits: BudgetLimits::default(),
                    deadline_ms: None,
                    parent: None,
                    run: None,
                },
                now,
            )?;
        }
        let next_run = change(&set.unwrap_or_default());
        locked.apply(Op::NextRun { next_run }, now)?;
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
        let (owner, mut locked) = self.lock()?;
        let now = (self.clock)();
        locked.apply(
            Op::PlanWrap {
                agent: agent.to_owned(),
                plan,
            },
            now,
        )?;
        Ok(locked.report(&owner, agent, now))
    }
}
