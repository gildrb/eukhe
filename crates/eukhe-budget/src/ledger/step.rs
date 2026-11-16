use super::runs;
use super::{
    add, core, dimension, from_ask, limits_amounts, mask, to_amt, to_ask, unlimited, LedgerError,
    Use, BUDGET_AMOUNT_MAX,
};
use crate::record::{
    Account, ChildCarve, HoldRecord, Member, Op, Outcome, RefusalRecord, RunRecord, State,
    UseRecord, PROGRAM_LABEL,
};
use eukhe_types::budget::{BudgetAmounts, BudgetDimension, BudgetLimits, BudgetPhase};
use std::collections::BTreeMap;

/// `limits` with `amount` added in every dimension it is non-zero in (a
/// dimension that had no limit gets one).
pub(super) fn raise(
    limits: BudgetLimits,
    amount: BudgetAmounts,
) -> Result<BudgetLimits, LedgerError> {
    BudgetDimension::ALL
        .into_iter()
        .try_fold(limits, |limits, dimension| {
            let more = amount.get(dimension);
            if more == 0 {
                return Ok(limits);
            }
            let total = limits.get(dimension).unwrap_or(0).saturating_add(more);
            if total > BUDGET_AMOUNT_MAX {
                return Err(LedgerError::TooLarge);
            }
            Ok(limits.with(dimension, Some(total)))
        })
}

pub(super) fn refusal_record(why: core::Why) -> RefusalRecord {
    match why {
        core::Why::Short(dim) => RefusalRecord::Short(dimension(dim)),
        core::Why::Held => RefusalRecord::Held,
        core::Why::Stopped => RefusalRecord::Stopped,
    }
}

pub(super) fn core_phase(phase: BudgetPhase) -> core::Phase {
    match phase {
        BudgetPhase::Working => core::Phase::Working,
        BudgetPhase::WrapUp => core::Phase::WrapUp,
        BudgetPhase::Exhausted => core::Phase::Exhausted,
    }
}
pub(super) fn core_use(use_: UseRecord) -> core::Use {
    match use_ {
        UseRecord::Work => core::Use::Work,
        UseRecord::Final => core::Use::Final,
        UseRecord::Side => core::Use::Side,
    }
}

pub(super) fn budget_phase(phase: core::Phase) -> BudgetPhase {
    match phase {
        core::Phase::Working => BudgetPhase::Working,
        core::Phase::WrapUp => BudgetPhase::WrapUp,
        core::Phase::Exhausted => BudgetPhase::Exhausted,
    }
}

/// The final-answer reserves of the members above `agent` in the account
/// (its parent, the parent's parent, up to the owner), as they were
/// asked (unmasked).
pub(super) fn above(state: &State, agent: &str) -> BudgetAmounts {
    let first = state
        .members
        .get(agent)
        .and_then(|member| member.parent.as_deref());
    // A chain longer than the members is a cycle in a forged file.
    (0..state.members.len())
        .fold((BudgetAmounts::default(), first), |(sum, at), _| {
            match at.and_then(|parent| state.members.get(parent)) {
                Some(member) => (add(sum, member.keep), member.parent.as_deref()),
                None => (sum, None),
            }
        })
        .0
}

/// `offers` of a reservation of `agent` for `use_` at `now`, each clipped
/// to the time left for it before the deadline (the reserves above and,
/// for work and a side request, its own `keep` left), never below
/// `min_ms` (an offer asking less keeps its own). Unclipped without a
/// time limit.
pub(super) fn clip_offers(
    state: &State,
    agent: &str,
    use_: Use,
    keep: BudgetAmounts,
    offers: &[BudgetAmounts],
    min_ms: u64,
    now: u64,
) -> Vec<BudgetAmounts> {
    match state.limits.time_ms {
        Some(_) => {
            let own = match use_ {
                Use::Work | Use::Side => keep.time_ms,
                Use::Final => 0,
            };
            let left = state
                .account
                .until
                .saturating_sub(now)
                .saturating_sub(above(state, agent).time_ms)
                .saturating_sub(own);
            offers
                .iter()
                .map(|offer| BudgetAmounts {
                    time_ms: if offer.time_ms <= min_ms {
                        offer.time_ms
                    } else {
                        offer.time_ms.min(left.max(min_ms))
                    },
                    ..*offer
                })
                .collect()
        }
        None => offers.to_vec(),
    }
}

/// The reserve a request of `agent` for `use_` leaves: `keep`, and for a
/// side request at least the reserve the agent's turns recorded, whichever
/// gate asks for it: one that never sent a turn (a compaction's, a
/// memory's) knows no reserve of its own (B6).
pub(super) fn side_keep(
    state: &State,
    agent: &str,
    use_: Use,
    keep: BudgetAmounts,
) -> BudgetAmounts {
    match use_ {
        Use::Side => state
            .members
            .get(agent)
            .map_or(keep, |member| BudgetAmounts {
                cost_micros: keep.cost_micros.max(member.keep.cost_micros),
                tokens: keep.tokens.max(member.keep.tokens),
                time_ms: keep.time_ms.max(member.keep.time_ms),
                tool_calls: keep.tool_calls.max(member.keep.tool_calls),
                requests: keep.requests.max(member.keep.requests),
            }),
        Use::Work | Use::Final => keep,
    }
}

/// How many agents share what is free when `agent` asks (B13): the asking
/// one and every other Working member of the account that holds nothing.
pub(super) fn sharing(state: &State, agent: &str) -> u64 {
    let waiting = state
        .members
        .iter()
        .filter(|(member, at)| {
            member.as_str() != agent
                && at.phase == BudgetPhase::Working
                && !state
                    .account
                    .holds
                    .iter()
                    .any(|hold| &hold.agent == *member)
        })
        .count();
    u64::try_from(waiting).map_or(u64::MAX, |others| others.saturating_add(1))
}

pub(super) fn use_record(use_: Use) -> UseRecord {
    match use_ {
        Use::Work => UseRecord::Work,
        Use::Final => UseRecord::Final,
        Use::Side => UseRecord::Side,
    }
}

/// The account after every open hold of `agent` was settled at its held
/// amount: what a crashed or ended agent left in flight has an unknown
/// cost, bounded by its reservation.
pub(super) fn settle_held(
    state: &State,
    agent: &str,
    before: Vec<HoldRecord>,
) -> Result<Account, LedgerError> {
    let acct = state
        .account
        .holds
        .iter()
        .filter(|hold| hold.agent == agent)
        .try_fold(state.account.to_acct(), |acct, hold| {
            core::settle(hold.id, to_amt(hold.amount), &acct)
        })?;
    Ok(Account::from_acct(&acct, before, None))
}

/// Every member back to `Working`, as after added budget or a new
/// allotment.
pub(super) fn resume(members: BTreeMap<String, Member>) -> BTreeMap<String, Member> {
    members
        .into_iter()
        .map(|(agent, member)| {
            (
                agent,
                Member {
                    phase: BudgetPhase::Working,
                    short: None,
                    ..member
                },
            )
        })
        .collect()
}

/// The state and the core's answer after `op` on `state`: the one place an
/// account's state changes, used to write a record and to audit one.
pub(super) fn step(state: &State, op: &Op) -> Result<(State, Outcome), LedgerError> {
    let next = state.clone();
    match op {
        Op::Open {
            agent,
            limits,
            deadline_ms,
            parent,
            run,
        } => step_open(
            state,
            next,
            agent,
            limits,
            *deadline_ms,
            parent.as_ref(),
            run.as_ref(),
        ),
        Op::Renew {
            limits,
            run,
            now_ms,
            mark,
            program_runs,
            next_run,
        } => step_renew(state, limits, run, *now_ms, *mark, *program_runs, next_run),
        Op::NextRun { next_run } => Ok(step_next_run(next, next_run)),
        Op::PlanWrap { agent, plan } => step_plan_wrap(state, agent, plan),
        Op::Join { agent, parent } => step_join(state, next, agent, parent),
        Op::Reserve {
            id,
            agent,
            use_,
            label,
            key,
            now_ms,
            keep,
            step,
            share,
            offers,
        } => step_reserve(
            state,
            next,
            ReserveRequest {
                id: *id,
                agent,
                use_: *use_,
                label,
                key: key.as_deref(),
                now_ms: *now_ms,
                keep: *keep,
                step: *step,
                share: *share,
                offers,
            },
        ),
        Op::Settle { id, actual } => step_settle(state, next, *id, *actual),
        Op::Recover { agent } => step_recover(state, next, agent),
        Op::Release { agent } => step_release(state, next, agent),
        Op::Carve {
            agent,
            child,
            carve,
            limits,
            now_ms,
        } => step_carve(state, next, agent, child, *carve, limits, *now_ms),
        Op::Return { account, .. } => step_return(state, next, account),
        Op::Reclaim { child, account, .. } => step_reclaim(state, next, child, account),
        Op::Fund {
            amount,
            parent,
            now_ms,
        } => step_fund(state, next, amount, parent.as_ref(), *now_ms),
        Op::Limit { limits, now_ms } => step_limit(state, next, limits, *now_ms),
    }
}

fn step_open(
    state: &State,
    mut next: State,
    agent: &str,
    limits: &BudgetLimits,
    deadline_ms: Option<u64>,
    parent: Option<&crate::record::ParentRef>,
    run: Option<&RunRecord>,
) -> Result<(State, Outcome), LedgerError> {
    let amounts = limits_amounts(limits);
    let until = deadline_ms.unwrap_or(BUDGET_AMOUNT_MAX);
    if until > BUDGET_AMOUNT_MAX
        || BudgetDimension::ALL
            .into_iter()
            .any(|dimension| amounts.get(dimension) > BUDGET_AMOUNT_MAX)
    {
        return Err(LedgerError::TooLarge);
    }
    let mut members = resume(std::mem::take(&mut next.members));
    members.entry(agent.to_owned()).or_default().parent = None;
    let opened = core::fund(
        core::Ask {
            amt: to_amt(amounts),
            ms: until,
        },
        &core::Acct::default(),
    )?;
    let next = State {
        account: Account::from_acct(&opened, std::mem::take(&mut next.account.holds), None),
        limits: *limits,
        next_id: state.next_id,
        next_carve: state.next_carve,
        members,
        parent: parent.cloned(),
        run: run.cloned(),
        ..State::default()
    };
    Ok((next, Outcome::Done))
}

fn step_renew(
    state: &State,
    limits: &BudgetLimits,
    run: &RunRecord,
    now_ms: u64,
    mark: BudgetAmounts,
    program_runs: u64,
    next_run: &eukhe_types::budget::NextRun,
) -> Result<(State, Outcome), LedgerError> {
    Ok((
        State {
            next_run: next_run.clone(),
            ..runs::renewed(state, limits, run, now_ms, mark, program_runs)?
        },
        Outcome::Done,
    ))
}

fn step_next_run(next: State, next_run: &eukhe_types::budget::NextRun) -> (State, Outcome) {
    (
        State {
            next_run: next_run.clone(),
            ..next
        },
        Outcome::Done,
    )
}

fn step_plan_wrap(
    state: &State,
    agent: &str,
    plan: &eukhe_types::budget::PlanShare,
) -> Result<(State, Outcome), LedgerError> {
    Ok((runs::plan_wrapped(state, agent, plan)?, Outcome::Done))
}

fn step_join(
    state: &State,
    next: State,
    agent: &str,
    parent: &str,
) -> Result<(State, Outcome), LedgerError> {
    if !state.members.contains_key(parent) {
        return Err(LedgerError::NotMember(parent.to_owned()));
    }
    let mut members = next.members;
    members.entry(agent.to_owned()).or_insert_with(|| Member {
        parent: Some(parent.to_owned()),
        ..Member::default()
    });
    Ok((State { members, ..next }, Outcome::Done))
}

fn step_settle(
    state: &State,
    mut next: State,
    id: u64,
    actual: BudgetAmounts,
) -> Result<(State, Outcome), LedgerError> {
    let acct = state.account.to_acct();
    let settled = core::settle(id, to_amt(mask(actual, &state.limits)), &acct)?;
    let account = Account::from_acct(&settled, std::mem::take(&mut next.account.holds), None);
    let tally = if state.run.is_some() && state.account.holds.iter().any(|hold| hold.id == id) {
        add(state.tally, unlimited(actual, &state.limits))
    } else {
        next.tally
    };
    Ok((
        State {
            account,
            tally,
            ..next
        },
        Outcome::Done,
    ))
}

fn step_recover(
    state: &State,
    mut next: State,
    agent: &str,
) -> Result<(State, Outcome), LedgerError> {
    let account = settle_held(state, agent, std::mem::take(&mut next.account.holds))?;
    Ok((State { account, ..next }, Outcome::Done))
}

fn step_release(
    state: &State,
    mut next: State,
    agent: &str,
) -> Result<(State, Outcome), LedgerError> {
    let account = settle_held(state, agent, std::mem::take(&mut next.account.holds))?;
    let mut members = next.members;
    let gone = state
        .members
        .get(agent)
        .and_then(|member| member.parent.clone());
    if let Some(up) = gone {
        members.remove(agent);
        for member in members.values_mut() {
            if member.parent.as_deref() == Some(agent) {
                member.parent = Some(up.clone());
            }
        }
    }
    Ok((
        State {
            account,
            members,
            ..next
        },
        Outcome::Done,
    ))
}

#[derive(Clone, Copy)]
struct ReserveRequest<'a> {
    id: u64,
    agent: &'a str,
    use_: UseRecord,
    label: &'a str,
    key: Option<&'a str>,
    now_ms: u64,
    keep: BudgetAmounts,
    step: BudgetAmounts,
    share: u64,
    offers: &'a [BudgetAmounts],
}

fn step_reserve(
    state: &State,
    mut next: State,
    request: ReserveRequest<'_>,
) -> Result<(State, Outcome), LedgerError> {
    let member = state
        .members
        .get(request.agent)
        .ok_or_else(|| LedgerError::NotMember(request.agent.to_owned()))?;
    let acct = state.account.to_acct();
    let (start, grant) = reserve_grant(state, &request, member.phase, &acct)?;
    let mut members = next.members;
    members.entry(request.agent.to_owned()).or_default().keep = request.keep;
    let (account, next_id, program_runs, outcome) = match grant {
        core::Grant::Granted {
            index,
            ask,
            acct,
            low,
        } => {
            let account = Account::from_acct(
                &acct,
                std::mem::take(&mut next.account.holds),
                Some(HoldRecord {
                    id: request.id,
                    agent: request.agent.to_owned(),
                    amount: from_ask(ask),
                    key: request.key.map(str::to_owned),
                }),
            );
            let program_runs = if request.label.starts_with(PROGRAM_LABEL) && state.run.is_some() {
                state.program_runs.saturating_add(1)
            } else {
                next.program_runs
            };
            (
                account,
                request.id.saturating_add(1),
                program_runs,
                Outcome::Granted {
                    index: start + index,
                    amount: from_ask(ask),
                    low,
                },
            )
        }
        core::Grant::Refused { why, phase } => {
            let after = members.entry(request.agent.to_owned()).or_default();
            after.phase = budget_phase(phase);
            if let (core::Why::Short(dim), UseRecord::Work | UseRecord::Final) = (why, request.use_)
            {
                after.short = Some(dimension(dim));
            }
            (
                next.account,
                next.next_id,
                next.program_runs,
                Outcome::Refused {
                    refusal: refusal_record(why),
                },
            )
        }
    };
    Ok((
        State {
            account,
            next_id,
            members,
            program_runs,
            ..next
        },
        outcome,
    ))
}

fn reserve_grant(
    state: &State,
    request: &ReserveRequest<'_>,
    phase: BudgetPhase,
    acct: &core::Acct,
) -> Result<(usize, core::Grant), LedgerError> {
    let offers: Vec<core::Ask> = request
        .offers
        .iter()
        .map(|offer| to_ask(mask(*offer, &state.limits)))
        .collect();
    let use_core = core_use(request.use_);
    let base = to_ask(mask(above(state, request.agent), &state.limits));
    let keep = to_ask(mask(request.keep, &state.limits));
    let (want, less) = offers.split_first().ok_or(LedgerError::NoOffer)?;
    let start = core::share_start(
        request.share,
        use_core,
        base,
        keep,
        *want,
        less,
        acct.free,
        request.now_ms,
        acct.until,
    )?;
    let (want, less) = offers
        .get(start..)
        .and_then(<[core::Ask]>::split_first)
        .ok_or(LedgerError::NoOffer)?;
    let grant = core::reserve(
        use_core,
        core_phase(phase),
        request.id,
        request.now_ms,
        base,
        keep,
        to_ask(mask(request.step, &state.limits)),
        *want,
        less,
        acct,
    )?;
    Ok((start, grant))
}

fn step_carve(
    state: &State,
    mut next: State,
    agent: &str,
    child: &str,
    carve: u64,
    limits: &BudgetLimits,
    now_ms: u64,
) -> Result<(State, Outcome), LedgerError> {
    let member = state
        .members
        .get(agent)
        .ok_or_else(|| LedgerError::NotMember(agent.to_owned()))?;
    let acct = state.account.to_acct();
    let want = core::Ask {
        amt: to_amt(mask(limits_amounts(limits), &state.limits)),
        ms: limits.time_ms.map_or_else(
            || BUDGET_AMOUNT_MAX.saturating_sub(now_ms),
            |ms| ms.min(BUDGET_AMOUNT_MAX),
        ),
    };
    let base = mask(add(member.keep, above(state, agent)), &state.limits);
    match core::carve(core_phase(member.phase), now_ms, want, to_ask(base), &acct)? {
        core::Carve::Carved {
            parent,
            child: carved,
        } => {
            let account =
                Account::from_acct(&parent, std::mem::take(&mut next.account.holds), None);
            let lent = if let Some(before) = state.children.get(child) {
                let until = before.until.max(carved.until);
                ChildCarve {
                    carve,
                    agent: agent.to_owned(),
                    limits: raise(
                        before.limits,
                        limits_amounts(limits)
                            .with(BudgetDimension::Time, until.saturating_sub(before.until)),
                    )?,
                    until,
                }
            } else {
                ChildCarve {
                    carve,
                    agent: agent.to_owned(),
                    limits: *limits,
                    until: carved.until,
                }
            };
            let mut children = next.children;
            children.insert(child.to_owned(), lent);
            Ok((
                State {
                    account,
                    next_carve: carve.saturating_add(1),
                    children,
                    ..next
                },
                Outcome::Done,
            ))
        }
        core::Carve::Kept(why) => Ok((
            next,
            Outcome::Refused {
                refusal: refusal_record(why),
            },
        )),
    }
}

fn step_return(
    state: &State,
    mut next: State,
    account: &Account,
) -> Result<(State, Outcome), LedgerError> {
    match core::close(&account.to_acct(), &core::Acct::default())? {
        core::Close::Closed { child, .. } => {
            let account = Account::from_acct(&child, std::mem::take(&mut next.account.holds), None);
            let limits = BudgetDimension::ALL.into_iter().fold(
                state.limits,
                |limits, dimension| match limits.get(dimension) {
                    Some(_) => limits.with(dimension, Some(0)),
                    None => limits,
                },
            );
            let returned = account.clone();
            let members = next
                .members
                .into_iter()
                .map(|(agent, member)| {
                    (
                        agent,
                        Member {
                            phase: BudgetPhase::Exhausted,
                            short: None,
                            ..member
                        },
                    )
                })
                .collect();
            Ok((
                State {
                    account,
                    limits,
                    members,
                    parent: None,
                    returned: Some(returned),
                    ..next
                },
                Outcome::Done,
            ))
        }
        core::Close::Busy => Ok((
            next,
            Outcome::Refused {
                refusal: RefusalRecord::Held,
            },
        )),
    }
}

fn step_reclaim(
    state: &State,
    mut next: State,
    child: &str,
    account: &Account,
) -> Result<(State, Outcome), LedgerError> {
    let acct = state.account.to_acct();
    let handed = Account {
        free: mask(account.free, &state.limits),
        spent: mask(account.spent, &state.limits),
        lent: mask(account.lent, &state.limits),
        over: mask(account.over, &state.limits),
        holds: account.holds.clone(),
        until: account.until,
    };
    match core::close(&handed.to_acct(), &acct)? {
        core::Close::Closed { parent, .. } => {
            let account =
                Account::from_acct(&parent, std::mem::take(&mut next.account.holds), None);
            let mut children = next.children;
            children.remove(child);
            Ok((
                State {
                    account,
                    children,
                    ..next
                },
                Outcome::Done,
            ))
        }
        core::Close::Busy => Ok((
            next,
            Outcome::Refused {
                refusal: RefusalRecord::Held,
            },
        )),
    }
}

fn step_fund(
    state: &State,
    mut next: State,
    amount: &BudgetAmounts,
    parent: Option<&crate::record::ParentRef>,
    now_ms: u64,
) -> Result<(State, Outcome), LedgerError> {
    let limits = raise(state.limits, *amount)?;
    let run = runs::set_where_limited(state.run.as_ref(), &state.limits, &limits);
    let timed = state.limits.time_ms.is_some();
    let ms = if timed { amount.time_ms } else { 0 };
    if state.account.until.saturating_add(ms) > BUDGET_AMOUNT_MAX {
        return Err(LedgerError::TooLarge);
    }
    let funded = core::fund(
        core::Ask {
            amt: to_amt(*amount),
            ms,
        },
        &state.account.to_acct(),
    )?;
    let mut account = Account::from_acct(&funded, std::mem::take(&mut next.account.holds), None);
    if !timed && amount.time_ms > 0 {
        let until = now_ms.saturating_add(amount.time_ms);
        if until > BUDGET_AMOUNT_MAX {
            return Err(LedgerError::TooLarge);
        }
        account = Account { until, ..account };
    }
    let members = resume(next.members);
    let (parent, returned) = match parent {
        Some(parent) => (Some(parent.clone()), None),
        None => (next.parent.clone(), next.returned.clone()),
    };
    Ok((
        State {
            account,
            limits,
            members,
            parent,
            returned,
            run,
            ..next
        },
        Outcome::Done,
    ))
}

fn step_limit(
    state: &State,
    mut next: State,
    limits: &BudgetLimits,
    now_ms: u64,
) -> Result<(State, Outcome), LedgerError> {
    let new =
        BudgetDimension::ALL
            .into_iter()
            .fold(BudgetLimits::default(), |new, dimension| {
                match (state.limits.get(dimension), limits.get(dimension)) {
                    (None, Some(limit)) => new.with(dimension, Some(limit)),
                    (Some(_), _) | (None, None) => new,
                }
            });
    let amounts = limits_amounts(&new);
    if BudgetDimension::ALL
        .into_iter()
        .any(|dimension| amounts.get(dimension) > BUDGET_AMOUNT_MAX)
    {
        return Err(LedgerError::TooLarge);
    }
    let funded = core::fund(
        core::Ask {
            amt: to_amt(amounts),
            ms: 0,
        },
        &state.account.to_acct(),
    )?;
    let mut account = Account::from_acct(&funded, std::mem::take(&mut next.account.holds), None);
    if let Some(ms) = new.time_ms {
        let until = now_ms.saturating_add(ms);
        if until > BUDGET_AMOUNT_MAX {
            return Err(LedgerError::TooLarge);
        }
        account = Account { until, ..account };
    }
    let limits = BudgetDimension::ALL
        .into_iter()
        .fold(state.limits, |limits, dimension| match new.get(dimension) {
            Some(limit) => limits.with(dimension, Some(limit)),
            None => limits,
        });
    let run = runs::set_where_limited(state.run.as_ref(), &state.limits, &limits);
    Ok((
        State {
            account,
            limits,
            run,
            ..next
        },
        Outcome::Done,
    ))
}
