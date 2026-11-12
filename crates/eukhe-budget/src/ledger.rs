//! The ledger file of one account of a task tree's budget.
//!
//! `<dir>/<owner session id>.jsonl`, one [`Record`] per line, append-only.
//! The owner is the tree's root, or a child given a budget of its own (a
//! carve). Every other agent of the tree draws from the account of the
//! agent above it: it is a member of that account and has a link file
//! `<dir>/<session id>.link` naming the account's owner, written (by an
//! atomic rename) after its `Join` record is in the account.
//!
//! Every operation resolves the account (its own file, else its link),
//! takes the account file's exclusive lock, reads the last complete line
//! (the state), asks the compiled core, appends the record and syncs it
//! before it returns: a caller acts on an answer only after it is on disk
//! (B5). The time an operation decides on is read under the lock and
//! recorded with it. A parent and its children are different processes;
//! a carve and a reclaim take the parent account's lock and then the
//! child's, always in that order; no other operation holds two.

use std::collections::{BTreeMap, BTreeSet};
use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use eukhe_bend::rules::budget as core;
use eukhe_types::budget::{
    BudgetAmounts, BudgetDimension, BudgetLimits, BudgetPhase, BudgetReport, BUDGET_AMOUNT_MAX,
};

use crate::amounts::{add, counted, dimension, from_ask, limits_amounts, mask, to_amt, to_ask};
use crate::record::{
    Account, ChildCarve, Member, Op, Outcome, ParentRef, Record, RefusalRecord, State, UseRecord,
};

/// How much of a file's end is read to find its last record before the
/// whole file is.
const TAIL_BYTES: u64 = 64 * 1024;

/// The shortest time a model request's offers are clipped to: a request
/// with less time left is refused, not sent to time out.
pub const REQUEST_MIN_MS: u64 = 30_000;

/// The shortest time a tool call's offers are clipped to.
pub const TOOL_MIN_MS: u64 = 10_000;

/// What a reservation is for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Use {
    /// Work: it must leave the agent's final-answer reserve free.
    Work,
    /// The final answer: it may use everything past the reserves of the
    /// agents above.
    Final,
    /// A side request of the agent, not its own turn (a title, a
    /// classifier, a compaction, a memory or side question): it must leave
    /// the agent's final-answer reserve free like work, is admitted while
    /// the agent can still answer (`Working`, `WrapUp`), and a refusal changes
    /// nothing of the agent: its phase stays.
    Side,
}

/// Why nothing was taken.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Refusal {
    /// No offer fits; the smallest lacks this dimension first (time: it
    /// would run past the deadline).
    Short(BudgetDimension),
    /// The agent's phase does not admit the request: work after the
    /// wrap-up, anything once exhausted.
    Stopped,
}

/// A granted reservation: settle it with [`Ledger::settle`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Reservation {
    pub id: u64,
    /// Which offer was granted, from 0 (the wanted one).
    pub index: usize,
    /// The granted offer in the dimensions the budget limits; `time_ms`:
    /// how long it may run (0 without a time limit).
    pub amount: BudgetAmounts,
    /// Two steps of the agent's `step` (this one and one more), started
    /// now, with the reserves, would not fit what was free before the
    /// grant: the budget runs low. It never depends on the offer granted.
    pub low: bool,
}

/// The answer to [`Ledger::reserve`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Reserved {
    Granted {
        reservation: Reservation,
        report: BudgetReport,
    },
    Refused {
        refusal: Refusal,
        report: BudgetReport,
    },
}

/// The answer to [`Ledger::carve`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CarveOutcome {
    /// The child's ledger holds the allotment.
    Carved { report: BudgetReport },
    /// Nothing moved.
    Refused {
        refusal: Refusal,
        report: BudgetReport,
    },
}

/// The answer to [`Ledger::reclaim`].
// One answer per reclaim, read at once and never stored: boxing the report
// would only add an allocation to every reclaim.
#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReclaimOutcome {
    /// The child's account came back: what it had free returned, its spend
    /// is this account's.
    Reclaimed {
        returned: BudgetAmounts,
        spent: BudgetAmounts,
        report: BudgetReport,
    },
    /// Nothing is lent to that child (it was reclaimed before, or never
    /// carved).
    NotLent,
    /// The child has a request in flight; ask again when it settled, or
    /// force (a child that has ended).
    Busy,
}

/// What an audit of a ledger found.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Audit {
    /// How many records the file holds.
    pub records: u64,
    /// The sum of every settled spend: settlements, recoveries, releases,
    /// and the spends of reclaimed children.
    pub settled: BudgetAmounts,
    /// What the ledger reports as spent.
    pub spent: BudgetAmounts,
    /// The first record whose state or answer the compiled core does not
    /// reproduce from the record before it.
    pub first_mismatch: Option<u64>,
}

impl Audit {
    /// The file replays to its states and the settled spends add up to
    /// the reported total.
    #[must_use]
    pub fn exact(&self) -> bool {
        self.first_mismatch.is_none() && self.settled == self.spent
    }
}

/// Why a ledger operation failed. Every failure refuses the spend.
#[derive(Debug, thiserror::Error)]
pub enum LedgerError {
    #[error("budget ledger {path}: {source}")]
    Io {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
    #[error("budget ledger {path}: record {line} does not read: {reason}")]
    Corrupt {
        path: PathBuf,
        line: u64,
        reason: String,
    },
    /// The session has no budget.
    #[error("session {0} has no budget")]
    NoBudget(String),
    /// The session already has a budget (add to it instead).
    #[error("session {0} already has a budget")]
    AlreadyOpen(String),
    /// A carved budget grows only through its parent.
    #[error("session {0} has its budget from a parent: add budget to the parent")]
    NotRoot(String),
    /// The agent draws from no budget of this account.
    #[error("session {0} is no agent of this budget")]
    NotMember(String),
    /// A child needs an allotment in every dimension its parent limits.
    #[error("the child's budget names no {} allotment, which its parent limits", .0.label())]
    NeedsAllotment(BudgetDimension),
    #[error("a budget holds at most {BUDGET_AMOUNT_MAX} per dimension")]
    TooLarge,
    #[error("a reservation needs at least one offer")]
    NoOffer,
    #[error("the compiled Bend core failed on the budget ledger: {0}")]
    Core(#[from] eukhe_bend::Error),
}

/// The ledger as one session sees it: a handle on the files. It holds no
/// state: every operation resolves the session's account and reads it
/// under its lock, so the processes of a session tree share one truth.
#[derive(Debug, Clone)]
pub struct Ledger {
    dir: PathBuf,
    session_id: String,
    clock: fn() -> u64,
}

/// The system clock, in Unix milliseconds.
fn now_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |elapsed| {
            u64::try_from(elapsed.as_millis()).unwrap_or(u64::MAX)
        })
}

/// `limits` with `amount` added in every dimension it is non-zero in (a
/// dimension that had no limit gets one).
fn raise(limits: BudgetLimits, amount: BudgetAmounts) -> Result<BudgetLimits, LedgerError> {
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

fn refusal_record(why: core::Why) -> RefusalRecord {
    match why {
        core::Why::Short(dim) => RefusalRecord::Short(dimension(dim)),
        core::Why::Held => RefusalRecord::Held,
        core::Why::Stopped => RefusalRecord::Stopped,
    }
}

fn core_phase(phase: BudgetPhase) -> core::Phase {
    match phase {
        BudgetPhase::Working => core::Phase::Working,
        BudgetPhase::WrapUp => core::Phase::WrapUp,
        BudgetPhase::Exhausted => core::Phase::Exhausted,
    }
}

/// The final-answer reserves of the members above `agent` in the account
/// (its parent, the parent's parent, up to the owner), as they were
/// asked (unmasked).
fn above(state: &State, agent: &str) -> BudgetAmounts {
    let mut sum = BudgetAmounts::default();
    let mut at = state
        .members
        .get(agent)
        .and_then(|member| member.parent.as_deref());
    // A chain longer than the members is a cycle in a forged file.
    for _ in 0..state.members.len() {
        let Some(member) = at.and_then(|parent| state.members.get(parent)) else {
            break;
        };
        sum = add(sum, member.keep);
        at = member.parent.as_deref();
    }
    sum
}

/// `offers` of a reservation of `agent` for `use_` at `now`, each clipped
/// to the time left for it before the deadline (the reserves above and,
/// for work and a side request, its own `keep` left), never below
/// `min_ms` (an offer asking less keeps its own). Unclipped without a
/// time limit.
fn clip_offers(
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
fn side_keep(state: &State, agent: &str, use_: Use, keep: BudgetAmounts) -> BudgetAmounts {
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
fn sharing(state: &State, agent: &str) -> u64 {
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

fn use_record(use_: Use) -> UseRecord {
    match use_ {
        Use::Work => UseRecord::Work,
        Use::Final => UseRecord::Final,
        Use::Side => UseRecord::Side,
    }
}

/// The account after every open hold of `agent` was settled at its held
/// amount: what a crashed or ended agent left in flight has an unknown
/// cost, bounded by its reservation.
fn settle_held(state: &State, agent: &str) -> Result<Account, LedgerError> {
    let mut acct = state.account.to_acct();
    for hold in state
        .account
        .holds
        .iter()
        .filter(|hold| hold.agent == agent)
    {
        acct = core::settle(hold.id, to_amt(hold.amount), &acct)?;
    }
    Ok(Account::from_acct(&acct, |id| state.account.holder(id)))
}

/// Every member back to `Working`, as after added budget or a new
/// allotment.
fn resume(members: &BTreeMap<String, Member>) -> BTreeMap<String, Member> {
    members
        .iter()
        .map(|(agent, member)| {
            (
                agent.clone(),
                Member {
                    phase: BudgetPhase::Working,
                    short: None,
                    ..member.clone()
                },
            )
        })
        .collect()
}

/// The state and the core's answer after `op` on `state`: the one place an
/// account's state changes, used to write a record and to audit one.
#[allow(clippy::too_many_lines)] // One arm per operation, each short.
fn step(state: &State, op: &Op) -> Result<(State, Outcome), LedgerError> {
    let mut next = state.clone();
    let acct = state.account.to_acct();
    let holder = |id| state.account.holder(id);
    let outcome =
        match op {
            Op::Open {
                agent,
                limits,
                deadline_ms,
                parent,
            } => {
                let amounts = limits_amounts(limits);
                let until = deadline_ms.unwrap_or(BUDGET_AMOUNT_MAX);
                if until > BUDGET_AMOUNT_MAX
                    || BudgetDimension::ALL
                        .into_iter()
                        .any(|dimension| amounts.get(dimension) > BUDGET_AMOUNT_MAX)
                {
                    return Err(LedgerError::TooLarge);
                }
                let mut members = resume(&state.members);
                members.entry(agent.clone()).or_default().parent = None;
                let opened = core::fund(
                    core::Ask {
                        amt: to_amt(amounts),
                        ms: until,
                    },
                    &core::Acct::default(),
                )?;
                // Ids and carve numbers go on: a late settlement of an earlier
                // budget's id never settles a new hold.
                next = State {
                    account: Account::from_acct(&opened, holder),
                    limits: *limits,
                    next_id: state.next_id,
                    next_carve: state.next_carve,
                    members,
                    parent: parent.clone(),
                    ..State::default()
                };
                Outcome::Done
            }
            Op::Join { agent, parent } => {
                if !state.members.contains_key(parent) {
                    return Err(LedgerError::NotMember(parent.clone()));
                }
                next.members.entry(agent.clone()).or_insert_with(|| Member {
                    parent: Some(parent.clone()),
                    ..Member::default()
                });
                Outcome::Done
            }
            Op::Reserve {
                id,
                agent,
                use_,
                label: _,
                now_ms,
                keep,
                step,
                share,
                offers,
            } => {
                let member = state
                    .members
                    .get(agent)
                    .ok_or_else(|| LedgerError::NotMember(agent.clone()))?;
                let offers: Vec<core::Ask> = offers
                    .iter()
                    .map(|offer| to_ask(mask(*offer, &state.limits)))
                    .collect();
                let use_core = match use_ {
                    UseRecord::Work => core::Use::Work,
                    UseRecord::Final => core::Use::Final,
                    UseRecord::Side => core::Use::Side,
                };
                let base = to_ask(mask(above(state, agent), &state.limits));
                let keep_ask = to_ask(mask(*keep, &state.limits));
                let (want, less) = offers.split_first().ok_or(LedgerError::NoOffer)?;
                // The agents that share what is free each start from an
                // offer within their share (B13).
                let start = core::share_start(
                    *share, use_core, base, keep_ask, *want, less, acct.free, *now_ms, acct.until,
                )?;
                let (want, less) = offers
                    .get(start..)
                    .and_then(<[core::Ask]>::split_first)
                    .ok_or(LedgerError::NoOffer)?;
                let grant = core::reserve(
                    use_core,
                    core_phase(member.phase),
                    *id,
                    *now_ms,
                    base,
                    keep_ask,
                    to_ask(mask(*step, &state.limits)),
                    *want,
                    less,
                    &acct,
                )?;
                let after = next.members.entry(agent.clone()).or_default();
                after.keep = *keep;
                match grant {
                    core::Grant::Granted {
                        index,
                        ask,
                        acct,
                        low,
                    } => {
                        next.account = Account::from_acct(&acct, |held| {
                            if held == *id {
                                agent.clone()
                            } else {
                                state.account.holder(held)
                            }
                        });
                        next.next_id = id.saturating_add(1);
                        Outcome::Granted {
                            index: start + index,
                            amount: from_ask(ask),
                            low,
                        }
                    }
                    core::Grant::Refused { why, phase } => {
                        after.phase = match phase {
                            core::Phase::Working => BudgetPhase::Working,
                            core::Phase::WrapUp => BudgetPhase::WrapUp,
                            core::Phase::Exhausted => BudgetPhase::Exhausted,
                        };
                        // A side request that does not fit leaves the
                        // agent as it was: its phase (the core keeps it)
                        // and what put it there.
                        if let (core::Why::Short(dim), UseRecord::Work | UseRecord::Final) =
                            (why, use_)
                        {
                            after.short = Some(dimension(dim));
                        }
                        Outcome::Refused {
                            refusal: refusal_record(why),
                        }
                    }
                }
            }
            Op::Settle { id, actual } => {
                next.account = Account::from_acct(
                    &core::settle(*id, to_amt(mask(*actual, &state.limits)), &acct)?,
                    holder,
                );
                Outcome::Done
            }
            Op::Recover { agent } => {
                next.account = settle_held(state, agent)?;
                Outcome::Done
            }
            Op::Release { agent } => {
                next.account = settle_held(state, agent)?;
                // The owner stays; a member's own members move up to its
                // parent, whose reserves they still leave.
                let gone = state
                    .members
                    .get(agent)
                    .and_then(|member| member.parent.clone());
                if let Some(up) = gone {
                    next.members.remove(agent);
                    for member in next.members.values_mut() {
                        if member.parent.as_deref() == Some(agent.as_str()) {
                            member.parent = Some(up.clone());
                        }
                    }
                }
                Outcome::Done
            }
            Op::Carve {
                agent,
                child,
                carve,
                limits,
                now_ms,
            } => {
                let member = state
                    .members
                    .get(agent)
                    .ok_or_else(|| LedgerError::NotMember(agent.clone()))?;
                let want = core::Ask {
                    amt: to_amt(mask(limits_amounts(limits), &state.limits)),
                    ms: limits.time_ms.map_or_else(
                        || BUDGET_AMOUNT_MAX.saturating_sub(*now_ms),
                        |ms| ms.min(BUDGET_AMOUNT_MAX),
                    ),
                };
                let base = mask(add(member.keep, above(state, agent)), &state.limits);
                match core::carve(core_phase(member.phase), *now_ms, want, to_ask(base), &acct)? {
                    core::Carve::Carved {
                        parent,
                        child: carved,
                    } => {
                        next.account = Account::from_acct(&parent, holder);
                        next.next_carve = carve.saturating_add(1);
                        let lent = match state.children.get(child) {
                            Some(before) => {
                                let until = before.until.max(carved.until);
                                ChildCarve {
                                    carve: *carve,
                                    agent: agent.clone(),
                                    limits: raise(
                                        before.limits,
                                        limits_amounts(limits).with(
                                            BudgetDimension::Time,
                                            until.saturating_sub(before.until),
                                        ),
                                    )?,
                                    until,
                                }
                            }
                            None => ChildCarve {
                                carve: *carve,
                                agent: agent.clone(),
                                limits: *limits,
                                until: carved.until,
                            },
                        };
                        next.children.insert(child.clone(), lent);
                        Outcome::Done
                    }
                    core::Carve::Kept(why) => Outcome::Refused {
                        refusal: refusal_record(why),
                    },
                }
            }
            Op::Return { carve: _, account } => {
                // The core empties a closed child whatever its parent holds.
                match core::close(&account.to_acct(), &core::Acct::default())? {
                    core::Close::Closed { child, .. } => {
                        next.account = Account::from_acct(&child, holder);
                        // The budget went back with the account: the limited
                        // dimensions stay limited, at nothing, and no agent is
                        // admitted until the parent lends again.
                        next.limits = BudgetDimension::ALL.into_iter().fold(
                            state.limits,
                            |limits, dimension| match limits.get(dimension) {
                                Some(_) => limits.with(dimension, Some(0)),
                                None => limits,
                            },
                        );
                        for member in next.members.values_mut() {
                            member.phase = BudgetPhase::Exhausted;
                            member.short = None;
                        }
                        next.parent = None;
                        next.returned = Some(account.clone());
                        Outcome::Done
                    }
                    core::Close::Busy => Outcome::Refused {
                        refusal: RefusalRecord::Held,
                    },
                }
            }
            Op::Reclaim {
                child,
                carve: _,
                account,
            } => {
                let handed = Account {
                    free: mask(account.free, &state.limits),
                    spent: mask(account.spent, &state.limits),
                    lent: mask(account.lent, &state.limits),
                    over: mask(account.over, &state.limits),
                    holds: account.holds.clone(),
                    until: account.until,
                };
                match core::close(&handed.to_acct(), &acct)? {
                    core::Close::Closed { parent, child: _ } => {
                        next.account = Account::from_acct(&parent, holder);
                        next.children.remove(child);
                        Outcome::Done
                    }
                    core::Close::Busy => Outcome::Refused {
                        refusal: RefusalRecord::Held,
                    },
                }
            }
            Op::Fund {
                amount,
                parent,
                now_ms,
            } => {
                next.limits = raise(state.limits, *amount)?;
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
                    &acct,
                )?;
                next.account = Account::from_acct(&funded, holder);
                if !timed && amount.time_ms > 0 {
                    // A budget without a time limit gets a deadline from now.
                    let until = now_ms.saturating_add(amount.time_ms);
                    if until > BUDGET_AMOUNT_MAX {
                        return Err(LedgerError::TooLarge);
                    }
                    next.account.until = until;
                }
                next.members = resume(&state.members);
                if let Some(parent) = parent {
                    next.parent = Some(parent.clone());
                    next.returned = None;
                }
                Outcome::Done
            }
            Op::Limit { limits, now_ms } => {
                let new = BudgetDimension::ALL.into_iter().fold(
                    BudgetLimits::default(),
                    |new, dimension| match (state.limits.get(dimension), limits.get(dimension)) {
                        (None, Some(limit)) => new.with(dimension, Some(limit)),
                        (Some(_), _) | (None, None) => new,
                    },
                );
                let amounts = limits_amounts(&new);
                if BudgetDimension::ALL
                    .into_iter()
                    .any(|dimension| amounts.get(dimension) > BUDGET_AMOUNT_MAX)
                {
                    return Err(LedgerError::TooLarge);
                }
                // An unlimited dimension holds nothing anywhere: funding it
                // makes its free the limit.
                let funded = core::fund(
                    core::Ask {
                        amt: to_amt(amounts),
                        ms: 0,
                    },
                    &acct,
                )?;
                next.account = Account::from_acct(&funded, holder);
                if let Some(ms) = new.time_ms {
                    let until = now_ms.saturating_add(ms);
                    if until > BUDGET_AMOUNT_MAX {
                        return Err(LedgerError::TooLarge);
                    }
                    next.account.until = until;
                }
                next.limits =
                    BudgetDimension::ALL
                        .into_iter()
                        .fold(state.limits, |limits, dimension| match new.get(dimension) {
                            Some(limit) => limits.with(dimension, Some(limit)),
                            None => limits,
                        });
                Outcome::Done
            }
        };
    Ok((next, outcome))
}

/// A ledger file held under its exclusive lock.
struct Locked {
    path: PathBuf,
    file: File,
    /// The last record, if the file has one.
    last: Option<Record>,
    /// Where the last complete line ends: a torn line after it is cut.
    end: u64,
}

impl Locked {
    fn io(&self, source: std::io::Error) -> LedgerError {
        LedgerError::Io {
            path: self.path.clone(),
            source,
        }
    }

    /// Opens (creating it when `create`) and locks the file, then reads
    /// its last complete line. `None`: the file does not exist.
    fn open(path: &Path, create: bool) -> Result<Option<Locked>, LedgerError> {
        let io = |source| LedgerError::Io {
            path: path.to_path_buf(),
            source,
        };
        if create {
            if let Some(dir) = path.parent() {
                std::fs::create_dir_all(dir).map_err(io)?;
            }
        }
        let file = match OpenOptions::new()
            .read(true)
            .append(true)
            .create(create)
            .open(path)
        {
            Ok(file) => file,
            Err(error) if !create && error.kind() == std::io::ErrorKind::NotFound => {
                return Ok(None)
            }
            Err(error) => return Err(io(error)),
        };
        file.lock().map_err(io)?;
        let mut locked = Locked {
            path: path.to_path_buf(),
            file,
            last: None,
            end: 0,
        };
        locked.read_last()?;
        Ok(Some(locked))
    }

    /// Reads the last complete line: the file's end first, the whole file
    /// when the end holds no complete line.
    fn read_last(&mut self) -> Result<(), LedgerError> {
        let len = self.file.metadata().map_err(|e| self.io(e))?.len();
        let mut from = len.saturating_sub(TAIL_BYTES);
        loop {
            self.file
                .seek(SeekFrom::Start(from))
                .map_err(|e| self.io(e))?;
            let mut bytes = Vec::new();
            self.file.read_to_end(&mut bytes).map_err(|e| self.io(e))?;
            // The last complete line ends at the last newline; it starts
            // after the newline before that, or at the file's start.
            let Some(last_newline) = bytes.iter().rposition(|byte| *byte == b'\n') else {
                if from == 0 {
                    self.end = 0;
                    self.last = None;
                    return Ok(());
                }
                from = 0;
                continue;
            };
            let start = bytes[..last_newline]
                .iter()
                .rposition(|byte| *byte == b'\n')
                .map(|at| at + 1);
            let start = match start {
                Some(start) => start,
                None if from == 0 => 0,
                None => {
                    from = 0;
                    continue;
                }
            };
            let line = &bytes[start..last_newline];
            let record: Record =
                serde_json::from_slice(line).map_err(|error| LedgerError::Corrupt {
                    path: self.path.clone(),
                    line: 0,
                    reason: error.to_string(),
                })?;
            self.end = from + last_newline as u64 + 1;
            self.last = Some(record);
            return Ok(());
        }
    }

    fn state(&self) -> Option<&State> {
        self.last.as_ref().map(|record| &record.state)
    }

    /// The budget as `agent` sees it at `now`, in the account of `owner`.
    fn report(&self, owner: &str, agent: &str, now: u64) -> BudgetReport {
        let empty = State::default();
        let state = self.state().unwrap_or(&empty);
        let member = state.members.get(agent);
        let phase = member.map_or(BudgetPhase::Working, |member| member.phase);
        BudgetReport {
            session_id: owner.to_owned(),
            agent_session_id: agent.to_owned(),
            limits: state.limits,
            free: BudgetAmounts {
                time_ms: match state.limits.time_ms {
                    Some(_) => state.account.until.saturating_sub(now),
                    None => 0,
                },
                ..state.account.free
            },
            held: state.account.held(),
            spent: state.account.spent,
            lent: state.account.lent,
            over: state.account.over,
            phase,
            short: match phase {
                BudgetPhase::Working => None,
                BudgetPhase::WrapUp | BudgetPhase::Exhausted => {
                    member.and_then(|member| member.short)
                }
            },
            deadline_ms: state.limits.time_ms.map(|_| state.account.until),
            parent_session_id: state
                .parent
                .as_ref()
                .map(|parent| parent.session_id.clone()),
        }
    }

    /// Applies `op` to the state, appends the record (written at `at_ms`)
    /// and syncs it.
    fn apply(&mut self, op: Op, at_ms: u64) -> Result<Outcome, LedgerError> {
        let before = self.state().cloned().unwrap_or_default();
        let (state, outcome) = step(&before, &op)?;
        let record = Record {
            seq: self.last.as_ref().map_or(0, |record| record.seq + 1),
            at_ms,
            op,
            outcome,
            state,
        };
        let mut line = serde_json::to_vec(&record).map_err(|error| LedgerError::Corrupt {
            path: self.path.clone(),
            line: record.seq,
            reason: error.to_string(),
        })?;
        line.push(b'\n');
        // A line cut short by a crash is dropped before the next record.
        let len = self.file.metadata().map_err(|e| self.io(e))?.len();
        if len != self.end {
            self.file.set_len(self.end).map_err(|e| self.io(e))?;
        }
        self.file.write_all(&line).map_err(|e| self.io(e))?;
        self.file.sync_data().map_err(|e| self.io(e))?;
        self.end += line.len() as u64;
        self.last = Some(record);
        Ok(outcome)
    }
}

/// Removes the link file of `session_id` under `dir`: it draws from no
/// shared account any more. A link that is not there is fine.
fn remove_link(dir: &Path, session_id: &str) -> Result<(), LedgerError> {
    let link = dir.join(format!("{session_id}.link"));
    match std::fs::remove_file(&link) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(source) => Err(LedgerError::Io { path: link, source }),
    }
}

impl Ledger {
    /// The ledger as `session_id` sees it under `dir` (`<agent
    /// dir>/budgets`): its own account, or the account its link names.
    /// Nothing is read until an operation.
    #[must_use]
    pub fn of(dir: &Path, session_id: &str) -> Ledger {
        Ledger {
            dir: dir.to_path_buf(),
            session_id: session_id.to_owned(),
            clock: now_ms,
        }
    }

    /// The same ledger, reading the time (Unix ms) from `clock`.
    #[must_use]
    pub fn with_clock(self, clock: fn() -> u64) -> Ledger {
        Ledger { clock, ..self }
    }

    /// The same view for another session, on the same clock.
    fn sibling(&self, session_id: &str) -> Ledger {
        Ledger {
            dir: self.dir.clone(),
            session_id: session_id.to_owned(),
            clock: self.clock,
        }
    }

    /// The session's own account file (it may have none).
    #[must_use]
    pub fn path(&self) -> PathBuf {
        self.account_path(&self.session_id)
    }

    fn account_path(&self, owner: &str) -> PathBuf {
        self.dir.join(format!("{owner}.jsonl"))
    }

    fn link_path(&self) -> PathBuf {
        self.dir.join(format!("{}.link", self.session_id))
    }

    /// The session the ledger is seen by.
    #[must_use]
    pub fn session_id(&self) -> &str {
        &self.session_id
    }

    /// Whether the session has a budget, its own or a shared one: at most
    /// two `stat`s, no lock.
    #[must_use]
    pub fn exists(&self) -> bool {
        self.path().is_file() || self.link_path().is_file()
    }

    /// Whether the session owns an account: one `stat`, no lock.
    #[must_use]
    pub fn is_owner(&self) -> bool {
        self.path().is_file()
    }

    /// The owner of the session's account: itself, or the session its link
    /// names. `None`: it has neither.
    fn owner(&self) -> Result<Option<String>, LedgerError> {
        if self.path().is_file() {
            return Ok(Some(self.session_id.clone()));
        }
        let link = self.link_path();
        match std::fs::read_to_string(&link) {
            Ok(text) => {
                let owner = text.trim();
                if owner.is_empty() || owner.contains(['/', '\\']) || owner.starts_with('.') {
                    return Err(LedgerError::Corrupt {
                        path: link,
                        line: 0,
                        reason: format!("the link names no session: {owner:?}"),
                    });
                }
                Ok(Some(owner.to_owned()))
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(None),
            Err(source) => Err(LedgerError::Io { path: link, source }),
        }
    }

    /// The session's account, locked, with its owner.
    fn lock(&self) -> Result<(String, Locked), LedgerError> {
        let owner = self
            .owner()?
            .ok_or_else(|| LedgerError::NoBudget(self.session_id.clone()))?;
        match Locked::open(&self.account_path(&owner), false)? {
            Some(locked) if locked.last.is_some() => Ok((owner, locked)),
            Some(_) | None => Err(LedgerError::NoBudget(self.session_id.clone())),
        }
    }

    /// Sets a root session's budget: the limits, and a deadline
    /// `limits.time_ms` from now.
    ///
    /// # Errors
    ///
    /// [`LedgerError::AlreadyOpen`] when the session has a budget (its own
    /// or a shared one), [`LedgerError::TooLarge`], and the file's or the
    /// core's failures.
    pub fn open_root(&self, limits: BudgetLimits) -> Result<BudgetReport, LedgerError> {
        if self.link_path().is_file() {
            return Err(LedgerError::AlreadyOpen(self.session_id.clone()));
        }
        let Some(mut locked) = Locked::open(&self.path(), true)? else {
            return Err(LedgerError::NoBudget(self.session_id.clone()));
        };
        if locked.last.is_some() {
            return Err(LedgerError::AlreadyOpen(self.session_id.clone()));
        }
        let now = (self.clock)();
        locked.apply(
            Op::Open {
                agent: self.session_id.clone(),
                limits,
                deadline_ms: limits.time_ms.map(|ms| now.saturating_add(ms)),
                parent: None,
            },
            now,
        )?;
        Ok(locked.report(&self.session_id, &self.session_id, now))
    }

    /// Makes this session (a child without a budget of its own) draw from
    /// the account of `parent_session_id`, below it. Joining again
    /// changes nothing. A session whose own account was handed back to
    /// its parent (or never got a record) sets that file aside
    /// (`<session>.jsonl.<ms>.returned`) and joins.
    ///
    /// # Errors
    ///
    /// [`LedgerError::NoBudget`] when the parent has no budget,
    /// [`LedgerError::AlreadyOpen`] when this session has a live budget of
    /// its own, [`LedgerError::NotMember`] when the parent draws from no
    /// account any more, and the file's or the core's failures.
    pub fn join(&self, parent_session_id: &str) -> Result<BudgetReport, LedgerError> {
        let owner = self
            .sibling(parent_session_id)
            .owner()?
            .ok_or_else(|| LedgerError::NoBudget(parent_session_id.to_owned()))?;
        if owner == self.session_id {
            return Err(LedgerError::AlreadyOpen(self.session_id.clone()));
        }
        let now = (self.clock)();
        if let Some(own) = Locked::open(&self.path(), false)? {
            let handed_back = own
                .state()
                .is_none_or(|state| state.parent.is_none() && state.returned.is_some());
            if !handed_back {
                return Err(LedgerError::AlreadyOpen(self.session_id.clone()));
            }
            let aside = self
                .dir
                .join(format!("{}.jsonl.{now}.returned", self.session_id));
            std::fs::rename(self.path(), &aside).map_err(|source| LedgerError::Io {
                path: self.path(),
                source,
            })?;
        }
        let mut locked = match Locked::open(&self.account_path(&owner), false)? {
            Some(locked) if locked.last.is_some() => locked,
            Some(_) | None => return Err(LedgerError::NoBudget(parent_session_id.to_owned())),
        };
        if !locked
            .state()
            .is_some_and(|state| state.members.contains_key(&self.session_id))
        {
            locked.apply(
                Op::Join {
                    agent: self.session_id.clone(),
                    parent: parent_session_id.to_owned(),
                },
                now,
            )?;
        }
        // The Join is on disk: the link follows, renamed into place whole.
        let link = self.link_path();
        let io = |source| LedgerError::Io {
            path: link.clone(),
            source,
        };
        if std::fs::read_to_string(&link).ok().as_deref() != Some(owner.as_str()) {
            let partial = self.dir.join(format!("{}.link.partial", self.session_id));
            let mut file = File::create(&partial).map_err(io)?;
            file.write_all(owner.as_bytes()).map_err(io)?;
            file.sync_all().map_err(io)?;
            std::fs::rename(&partial, &link).map_err(io)?;
        }
        Ok(locked.report(&owner, &self.session_id, now))
    }

    /// The budget as `agent` sees it; `None` when the session has none.
    ///
    /// # Errors
    ///
    /// The file's failures.
    pub fn report(&self, agent: &str) -> Result<Option<BudgetReport>, LedgerError> {
        let Some(owner) = self.owner()? else {
            return Ok(None);
        };
        match Locked::open(&self.account_path(&owner), false)? {
            Some(locked) if locked.last.is_some() => {
                Ok(Some(locked.report(&owner, agent, (self.clock)())))
            }
            Some(_) | None => Ok(None),
        }
    }

    /// The agents drawing from the session's account, the owner among
    /// them. Empty when the session has no budget.
    ///
    /// # Errors
    ///
    /// The file's failures.
    pub fn members(&self) -> Result<BTreeMap<String, Member>, LedgerError> {
        let Some(owner) = self.owner()? else {
            return Ok(BTreeMap::new());
        };
        Ok(Locked::open(&self.account_path(&owner), false)?
            .as_ref()
            .and_then(Locked::state)
            .map(|state| state.members.clone())
            .unwrap_or_default())
    }

    /// The children `agent` gave a budget of their own from the session's
    /// account and that were not reclaimed yet. Empty when the session has
    /// no budget.
    ///
    /// # Errors
    ///
    /// The file's failures.
    pub fn lent_children(&self, agent: &str) -> Result<Vec<String>, LedgerError> {
        let Some(owner) = self.owner()? else {
            return Ok(Vec::new());
        };
        Ok(Locked::open(&self.account_path(&owner), false)?
            .as_ref()
            .and_then(Locked::state)
            .map(|state| {
                state
                    .children
                    .iter()
                    .filter(|(_, lent)| lent.agent == agent)
                    .map(|(child, _)| child.clone())
                    .collect()
            })
            .unwrap_or_default())
    }

    /// Reserves for `agent` the first of `offers` (the wanted amount, then
    /// smaller ones) that fits and ends before the deadline, leaving the
    /// final-answer reserves of the agents above it; work and a side
    /// request also leave `keep` (the agent's own, recorded as its
    /// reserve). With a time limit, each offer's `time_ms` is first
    /// clipped to what is left for the agent, never below `min_ms` (an
    /// offer asking less keeps its own). A side request that does not fit
    /// changes nothing of the agent. The grant is low when two steps of
    /// `step` (the agent's largest recent step as actually spent; zero
    /// before its first) would not fit. The answer is on disk when this
    /// returns: spend only after a grant.
    ///
    /// # Errors
    ///
    /// [`LedgerError::NoBudget`], [`LedgerError::NotMember`],
    /// [`LedgerError::NoOffer`], and the file's or the core's failures:
    /// each means do not spend.
    #[allow(clippy::too_many_arguments)] // The facts of one reservation, each its own: the core's `reserve` takes them all.
    pub fn reserve(
        &self,
        agent: &str,
        use_: Use,
        label: &str,
        keep: BudgetAmounts,
        step: BudgetAmounts,
        offers: &[BudgetAmounts],
        min_ms: u64,
    ) -> Result<Reserved, LedgerError> {
        let (owner, mut locked) = self.lock()?;
        let now = (self.clock)();
        let empty = State::default();
        let state = locked.state().unwrap_or(&empty);
        let id = state.next_id;
        let keep = side_keep(state, agent, use_, keep);
        let offers = clip_offers(state, agent, use_, keep, offers, min_ms, now);
        let share = sharing(state, agent);
        let outcome = locked.apply(
            Op::Reserve {
                id,
                agent: agent.to_owned(),
                use_: use_record(use_),
                label: label.to_owned(),
                now_ms: now,
                keep,
                step,
                share,
                offers,
            },
            now,
        )?;
        let report = locked.report(&owner, agent, now);
        Ok(match outcome {
            Outcome::Granted { index, amount, low } => Reserved::Granted {
                reservation: Reservation {
                    id,
                    index,
                    amount,
                    low,
                },
                report,
            },
            Outcome::Refused {
                refusal: RefusalRecord::Short(dimension),
            } => Reserved::Refused {
                refusal: Refusal::Short(dimension),
                report,
            },
            // The id is the account's next: it is never held. An answer
            // with no grant refuses.
            Outcome::Refused {
                refusal: RefusalRecord::Held | RefusalRecord::Stopped,
            }
            | Outcome::Done => Reserved::Refused {
                refusal: Refusal::Stopped,
                report,
            },
        })
    }

    /// Whether [`Self::reserve`] for `agent` of `offers` for `use_`,
    /// leaving `keep`, would be granted now. The core answers it on the
    /// account as it is; nothing is held or written, the agent's phase
    /// does not move.
    ///
    /// # Errors
    ///
    /// [`LedgerError::NoBudget`], [`LedgerError::NotMember`],
    /// [`LedgerError::NoOffer`], and the file's or the core's failures.
    pub fn admits(
        &self,
        agent: &str,
        use_: Use,
        keep: BudgetAmounts,
        offers: &[BudgetAmounts],
        min_ms: u64,
    ) -> Result<bool, LedgerError> {
        let (_, locked) = self.lock()?;
        let now = (self.clock)();
        let empty = State::default();
        let state = locked.state().unwrap_or(&empty);
        let keep = side_keep(state, agent, use_, keep);
        let op = Op::Reserve {
            id: state.next_id,
            agent: agent.to_owned(),
            use_: use_record(use_),
            label: String::new(),
            now_ms: now,
            keep,
            // A step only says whether a grant runs low.
            step: BudgetAmounts::default(),
            share: sharing(state, agent),
            offers: clip_offers(state, agent, use_, keep, offers, min_ms, now),
        };
        let (_, outcome) = step(state, &op)?;
        Ok(match outcome {
            Outcome::Granted { .. } => true,
            Outcome::Refused { .. } | Outcome::Done => false,
        })
    }

    /// Settles the reservation `id` at what was actually spent: the rest
    /// of the hold is free again. A reservation settles once: settling it
    /// again, or an id that is not held, changes nothing. The report is
    /// this session's.
    ///
    /// # Errors
    ///
    /// [`LedgerError::NoBudget`] and the file's or the core's failures.
    pub fn settle(&self, id: u64, actual: BudgetAmounts) -> Result<BudgetReport, LedgerError> {
        let (owner, mut locked) = self.lock()?;
        let now = (self.clock)();
        locked.apply(Op::Settle { id, actual }, now)?;
        Ok(locked.report(&owner, &self.session_id, now))
    }

    /// Settles every open reservation of `agent` at its held amount: what
    /// a crashed process left in flight has an unknown cost, bounded by
    /// its reservation. Another agent's reservations are untouched. Call
    /// it when the agent's process starts, before it spends.
    ///
    /// # Errors
    ///
    /// [`LedgerError::NoBudget`] and the file's or the core's failures.
    pub fn recover(&self, agent: &str) -> Result<BudgetReport, LedgerError> {
        let (owner, mut locked) = self.lock()?;
        let now = (self.clock)();
        if locked
            .state()
            .is_some_and(|state| state.account.holds.iter().any(|hold| hold.agent == agent))
        {
            locked.apply(
                Op::Recover {
                    agent: agent.to_owned(),
                },
                now,
            )?;
        }
        Ok(locked.report(&owner, agent, now))
    }

    /// A child that shared the account ended: its open reservations are
    /// settled at their held amount, it is no member any more and its link
    /// is removed (joining again makes it one). The owner's reservations
    /// are only settled.
    ///
    /// # Errors
    ///
    /// [`LedgerError::NoBudget`] and the file's or the core's failures.
    pub fn release(&self, agent: &str) -> Result<(), LedgerError> {
        let (_, mut locked) = self.lock()?;
        let now = (self.clock)();
        let (member, holds) = locked.state().map_or((false, false), |state| {
            (
                state
                    .members
                    .get(agent)
                    .is_some_and(|member| member.parent.is_some()),
                state.account.holds.iter().any(|hold| hold.agent == agent),
            )
        });
        if member {
            locked.apply(
                Op::Release {
                    agent: agent.to_owned(),
                },
                now,
            )?;
            remove_link(&self.dir, agent)?;
        } else if holds {
            locked.apply(
                Op::Recover {
                    agent: agent.to_owned(),
                },
                now,
            )?;
        }
        Ok(())
    }

    /// Adds budget to the session's account (a root's, or one it shares):
    /// an overrun is repaid first, `amounts.time_ms` extends the deadline
    /// (or sets one from now), a dimension without a limit gets one, and
    /// every agent of the account is admitted work again.
    ///
    /// # Errors
    ///
    /// [`LedgerError::NotRoot`] for a carved budget,
    /// [`LedgerError::TooLarge`], [`LedgerError::NoBudget`], and the file's
    /// or the core's failures.
    pub fn fund(&self, amounts: BudgetAmounts) -> Result<BudgetReport, LedgerError> {
        let (owner, mut locked) = self.lock()?;
        if locked.state().is_some_and(|state| state.parent.is_some()) {
            return Err(LedgerError::NotRoot(self.session_id.clone()));
        }
        let now = (self.clock)();
        locked.apply(
            Op::Fund {
                amount: amounts,
                parent: None,
                now_ms: now,
            },
            now,
        )?;
        Ok(locked.report(&owner, &self.session_id, now))
    }

    /// Limits every dimension that had no limit and that `limits` names
    /// (time: a deadline `time_ms` from now); a dimension that has a limit
    /// keeps it (add budget to raise it).
    ///
    /// # Errors
    ///
    /// [`LedgerError::NoBudget`], [`LedgerError::TooLarge`], and the
    /// file's or the core's failures.
    pub fn limit(&self, limits: BudgetLimits) -> Result<BudgetReport, LedgerError> {
        let (owner, mut locked) = self.lock()?;
        let now = (self.clock)();
        if locked.state().is_some_and(|state| {
            BudgetDimension::ALL.into_iter().any(|dimension| {
                state.limits.get(dimension).is_none() && limits.get(dimension).is_some()
            })
        }) {
            locked.apply(
                Op::Limit {
                    limits,
                    now_ms: now,
                },
                now,
            )?;
        }
        Ok(locked.report(&owner, &self.session_id, now))
    }

    /// `agent` gives the child `child_session_id` a budget of its own out
    /// of the account: `limits` in every spent dimension the account
    /// limits (the amounts leave what is free, which keeps the reserves of
    /// `agent` and the agents above it), any limit of its own in a
    /// dimension the account leaves unlimited, and `limits.time_ms` from
    /// now (absent: what is left for `agent`). A child that drew from the
    /// account is released first; a child that has a ledger already (it
    /// was reclaimed and works again, or is lent more) is funded.
    ///
    /// # Errors
    ///
    /// [`LedgerError::NeedsAllotment`] when `limits` leaves out a spent
    /// dimension the account limits, [`LedgerError::NotMember`],
    /// [`LedgerError::NoBudget`], and the file's or the core's failures.
    pub fn carve(
        &self,
        agent: &str,
        child_session_id: &str,
        limits: BudgetLimits,
    ) -> Result<CarveOutcome, LedgerError> {
        let (owner, mut locked) = self.lock()?;
        let now = (self.clock)();
        let empty = State::default();
        let state = locked.state().unwrap_or(&empty);
        for dimension in BudgetDimension::ALL {
            if dimension != BudgetDimension::Time
                && state.limits.get(dimension).is_some()
                && limits.get(dimension).is_none()
            {
                return Err(LedgerError::NeedsAllotment(dimension));
            }
        }
        let member = state
            .members
            .get(agent)
            .ok_or_else(|| LedgerError::NotMember(agent.to_owned()))?;
        let time = match (limits.time_ms, state.limits.time_ms) {
            (Some(ms), _) => Some(ms),
            (None, Some(_)) => Some(
                state
                    .account
                    .until
                    .saturating_sub(now)
                    .saturating_sub(add(member.keep, above(state, agent)).time_ms),
            ),
            (None, None) => None,
        };
        let limits = limits.with(BudgetDimension::Time, time);
        let shared = state.members.contains_key(child_session_id);
        let carve = state.next_carve;
        let outcome = locked.apply(
            Op::Carve {
                agent: agent.to_owned(),
                child: child_session_id.to_owned(),
                carve,
                limits,
                now_ms: now,
            },
            now,
        )?;
        match outcome {
            Outcome::Done => {}
            Outcome::Refused {
                refusal: RefusalRecord::Short(dimension),
            } => {
                return Ok(CarveOutcome::Refused {
                    refusal: Refusal::Short(dimension),
                    report: locked.report(&owner, agent, now),
                })
            }
            Outcome::Refused {
                refusal: RefusalRecord::Held | RefusalRecord::Stopped,
            }
            | Outcome::Granted { .. } => {
                return Ok(CarveOutcome::Refused {
                    refusal: Refusal::Stopped,
                    report: locked.report(&owner, agent, now),
                })
            }
        }
        if shared {
            locked.apply(
                Op::Release {
                    agent: child_session_id.to_owned(),
                },
                now,
            )?;
        }
        let until = locked
            .state()
            .and_then(|state| state.children.get(child_session_id))
            .map_or(BUDGET_AMOUNT_MAX, |lent| lent.until);
        // The parent's record is on disk: the child's ledger follows, then
        // its link goes. A crash between the two leaves the allotment lent
        // and unopened; `ensure_child` (the child's start) or the reclaim
        // finds it.
        self.sibling(child_session_id).receive(
            limits,
            until,
            ParentRef {
                session_id: owner.clone(),
                carve,
            },
        )?;
        remove_link(&self.dir, child_session_id)?;
        Ok(CarveOutcome::Carved {
            report: locked.report(&owner, agent, now),
        })
    }

    /// Writes a carved allotment (`limits`, the child's deadline `until`)
    /// into this (the child's) ledger: opens it, or funds it when it holds
    /// a budget it was not handed back. A carve it already holds (the same
    /// parent and number) changes nothing.
    fn receive(
        &self,
        limits: BudgetLimits,
        until: u64,
        parent: ParentRef,
    ) -> Result<(), LedgerError> {
        let Some(mut locked) = Locked::open(&self.path(), true)? else {
            return Err(LedgerError::NoBudget(self.session_id.clone()));
        };
        let now = (self.clock)();
        let open = |parent: ParentRef| Op::Open {
            agent: self.session_id.clone(),
            limits,
            deadline_ms: limits.time_ms.map(|_| until),
            parent: Some(parent),
        };
        let op = match locked.state() {
            None => Some(open(parent)),
            Some(state) if state.parent.as_ref() == Some(&parent) => None,
            Some(state) if state.parent.is_none() && state.returned.is_some() => Some(open(parent)),
            Some(state) => {
                // The deadline moves to `until` when that is later.
                let time = if until >= BUDGET_AMOUNT_MAX {
                    0
                } else if state.limits.time_ms.is_some() {
                    until.saturating_sub(state.account.until)
                } else {
                    until.saturating_sub(now)
                };
                Some(Op::Fund {
                    amount: limits_amounts(&limits).with(BudgetDimension::Time, time),
                    parent: Some(parent),
                    now_ms: now,
                })
            }
        };
        if let Some(op) = op {
            locked.apply(op, now)?;
        }
        Ok(())
    }

    /// Makes sure this (a child's) ledger holds what its parent's account
    /// lent it: a crash between the parent's carve and the child's record
    /// left it unopened. Call it when the child's process starts. `None`:
    /// the parent has no budget or its account lent this child nothing
    /// (then the child may [`Ledger::join`] it).
    ///
    /// # Errors
    ///
    /// The file's or the core's failures.
    pub fn ensure_child(
        &self,
        parent_session_id: &str,
    ) -> Result<Option<BudgetReport>, LedgerError> {
        let Some(owner) = self.sibling(parent_session_id).owner()? else {
            return Ok(None);
        };
        let Some(parent_locked) = Locked::open(&self.account_path(&owner), false)? else {
            return Ok(None);
        };
        let Some(lent) = parent_locked
            .state()
            .and_then(|state| state.children.get(&self.session_id))
            .cloned()
        else {
            return Ok(None);
        };
        // The parent's lock is held: no carve or reclaim runs meanwhile.
        if !self.path().is_file() {
            self.receive(
                lent.limits,
                lent.until,
                ParentRef {
                    session_id: owner,
                    carve: lent.carve,
                },
            )?;
        }
        drop(parent_locked);
        self.report(&self.session_id)
    }

    /// Takes back what the child `child_session_id` was lent from the
    /// session's account: what it has free returns and its spend is added
    /// to the account's. A child with a request in flight is `Busy` unless
    /// `force` (the child has ended: what its agents left in flight is
    /// charged in full); its own live children are reclaimed first.
    /// Reclaiming again changes nothing.
    ///
    /// # Errors
    ///
    /// [`LedgerError::NoBudget`] and the file's or the core's failures.
    pub fn reclaim(
        &self,
        child_session_id: &str,
        force: bool,
    ) -> Result<ReclaimOutcome, LedgerError> {
        let (owner, mut locked) = self.lock()?;
        let Some((lent, limits)) = locked.state().and_then(|state| {
            state
                .children
                .get(child_session_id)
                .map(|lent| (lent.clone(), state.limits))
        }) else {
            return Ok(ReclaimOutcome::NotLent);
        };
        let Some(handed) = self
            .sibling(child_session_id)
            .hand_back(&owner, &lent, force)?
        else {
            return Ok(ReclaimOutcome::Busy);
        };
        let now = (self.clock)();
        let outcome = locked.apply(
            Op::Reclaim {
                child: child_session_id.to_owned(),
                carve: lent.carve,
                account: handed.clone(),
            },
            now,
        )?;
        Ok(match outcome {
            Outcome::Done => ReclaimOutcome::Reclaimed {
                returned: counted(handed.free, &limits),
                spent: counted(handed.spent, &limits),
                report: locked.report(&owner, &self.session_id, now),
            },
            Outcome::Granted { .. } | Outcome::Refused { .. } => ReclaimOutcome::Busy,
        })
    }

    /// Hands this (the child's) account back to the account of
    /// `parent_owner`: the account as it is returned, and the ledger left
    /// empty. `None`: a request is in flight and `force` is off. A ledger
    /// that was never opened hands back the untouched allotment; one that
    /// already handed back (the parent crashed before its record) hands
    /// back the same account.
    fn hand_back(
        &self,
        parent_owner: &str,
        lent: &ChildCarve,
        force: bool,
    ) -> Result<Option<Account>, LedgerError> {
        let untouched = || Account {
            free: limits_amounts(&lent.limits).with(BudgetDimension::Time, 0),
            ..Account::default()
        };
        let Some(locked) = Locked::open(&self.path(), false)? else {
            return Ok(Some(untouched()));
        };
        let Some(state) = locked.state().cloned() else {
            return Ok(Some(untouched()));
        };
        if state
            .parent
            .as_ref()
            .is_none_or(|parent| parent.session_id != parent_owner)
        {
            // Already handed back: the same account again, or, for a
            // ledger that is not this parent's child, nothing to return.
            return Ok(Some(state.returned.unwrap_or_default()));
        }
        // The child's own live children first, each forced as this one is.
        drop(locked);
        for grandchild in state.children.keys() {
            if matches!(self.reclaim(grandchild, force)?, ReclaimOutcome::Busy) {
                return Ok(None);
            }
        }
        let (_, mut locked) = self.lock()?;
        let now = (self.clock)();
        let agents: BTreeSet<String> = locked
            .state()
            .map(|state| {
                state
                    .account
                    .holds
                    .iter()
                    .map(|hold| hold.agent.clone())
                    .collect()
            })
            .unwrap_or_default();
        if !agents.is_empty() {
            if !force {
                return Ok(None);
            }
            for agent in agents {
                locked.apply(Op::Recover { agent }, now)?;
            }
        }
        let account = locked
            .state()
            .map(|state| state.account.clone())
            .unwrap_or_default();
        match locked.apply(
            Op::Return {
                carve: lent.carve,
                account: account.clone(),
            },
            now,
        )? {
            Outcome::Done => Ok(Some(account)),
            Outcome::Granted { .. } | Outcome::Refused { .. } => Ok(None),
        }
    }

    /// Replays the session's whole account file through the compiled core:
    /// every record's state and answer must be what the core gives from
    /// the record before it, and the settled spends must add up to the
    /// reported total (B9).
    ///
    /// # Errors
    ///
    /// [`LedgerError::NoBudget`], [`LedgerError::Corrupt`] for a line that
    /// does not read, and the file's failures.
    pub fn audit(&self) -> Result<Audit, LedgerError> {
        let (owner, locked) = self.lock()?;
        let path = self.account_path(&owner);
        let text = std::fs::read_to_string(&path).map_err(|source| LedgerError::Io {
            path: path.clone(),
            source,
        })?;
        drop(locked);
        let mut state = State::default();
        let mut settled = BudgetAmounts::default();
        let mut records = 0;
        let mut first_mismatch = None;
        // A last line without its newline is a record cut short by a
        // crash: it never took effect.
        let complete = text.rfind('\n').map_or("", |end| &text[..end]);
        for line in complete.lines() {
            let record: Record =
                serde_json::from_str(line).map_err(|error| LedgerError::Corrupt {
                    path: path.clone(),
                    line: records,
                    reason: error.to_string(),
                })?;
            // A record the core refuses to replay is a mismatch too.
            let replays = step(&state, &record.op).is_ok_and(|(replayed, outcome)| {
                replayed == record.state && outcome == record.outcome && record.seq == records
            });
            if first_mismatch.is_none() && !replays {
                first_mismatch = Some(records);
            }
            // What the record settled: a settlement of a held id its
            // actual spend, a recovery or a release the agent's holds, a
            // reclaim the child's spend; nothing else spends.
            settled = match &record.op {
                Op::Settle { id, actual }
                    if state.account.holds.iter().any(|hold| hold.id == *id) =>
                {
                    add(settled, counted(*actual, &state.limits))
                }
                Op::Recover { agent } | Op::Release { agent } => state
                    .account
                    .holds
                    .iter()
                    .filter(|hold| hold.agent == *agent)
                    .fold(settled, |sum, hold| add(sum, hold.amount)),
                Op::Reclaim { account, .. } if record.outcome == Outcome::Done => {
                    add(settled, counted(account.spent, &state.limits))
                }
                // A child's ledger starts over after it was handed back.
                Op::Return { .. } if record.outcome == Outcome::Done => BudgetAmounts::default(),
                Op::Open { .. }
                | Op::Join { .. }
                | Op::Reserve { .. }
                | Op::Settle { .. }
                | Op::Carve { .. }
                | Op::Return { .. }
                | Op::Reclaim { .. }
                | Op::Fund { .. }
                | Op::Limit { .. } => settled,
            };
            state = record.state;
            records += 1;
        }
        Ok(Audit {
            records,
            settled,
            spent: state.account.spent,
            first_mismatch,
        })
    }
}
