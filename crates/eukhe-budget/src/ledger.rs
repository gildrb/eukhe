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
use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use eukhe_bend::rules::budget as core;
use eukhe_types::budget::{
    BudgetAmounts, BudgetDimension, BudgetLimits, BudgetReport, BUDGET_AMOUNT_MAX,
};

use crate::amounts::{
    add, counted, dimension, from_ask, limits_amounts, mask, sub, to_amt, to_ask, unlimited,
};
use crate::record::{
    Account, ChildCarve, HoldRecord, Member, Op, Outcome, ParentRef, Record, RefusalRecord, State,
};

mod file;
mod runs;
mod step;

use file::{remove_link, Locked, OpenMode};
use step::{above, clip_offers, resume, sharing, side_keep, step, use_record};

pub use runs::floor;

/// The shortest time a model request's offers are clipped to: a request
/// with less time left is refused, not sent to time out.
pub const REQUEST_MIN_MS: u64 = 30_000;

/// The shortest time a tool call's offers are clipped to.
pub const TOOL_MIN_MS: u64 = 10_000;

/// The shortest time a final answer's offers are clipped to, below the
/// least time a final answer's reserve keeps: after a work turn stopped at
/// its granted time, the final answer runs for what is left of the
/// reserve's time once the stop is settled and the answer asked; one with
/// less time left is refused.
pub const FINAL_MIN_MS: u64 = 10_000;

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

enum ReleaseAction {
    Member,
    Recover,
    None,
}

fn release_op(state: Option<&State>, agent: &str) -> ReleaseAction {
    match state {
        Some(state)
            if state
                .members
                .get(agent)
                .is_some_and(|member| member.parent.is_some()) =>
        {
            ReleaseAction::Member
        }
        Some(state) if state.account.holds.iter().any(|hold| hold.agent == agent) => {
            ReleaseAction::Recover
        }
        Some(_) | None => ReleaseAction::None,
    }
}

enum Standing<'a> {
    Root,
    Carved(&'a ParentRef),
    Returned(&'a Account),
}

#[derive(Clone, Copy)]
enum InFlight {
    Wait,
    Charge,
}

fn standing(state: &State) -> Standing<'_> {
    match (&state.parent, &state.returned) {
        (Some(parent), _) => Standing::Carved(parent),
        (None, Some(account)) => Standing::Returned(account),
        (None, None) => Standing::Root,
    }
}

/// The owner of the account a session draws from, and the account's file.
struct Owner {
    session_id: String,
    path: PathBuf,
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

fn carve_op(
    state: &State,
    agent: &str,
    child: &str,
    limits: BudgetLimits,
    carve: u64,
    now: u64,
) -> Result<(Op, BudgetLimits), LedgerError> {
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
    Ok((
        Op::Carve {
            agent: agent.to_owned(),
            child: child.to_owned(),
            carve,
            limits,
            now_ms: now,
        },
        limits,
    ))
}

fn carve_refusal(outcome: Outcome) -> Option<Refusal> {
    match outcome {
        Outcome::Done => None,
        Outcome::Granted { .. }
        | Outcome::Refused {
            refusal: RefusalRecord::Held | RefusalRecord::Stopped,
        } => Some(Refusal::Stopped),
        Outcome::Refused {
            refusal: RefusalRecord::Short(dimension),
        } => Some(Refusal::Short(dimension)),
    }
}

fn receive_op(
    state: Option<&State>,
    agent: &str,
    limits: BudgetLimits,
    until: u64,
    parent: ParentRef,
    now: u64,
) -> Option<Op> {
    let open = |parent| Op::Open {
        agent: agent.to_owned(),
        limits,
        deadline_ms: limits.time_ms.map(|_| until),
        parent: Some(parent),
        run: None,
    };
    match state {
        None => Some(open(parent)),
        Some(state) if matches!(standing(state), Standing::Carved(current) if current == &parent) => {
            None
        }
        Some(state) if matches!(standing(state), Standing::Returned(_)) => Some(open(parent)),
        Some(state) => {
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
    }
}
fn join_op(state: &State, agent: &str, parent: &str) -> Result<Option<Op>, LedgerError> {
    if state.members.contains_key(agent) {
        return Ok(None);
    }
    if !state.members.contains_key(parent) {
        return Err(LedgerError::NotMember(parent.to_owned()));
    }
    Ok(Some(Op::Join {
        agent: agent.to_owned(),
        parent: parent.to_owned(),
    }))
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

    /// The owner of the session's account and its file: itself, or the
    /// session its link names. `None`: it has neither.
    fn owner(&self) -> Result<Option<Owner>, LedgerError> {
        let own = self.path();
        if own.is_file() {
            return Ok(Some(Owner {
                session_id: self.session_id.clone(),
                path: own,
            }));
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
                Ok(Some(Owner {
                    session_id: owner.to_owned(),
                    path: self.account_path(owner),
                }))
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(None),
            Err(source) => Err(LedgerError::Io { path: link, source }),
        }
    }

    /// The session's account, locked, with its owner.
    fn lock(&self) -> Result<(Owner, Locked), LedgerError> {
        let owner = self
            .owner()?
            .ok_or_else(|| LedgerError::NoBudget(self.session_id.clone()))?;
        match Locked::open(&owner.path, OpenMode::Existing)? {
            Some(locked) if locked.state().is_some() => Ok((owner, locked)),
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
        let Some(locked) = Locked::open(&self.path(), OpenMode::Create)? else {
            return Err(LedgerError::NoBudget(self.session_id.clone()));
        };
        if locked.state().is_some() {
            return Err(LedgerError::AlreadyOpen(self.session_id.clone()));
        }
        let now = (self.clock)();
        let (locked, _) = locked.apply(
            Op::Open {
                agent: self.session_id.clone(),
                limits,
                deadline_ms: limits.time_ms.map(|ms| now.saturating_add(ms)),
                parent: None,
                run: None,
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
        if owner.session_id == self.session_id {
            return Err(LedgerError::AlreadyOpen(self.session_id.clone()));
        }
        let now = (self.clock)();
        if let Some(own) = Locked::open(&self.path(), OpenMode::Existing)? {
            let handed_back = own
                .state()
                .is_none_or(|state| matches!(standing(state), Standing::Returned(_)));
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
        let locked = match Locked::open(&owner.path, OpenMode::Existing)? {
            Some(locked) if locked.state().is_some() => locked,
            Some(_) | None => return Err(LedgerError::NoBudget(parent_session_id.to_owned())),
        };
        let empty = State::default();
        let op = join_op(
            locked.state().unwrap_or(&empty),
            &self.session_id,
            parent_session_id,
        )?;
        let locked = locked.apply_all(op, now)?;
        // The Join is on disk: the link follows, renamed into place whole.
        let link = self.link_path();
        let io = |source| LedgerError::Io {
            path: link.clone(),
            source,
        };
        if std::fs::read_to_string(&link).ok().as_deref() != Some(owner.session_id.as_str()) {
            let partial = self.dir.join(format!("{}.link.partial", self.session_id));
            let mut file = File::create(&partial).map_err(io)?;
            file.write_all(owner.session_id.as_bytes()).map_err(io)?;
            file.sync_all().map_err(io)?;
            std::fs::rename(&partial, &link).map_err(io)?;
        }
        Ok(locked.report(&owner.session_id, &self.session_id, now))
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
        match Locked::open(&owner.path, OpenMode::Existing)? {
            Some(locked) if locked.state().is_some() => Ok(Some(locked.report(
                &owner.session_id,
                agent,
                (self.clock)(),
            ))),
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
        Ok(Locked::open(&owner.path, OpenMode::Existing)?
            .as_ref()
            .and_then(Locked::state)
            .map_or_else(Default::default, |state| state.members.clone()))
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
        Ok(Locked::open(&owner.path, OpenMode::Existing)?
            .as_ref()
            .and_then(Locked::state)
            .map_or_else(Default::default, |state| {
                state
                    .children
                    .iter()
                    .filter(|(_, lent)| lent.agent == agent)
                    .map(|(child, _)| child.clone())
                    .collect()
            }))
    }

    /// The open reservations of `agent`: what it holds now, each with the
    /// key of the model request it is for. A crashed process's holds read
    /// before [`Self::recover`] settles them say what each request left
    /// counted. Empty when the session has no budget.
    ///
    /// # Errors
    ///
    /// The file's failures.
    pub fn holds(&self, agent: &str) -> Result<Vec<HoldRecord>, LedgerError> {
        let Some(owner) = self.owner()? else {
            return Ok(Vec::new());
        };
        Ok(Locked::open(&owner.path, OpenMode::Existing)?
            .as_ref()
            .and_then(Locked::state)
            .map_or_else(Default::default, |state| {
                state
                    .account
                    .holds
                    .iter()
                    .filter(|hold| hold.agent == agent)
                    .cloned()
                    .collect()
            }))
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
        self.reserve_keyed(agent, use_, label, None, keep, step, offers, min_ms)
    }

    /// [`Self::reserve`] for the model request whose idempotency key is
    /// `key`: the hold keeps the key, so a crashed process's holds say
    /// what each request left counted ([`Self::holds`]).
    ///
    /// # Errors
    ///
    /// As [`Self::reserve`].
    #[allow(clippy::too_many_arguments)] // As `reserve`, and the request's key.
    pub fn reserve_keyed(
        &self,
        agent: &str,
        use_: Use,
        label: &str,
        key: Option<&str>,
        keep: BudgetAmounts,
        step: BudgetAmounts,
        offers: &[BudgetAmounts],
        min_ms: u64,
    ) -> Result<Reserved, LedgerError> {
        let (owner, locked) = self.lock()?;
        let now = (self.clock)();
        let empty = State::default();
        let state = locked.state().unwrap_or(&empty);
        let id = state.next_id;
        let keep = side_keep(state, agent, use_, keep);
        let offers = clip_offers(state, agent, use_, keep, offers, min_ms, now);
        let share = sharing(state, agent);
        let (locked, outcome) = locked.apply(
            Op::Reserve {
                id,
                agent: agent.to_owned(),
                use_: use_record(use_),
                label: label.to_owned(),
                key: key.map(str::to_owned),
                now_ms: now,
                keep,
                step,
                share,
                offers,
            },
            now,
        )?;
        let report = locked.report(&owner.session_id, agent, now);
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
            key: None,
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
        let (owner, locked) = self.lock()?;
        let now = (self.clock)();
        let (locked, _) = locked.apply(Op::Settle { id, actual }, now)?;
        Ok(locked.report(&owner.session_id, &self.session_id, now))
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
        let (owner, locked) = self.lock()?;
        let now = (self.clock)();
        let recover = locked
            .state()
            .is_some_and(|state| state.account.holds.iter().any(|hold| hold.agent == agent))
            .then(|| Op::Recover {
                agent: agent.to_owned(),
            });
        let locked = locked.apply_all(recover, now)?;
        Ok(locked.report(&owner.session_id, agent, now))
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
        let (_, locked) = self.lock()?;
        let now = (self.clock)();
        match release_op(locked.state(), agent) {
            ReleaseAction::Member => {
                let op = Op::Release {
                    agent: agent.to_owned(),
                };
                // The link goes while the account is still locked.
                let (_locked, _) = locked.apply(op, now)?;
                remove_link(&self.dir, agent)
            }
            ReleaseAction::Recover => {
                let op = Op::Recover {
                    agent: agent.to_owned(),
                };
                locked.apply(op, now).map(drop)
            }
            ReleaseAction::None => Ok(()),
        }
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
        let (owner, locked) = self.lock()?;
        if locked
            .state()
            .is_some_and(|state| matches!(standing(state), Standing::Carved(_)))
        {
            return Err(LedgerError::NotRoot(self.session_id.clone()));
        }
        let now = (self.clock)();
        let (locked, _) = locked.apply(
            Op::Fund {
                amount: amounts,
                parent: None,
                now_ms: now,
            },
            now,
        )?;
        Ok(locked.report(&owner.session_id, &self.session_id, now))
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
        let (owner, locked) = self.lock()?;
        let now = (self.clock)();
        let limit = locked
            .state()
            .is_some_and(|state| {
                BudgetDimension::ALL.into_iter().any(|dimension| {
                    state.limits.get(dimension).is_none() && limits.get(dimension).is_some()
                })
            })
            .then_some(Op::Limit {
                limits,
                now_ms: now,
            });
        let locked = locked.apply_all(limit, now)?;
        Ok(locked.report(&owner.session_id, &self.session_id, now))
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
        let (owner, locked) = self.lock()?;
        let now = (self.clock)();
        let empty = State::default();
        let state = locked.state().unwrap_or(&empty);
        let shared = state.members.contains_key(child_session_id);
        let carve = state.next_carve;
        let (op, limits) = carve_op(state, agent, child_session_id, limits, carve, now)?;
        let (locked, outcome) = locked.apply(op, now)?;
        if let Some(refusal) = carve_refusal(outcome) {
            return Ok(CarveOutcome::Refused {
                refusal,
                report: locked.report(&owner.session_id, agent, now),
            });
        }
        let release = shared.then(|| Op::Release {
            agent: child_session_id.to_owned(),
        });
        let locked = locked.apply_all(release, now)?;
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
                session_id: owner.session_id.clone(),
                carve,
            },
        )?;
        remove_link(&self.dir, child_session_id)?;
        Ok(CarveOutcome::Carved {
            report: locked.report(&owner.session_id, agent, now),
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
        let Some(locked) = Locked::open(&self.path(), OpenMode::Create)? else {
            return Err(LedgerError::NoBudget(self.session_id.clone()));
        };
        let now = (self.clock)();
        let op = receive_op(locked.state(), &self.session_id, limits, until, parent, now);
        locked.apply_all(op, now).map(drop)
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
        let Some(parent_locked) = Locked::open(&owner.path, OpenMode::Existing)? else {
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
                    session_id: owner.session_id,
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
        let (owner, locked) = self.lock()?;
        let Some((lent, limits)) = locked.state().and_then(|state| {
            state
                .children
                .get(child_session_id)
                .map(|lent| (lent.clone(), state.limits))
        }) else {
            return Ok(ReclaimOutcome::NotLent);
        };
        let in_flight = if force {
            InFlight::Charge
        } else {
            InFlight::Wait
        };
        let Some(handed) =
            self.sibling(child_session_id)
                .hand_back(&owner.session_id, &lent, in_flight)?
        else {
            return Ok(ReclaimOutcome::Busy);
        };
        let now = (self.clock)();
        let (locked, outcome) = locked.apply(
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
                report: locked.report(&owner.session_id, &self.session_id, now),
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
        in_flight: InFlight,
    ) -> Result<Option<Account>, LedgerError> {
        let untouched = || Account {
            free: limits_amounts(&lent.limits).with(BudgetDimension::Time, 0),
            ..Account::default()
        };
        let Some(locked) = Locked::open(&self.path(), OpenMode::Existing)? else {
            return Ok(Some(untouched()));
        };
        let Some(state) = locked.state() else {
            return Ok(Some(untouched()));
        };
        match standing(state) {
            Standing::Carved(parent) if parent.session_id == parent_owner => {}
            Standing::Returned(account) => return Ok(Some(account.clone())),
            Standing::Root | Standing::Carved(_) => {
                return Ok(Some(state.returned.clone().unwrap_or_default()));
            }
        }
        let grandchildren: Vec<String> = state.children.keys().cloned().collect();
        // The child's own live children first, each forced as this one is.
        drop(locked);
        for grandchild in &grandchildren {
            if matches!(
                self.reclaim(grandchild, matches!(in_flight, InFlight::Charge))?,
                ReclaimOutcome::Busy
            ) {
                return Ok(None);
            }
        }
        let (_, locked) = self.lock()?;
        let now = (self.clock)();
        // Every agent with a hold, once each, in order.
        let agents: BTreeSet<String> = locked.state().map_or_else(Default::default, |state| {
            state
                .account
                .holds
                .iter()
                .map(|hold| hold.agent.clone())
                .collect()
        });
        let locked = match (agents.is_empty(), in_flight) {
            (false, InFlight::Wait) => return Ok(None),
            (true, InFlight::Wait | InFlight::Charge) => locked,
            (false, InFlight::Charge) => {
                locked.apply_all(agents.into_iter().map(|agent| Op::Recover { agent }), now)?
            }
        };
        let account = locked
            .state()
            .map_or_else(Default::default, |state| state.account.clone());
        let op = Op::Return {
            carve: lent.carve,
            account: account.clone(),
        };
        match locked.apply(op, now)? {
            (_, Outcome::Done) => Ok(Some(account)),
            (_, Outcome::Granted { .. } | Outcome::Refused { .. }) => Ok(None),
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
        let text = std::fs::read_to_string(&owner.path).map_err(|source| LedgerError::Io {
            path: owner.path.clone(),
            source,
        })?;
        drop(locked);
        replay(&owner.path, &text)
    }
}

fn replay(path: &Path, text: &str) -> Result<Audit, LedgerError> {
    let mut state = State::default();
    let mut settled = BudgetAmounts::default();
    let mut records = 0;
    let mut first_mismatch = None;
    let complete = text.rfind('\n').map_or("", |end| &text[..end]);
    for line in complete.lines() {
        let record: Record = serde_json::from_str(line).map_err(|error| LedgerError::Corrupt {
            path: path.to_path_buf(),
            line: records,
            reason: error.to_string(),
        })?;
        let replays = step(&state, &record.op).is_ok_and(|(replayed, outcome)| {
            replayed == record.state && outcome == record.outcome && record.seq == records
        });
        if first_mismatch.is_none() && !replays {
            first_mismatch = Some(records);
        }
        settled = settled_after(settled, &state, &record);
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

fn settled_after(settled: BudgetAmounts, state: &State, record: &Record) -> BudgetAmounts {
    match &record.op {
        Op::Settle { id, actual } if state.account.holds.iter().any(|hold| hold.id == *id) => {
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
        Op::Return { .. } if record.outcome == Outcome::Done => BudgetAmounts::default(),
        Op::Renew { .. } => record.state.account.spent,
        Op::Open { .. }
        | Op::Join { .. }
        | Op::Reserve { .. }
        | Op::Settle { .. }
        | Op::Carve { .. }
        | Op::Return { .. }
        | Op::Reclaim { .. }
        | Op::Fund { .. }
        | Op::Limit { .. }
        | Op::NextRun { .. }
        | Op::PlanWrap { .. } => settled,
    }
}
