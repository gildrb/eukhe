//! The records of a ledger file: one JSON object per line, each an
//! operation, what the compiled core answered, and the state after it.
//! The last complete line is the account's state; the whole file replays
//! through the core to the same states ([`crate::Ledger::audit`]).

use std::collections::BTreeMap;

use eukhe_bend::rules::budget::{Acct, Hold};
use eukhe_types::budget::{
    BudgetAmounts, BudgetDimension, BudgetLimits, BudgetPhase, BudgetSources, RunKind, RunLimits,
};
use serde::{Deserialize, Serialize};

use crate::amounts::{add, from_amt, to_amt};

/// The label prefix of a reservation for a tool call that runs a program.
pub const PROGRAM_LABEL: &str = "program:";

/// An open reservation, as the file holds it: the agent it is for.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct HoldRecord {
    pub id: u64,
    pub agent: String,
    pub amount: BudgetAmounts,
}

/// An account, as the file holds it (the core's `Acct`). Its amounts'
/// `time_ms` are 0: time is the deadline `until`.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct Account {
    pub free: BudgetAmounts,
    pub spent: BudgetAmounts,
    pub lent: BudgetAmounts,
    pub over: BudgetAmounts,
    pub holds: Vec<HoldRecord>,
    /// The deadline (Unix ms); `BUDGET_AMOUNT_MAX` without a time limit, 0
    /// once the account was handed back.
    pub until: u64,
}

impl Account {
    pub(crate) fn to_acct(&self) -> Acct {
        Acct {
            free: to_amt(self.free),
            spent: to_amt(self.spent),
            lent: to_amt(self.lent),
            over: to_amt(self.over),
            holds: self
                .holds
                .iter()
                .map(|hold| Hold {
                    id: hold.id,
                    amt: to_amt(hold.amount),
                })
                .collect(),
            until: self.until,
        }
    }

    /// The account the core answered, each hold kept with the agent
    /// `agent_of` its id.
    pub(crate) fn from_acct(acct: &Acct, agent_of: impl Fn(u64) -> String) -> Account {
        Account {
            free: from_amt(acct.free),
            spent: from_amt(acct.spent),
            lent: from_amt(acct.lent),
            over: from_amt(acct.over),
            holds: acct
                .holds
                .iter()
                .map(|hold| HoldRecord {
                    id: hold.id,
                    agent: agent_of(hold.id),
                    amount: from_amt(hold.amt),
                })
                .collect(),
            until: acct.until,
        }
    }

    /// The agent the hold `id` is for (empty when it is not held).
    pub(crate) fn holder(&self, id: u64) -> String {
        self.holds
            .iter()
            .find(|hold| hold.id == id)
            .map(|hold| hold.agent.clone())
            .unwrap_or_default()
    }

    /// What the open reservations hold.
    pub(crate) fn held(&self) -> BudgetAmounts {
        self.holds
            .iter()
            .fold(BudgetAmounts::default(), |sum, hold| add(sum, hold.amount))
    }
}

/// An agent of an account: the owner, or a child without a budget of its
/// own that draws from it.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct Member {
    /// The agent above it in this account; `None` for the owner.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub parent: Option<String>,
    /// Its last final-answer reserve (`time_ms`: a duration): every agent
    /// below it leaves it free.
    pub keep: BudgetAmounts,
    pub phase: BudgetPhase,
    /// The dimension that ran short when its phase left `Working`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub short: Option<BudgetDimension>,
}

/// The account a child's budget was carved from.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ParentRef {
    /// The owner of the parent's account.
    pub session_id: String,
    /// The parent account's number of the carve.
    pub carve: u64,
}

/// What an account lent a live child.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ChildCarve {
    /// The account's number of the latest carve for the child.
    pub carve: u64,
    /// The agent that carved it.
    pub agent: String,
    /// The child's budget, every carve for it added up (`time_ms`: its
    /// duration).
    pub limits: BudgetLimits,
    /// The child's deadline.
    pub until: u64,
}

/// What a reservation is for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum UseRecord {
    Work,
    Final,
    /// A side request of the agent, not its own turn (`"side"`).
    Side,
}

/// Why nothing was taken.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case", tag = "why", content = "dimension")]
pub enum RefusalRecord {
    /// No offer fits; the smallest lacks this dimension first.
    Short(BudgetDimension),
    /// The id is already held.
    Held,
    /// The agent's phase does not admit the request.
    Stopped,
}

/// A run of an account: what its limits last for and who decided them.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct RunRecord {
    pub kind: RunKind,
    /// Who decided each dimension's limit.
    pub sources: BudgetSources,
    /// What the principal set for every run of the session (flags, a
    /// create config, the SDK); each run fills from it.
    #[serde(skip_serializing_if = "RunLimits::is_unset")]
    pub standing: RunLimits,
}

/// An operation on an account: the facts the core decided on.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(
    rename_all = "snake_case",
    tag = "kind",
    rename_all_fields = "camelCase"
)]
pub enum Op {
    /// The budget is set: a root's limits, or a child's allotment. `agent`
    /// owns the account.
    Open {
        agent: String,
        limits: BudgetLimits,
        /// The deadline (Unix ms); `None`: no time limit.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        deadline_ms: Option<u64>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        parent: Option<ParentRef>,
        /// The run the budget is for; `None` in a ledger written before
        /// runs were recorded, and for a child's allotment.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        run: Option<RunRecord>,
    },
    /// A new run of a root account: its own limits from now (`time_ms`: a
    /// deadline that long from `now_ms`), what is free being the limits
    /// less what is still held and lent; spend starts over.
    Renew {
        limits: BudgetLimits,
        run: RunRecord,
        now_ms: u64,
    },
    /// A child without a budget of its own draws from this account, below
    /// `parent`.
    Join { agent: String, parent: String },
    /// Before a spend: the worst case, offered in order (their time
    /// already clipped to what is left for the agent).
    Reserve {
        id: u64,
        agent: String,
        #[serde(rename = "use")]
        use_: UseRecord,
        /// What the reservation is for (`model:<provider>/<id>`,
        /// `tool:<name>`; [`PROGRAM_LABEL`]`<name>`: a tool call that runs
        /// a program, counted in the run's `program_runs`).
        label: String,
        now_ms: u64,
        keep: BudgetAmounts,
        /// The agent's largest recent step as actually spent (`time_ms`:
        /// the duration of its longest recent step): whether the grant says the
        /// budget runs low is judged against it. Zero before the agent's first step
        /// and in a record written before the field.
        #[serde(default)]
        step: BudgetAmounts,
        /// How many agents share what is free (spec/README.md B13): the
        /// account's Working agents that held nothing when it was asked,
        /// the asking one among them. A record written before the field
        /// reads 0, which the core takes as 1: a lone agent.
        #[serde(default)]
        share: u64,
        offers: Vec<BudgetAmounts>,
    },
    /// After a spend: what it actually took.
    Settle { id: u64, actual: BudgetAmounts },
    /// After a crash: every open hold of the agent is settled at its held
    /// amount.
    Recover { agent: String },
    /// A child that shared the account ended: its open holds are settled
    /// at their held amount and it is no member any more.
    Release { agent: String },
    /// A child's own budget leaves this account; `limits` is the child's
    /// (`time_ms`: its duration).
    Carve {
        agent: String,
        child: String,
        carve: u64,
        limits: BudgetLimits,
        now_ms: u64,
    },
    /// This account (a child's) was handed back to its parent.
    Return { carve: u64, account: Account },
    /// A child's account came back.
    Reclaim {
        child: String,
        carve: u64,
        account: Account,
    },
    /// More budget and time: from the user (a root), or from the parent.
    Fund {
        amount: BudgetAmounts,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        parent: Option<ParentRef>,
        now_ms: u64,
    },
    /// A limit for every dimension that had none (time: a deadline
    /// `time_ms` from now).
    Limit { limits: BudgetLimits, now_ms: u64 },
}

/// What the core answered to an operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(
    rename_all = "snake_case",
    tag = "kind",
    rename_all_fields = "camelCase"
)]
pub enum Outcome {
    /// The operation has no refusal: the state is the answer.
    Done,
    Granted {
        index: usize,
        /// `time_ms`: the granted duration.
        amount: BudgetAmounts,
        /// The budget runs low by the agent's steps (`Op::Reserve::step`);
        /// false in a record written before the field.
        #[serde(default)]
        low: bool,
    },
    Refused {
        refusal: RefusalRecord,
    },
}

/// The state of an account after an operation.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct State {
    pub account: Account,
    /// The budget per limited dimension: what was given, added budget
    /// included (`time_ms`: the duration from when it was set).
    pub limits: BudgetLimits,
    /// The id of the next reservation.
    pub next_id: u64,
    /// The number of the next carve.
    pub next_carve: u64,
    /// The agents drawing from the account, the owner among them.
    pub members: BTreeMap<String, Member>,
    /// What each live child given its own budget was lent, by its session
    /// id.
    #[serde(skip_serializing_if = "BTreeMap::is_empty")]
    pub children: BTreeMap<String, ChildCarve>,
    /// The account this budget is carved from, while it is.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub parent: Option<ParentRef>,
    /// The account as it was handed back, until the parent lends again.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub returned: Option<Account>,
    /// The account's current run; `None` in a ledger written before runs
    /// were recorded (it counts no spend without a limit).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub run: Option<RunRecord>,
    /// What the run spent in each dimension without a limit (time: 0).
    #[serde(skip_serializing_if = "BudgetAmounts::is_zero")]
    pub tally: BudgetAmounts,
    /// The tool calls of the run that run a program, as granted.
    #[serde(skip_serializing_if = "is_zero")]
    pub program_runs: u64,
}

/// One line of a ledger file.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Record {
    /// The record's place in the file, from 0.
    pub seq: u64,
    /// When it was written (Unix milliseconds).
    pub at_ms: u64,
    pub op: Op,
    pub outcome: Outcome,
    pub state: State,
}

#[allow(clippy::trivially_copy_pass_by_ref)] // serde's `skip_serializing_if` passes a reference.
fn is_zero(count: &u64) -> bool {
    *count == 0
}
