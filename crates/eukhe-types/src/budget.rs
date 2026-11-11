//! Budget wire state. The `budget_update` session event, the
//! `get_budget` / `set_budget` / `add_budget` daemon commands and the SDK
//! carry these objects to every surface (TUI, CLI, SDK clients), so the
//! shared vocabulary lives in eukhe-types; the ledger (reserve before
//! spending, settle after, carve for children) lives in eukhe-budget and
//! its decisions in the compiled core (`bend/budget.bend`). Field shape is
//! camelCase, optional keys omitted.

use serde::{Deserialize, Serialize};

/// The largest amount one dimension of a budget holds: money in
/// micro-dollars (10 million dollars), tokens, tool calls, model requests,
/// a duration in milliseconds; also the deadline of a budget without a time
/// limit. The compiled core counts within its wire's 14 digits; a budget
/// and every sum of its parts (a deadline and the durations after it
/// included) stay below it.
pub const BUDGET_AMOUNT_MAX: u64 = 9_999_999_999_999;

/// A dimension of a budget.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BudgetDimension {
    /// Money, in micro-dollars.
    Cost,
    /// Tokens a provider bills: input, output, cache reads and writes.
    Tokens,
    /// Wall-clock time in milliseconds: a deadline for the whole task tree,
    /// set as a duration from when the budget was set.
    Time,
    /// Tool calls.
    ToolCalls,
    /// Model requests: every request sent to a provider.
    Requests,
}

impl BudgetDimension {
    /// Every dimension, in the ledger's order.
    pub const ALL: [BudgetDimension; 5] = [
        BudgetDimension::Cost,
        BudgetDimension::Tokens,
        BudgetDimension::Time,
        BudgetDimension::ToolCalls,
        BudgetDimension::Requests,
    ];

    /// The word a notice or a status line names the dimension with.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            BudgetDimension::Cost => "cost",
            BudgetDimension::Tokens => "tokens",
            BudgetDimension::Time => "time",
            BudgetDimension::ToolCalls => "tool calls",
            BudgetDimension::Requests => "requests",
        }
    }
}

/// An amount in each dimension. `time_ms` is a duration wherever amounts
/// are asked for or added (limits, added budget, a reservation's offers);
/// in a [`BudgetReport`] only `free.time_ms` carries time (what is left
/// until the deadline).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct BudgetAmounts {
    /// Micro-dollars.
    pub cost_micros: u64,
    pub tokens: u64,
    /// Milliseconds.
    pub time_ms: u64,
    pub tool_calls: u64,
    /// Model requests.
    pub requests: u64,
}

impl BudgetAmounts {
    /// The amount in `dimension`.
    #[must_use]
    pub fn get(&self, dimension: BudgetDimension) -> u64 {
        match dimension {
            BudgetDimension::Cost => self.cost_micros,
            BudgetDimension::Tokens => self.tokens,
            BudgetDimension::Time => self.time_ms,
            BudgetDimension::ToolCalls => self.tool_calls,
            BudgetDimension::Requests => self.requests,
        }
    }

    /// The amounts with `dimension` set to `value`.
    #[must_use]
    pub fn with(mut self, dimension: BudgetDimension, value: u64) -> Self {
        match dimension {
            BudgetDimension::Cost => self.cost_micros = value,
            BudgetDimension::Tokens => self.tokens = value,
            BudgetDimension::Time => self.time_ms = value,
            BudgetDimension::ToolCalls => self.tool_calls = value,
            BudgetDimension::Requests => self.requests = value,
        }
        self
    }

    /// Whether every dimension is zero.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        *self == BudgetAmounts::default()
    }
}

/// The limits of a budget: a dimension with no limit is unlimited and is
/// not counted by the ledger.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct BudgetLimits {
    /// Micro-dollars.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cost_micros: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tokens: Option<u64>,
    /// The wall-clock duration of the tree's budget, in milliseconds from
    /// when it was set: the deadline is that much later.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub time_ms: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tool_calls: Option<u64>,
    /// Model requests.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub requests: Option<u64>,
}

impl BudgetLimits {
    /// The limit of `dimension`, if it has one.
    #[must_use]
    pub fn get(&self, dimension: BudgetDimension) -> Option<u64> {
        match dimension {
            BudgetDimension::Cost => self.cost_micros,
            BudgetDimension::Tokens => self.tokens,
            BudgetDimension::Time => self.time_ms,
            BudgetDimension::ToolCalls => self.tool_calls,
            BudgetDimension::Requests => self.requests,
        }
    }

    /// The limits with `dimension` set to `value`.
    #[must_use]
    pub fn with(mut self, dimension: BudgetDimension, value: Option<u64>) -> Self {
        match dimension {
            BudgetDimension::Cost => self.cost_micros = value,
            BudgetDimension::Tokens => self.tokens = value,
            BudgetDimension::Time => self.time_ms = value,
            BudgetDimension::ToolCalls => self.tool_calls = value,
            BudgetDimension::Requests => self.requests = value,
        }
        self
    }

    /// Whether no dimension has a limit.
    #[must_use]
    pub fn is_unlimited(&self) -> bool {
        *self == BudgetLimits::default()
    }
}

/// What an agent of a budget's tree is still admitted.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BudgetPhase {
    /// Work and a final answer.
    #[default]
    Working,
    /// Only a final answer: the agent was told to wrap up.
    WrapUp,
    /// Nothing, until budget is added.
    Exhausted,
}

impl BudgetPhase {
    /// The wire slug (`"working"`, `"wrap_up"`, `"exhausted"`).
    #[must_use]
    pub fn slug(self) -> &'static str {
        match self {
            BudgetPhase::Working => "working",
            BudgetPhase::WrapUp => "wrap_up",
            BudgetPhase::Exhausted => "exhausted",
        }
    }
}

/// The state of a budget as one agent of its tree sees it, as every
/// surface shows it. In each limited dimension but time
/// `free + held + spent + lent == limits + over`; time is a deadline:
/// `free.time_ms` is what is left until it (0 once it passed) and every
/// other amount's `time_ms` is 0.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct BudgetReport {
    /// The session whose account the budget is: the tree's root, or a
    /// child given a budget of its own.
    pub session_id: String,
    /// The agent this report is for: its phase and shortage are `phase`
    /// and `short`. A child without a budget of its own draws from its
    /// parent's account.
    pub agent_session_id: String,
    /// The budget: what was given, added budget included. A dimension
    /// without a limit is unlimited and shows zero everywhere else.
    pub limits: BudgetLimits,
    /// What can still be reserved; `time_ms`: what is left until the
    /// deadline.
    pub free: BudgetAmounts,
    /// What open reservations hold: requests and tool calls in flight.
    pub held: BudgetAmounts,
    /// What was spent: the settled spends of every agent of the account
    /// and those of its closed children.
    pub spent: BudgetAmounts,
    /// What live children given their own budget were allotted.
    pub lent: BudgetAmounts,
    /// What was spent past the budget: a provider that answered more than
    /// its reservation. Zero unless a provider broke its cap.
    pub over: BudgetAmounts,
    /// The agent's phase.
    pub phase: BudgetPhase,
    /// The dimension that ran short when the agent's phase left
    /// `Working`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub short: Option<BudgetDimension>,
    /// The deadline (Unix milliseconds); `None`: no time limit.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub deadline_ms: Option<u64>,
    /// The session this budget was carved from, for a child given a
    /// budget of its own.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub parent_session_id: Option<String>,
}
