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

/// The kind of a run: what one fill of a session's limits lasts for.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RunKind {
    /// One message sent while the session is idle; queued and steering
    /// messages and goal or autonomous continuations join it.
    #[default]
    Interactive,
    /// One `-p` prompt.
    Headless,
    /// One prompt of an embedding host.
    Sdk,
    /// One fire of a scheduled job.
    Scheduled,
    /// One whole `/loop`.
    Loop,
    /// One whole `/autoresearch`.
    Autoresearch,
}

impl RunKind {
    /// Every kind, in the settings' order.
    pub const ALL: [RunKind; 6] = [
        RunKind::Interactive,
        RunKind::Headless,
        RunKind::Sdk,
        RunKind::Scheduled,
        RunKind::Loop,
        RunKind::Autoresearch,
    ];

    /// The wire slug, also the settings key (`budget.profile.<slug>`).
    #[must_use]
    pub fn slug(self) -> &'static str {
        match self {
            RunKind::Interactive => "interactive",
            RunKind::Headless => "headless",
            RunKind::Sdk => "sdk",
            RunKind::Scheduled => "scheduled",
            RunKind::Loop => "loop",
            RunKind::Autoresearch => "autoresearch",
        }
    }
}

/// How the session's model is paid for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AuthClass {
    /// A subscription login: quota windows, no price per request.
    Plan,
    /// An API key: a price per request.
    ApiKey,
    /// A local model: no price.
    Local,
}

/// One dimension's limit as asked: a number, or unlimited as the
/// principal declared it. Serde: a number or the string `"unlimited"`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LimitValue {
    At(u64),
    Unlimited,
}

impl LimitValue {
    /// The settings and wire word of [`LimitValue::Unlimited`].
    pub const UNLIMITED: &'static str = "unlimited";

    /// The number, `None` when unlimited.
    #[must_use]
    pub fn at(self) -> Option<u64> {
        match self {
            LimitValue::At(value) => Some(value),
            LimitValue::Unlimited => None,
        }
    }
}

impl Serialize for LimitValue {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            LimitValue::At(value) => serializer.serialize_u64(*value),
            LimitValue::Unlimited => serializer.serialize_str(Self::UNLIMITED),
        }
    }
}

impl<'de> Deserialize<'de> for LimitValue {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        #[serde(untagged)]
        enum Wire {
            At(u64),
            Word(String),
        }
        match Wire::deserialize(deserializer)? {
            Wire::At(value) => Ok(LimitValue::At(value)),
            Wire::Word(word) if word == Self::UNLIMITED => Ok(LimitValue::Unlimited),
            Wire::Word(word) => Err(serde::de::Error::custom(format!(
                "a limit is a number or \"{}\", not \"{word}\"",
                Self::UNLIMITED
            ))),
        }
    }
}

/// Limits as one layer asks them (the principal, a `/b` preset, the
/// principal's profile, the limits profile): `None` = this layer leaves
/// the dimension unset.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct RunLimits {
    /// Micro-dollars.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cost_micros: Option<LimitValue>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tokens: Option<LimitValue>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub time_ms: Option<LimitValue>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tool_calls: Option<LimitValue>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub requests: Option<LimitValue>,
}

impl RunLimits {
    /// What this layer asks of `dimension`.
    #[must_use]
    pub fn get(&self, dimension: BudgetDimension) -> Option<LimitValue> {
        match dimension {
            BudgetDimension::Cost => self.cost_micros,
            BudgetDimension::Tokens => self.tokens,
            BudgetDimension::Time => self.time_ms,
            BudgetDimension::ToolCalls => self.tool_calls,
            BudgetDimension::Requests => self.requests,
        }
    }

    /// The layer with `dimension` asked as `value`.
    #[must_use]
    pub fn with(mut self, dimension: BudgetDimension, value: Option<LimitValue>) -> Self {
        match dimension {
            BudgetDimension::Cost => self.cost_micros = value,
            BudgetDimension::Tokens => self.tokens = value,
            BudgetDimension::Time => self.time_ms = value,
            BudgetDimension::ToolCalls => self.tool_calls = value,
            BudgetDimension::Requests => self.requests = value,
        }
        self
    }

    /// Whether the layer leaves every dimension unset.
    #[must_use]
    pub fn is_unset(&self) -> bool {
        *self == RunLimits::default()
    }

    /// `self` where it asks, `under` elsewhere.
    #[must_use]
    pub fn over(self, under: RunLimits) -> RunLimits {
        BudgetDimension::ALL
            .into_iter()
            .fold(self, |layer, dimension| match layer.get(dimension) {
                Some(_) => layer,
                None => layer.with(dimension, under.get(dimension)),
            })
    }

    /// The numbers the ledger counts: an unlimited dimension has none.
    #[must_use]
    pub fn counted(&self) -> BudgetLimits {
        BudgetDimension::ALL
            .into_iter()
            .fold(BudgetLimits::default(), |limits, dimension| {
                limits.with(dimension, self.get(dimension).and_then(LimitValue::at))
            })
    }
}

impl From<BudgetLimits> for RunLimits {
    /// Each number as asked; a dimension without one is unset.
    fn from(limits: BudgetLimits) -> Self {
        BudgetDimension::ALL
            .into_iter()
            .fold(RunLimits::default(), |layer, dimension| {
                layer.with(dimension, limits.get(dimension).map(LimitValue::At))
            })
    }
}

/// Who decided one dimension's limit of a run.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case", tag = "source", content = "name")]
pub enum LimitSource {
    /// Nobody: limits are off, the run goes until finished.
    #[default]
    UntilFinished,
    /// The principal: a flag, `/budget set`, the SDK or a create config.
    Set,
    /// The shipped limits profile (limits on).
    LimitsProfile,
    /// The principal's own `budget.profile` (limits on).
    Profile,
    /// A `/b <name>` preset of the run's message.
    Preset(String),
}

/// The source of each dimension's limit.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct BudgetSources {
    pub cost_micros: LimitSource,
    pub tokens: LimitSource,
    pub time_ms: LimitSource,
    pub tool_calls: LimitSource,
    pub requests: LimitSource,
}

impl BudgetSources {
    /// The source of `dimension`'s limit.
    #[must_use]
    pub fn get(&self, dimension: BudgetDimension) -> &LimitSource {
        match dimension {
            BudgetDimension::Cost => &self.cost_micros,
            BudgetDimension::Tokens => &self.tokens,
            BudgetDimension::Time => &self.time_ms,
            BudgetDimension::ToolCalls => &self.tool_calls,
            BudgetDimension::Requests => &self.requests,
        }
    }

    /// The sources with `dimension`'s set to `source`.
    #[must_use]
    pub fn with(mut self, dimension: BudgetDimension, source: LimitSource) -> Self {
        match dimension {
            BudgetDimension::Cost => self.cost_micros = source,
            BudgetDimension::Tokens => self.tokens = source,
            BudgetDimension::Time => self.time_ms = source,
            BudgetDimension::ToolCalls => self.tool_calls = source,
            BudgetDimension::Requests => self.requests = source,
        }
        self
    }

    /// Whether no dimension had a limit decided: the run went until
    /// finished.
    #[must_use]
    pub fn until_finished(&self) -> bool {
        *self == BudgetSources::default()
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
    /// The budget of the run: what was given, added budget included. A
    /// dimension without a limit is unlimited (`sources` says by whom): it
    /// shows its spend in `spent` and zero everywhere else.
    pub limits: BudgetLimits,
    /// What can still be reserved; `time_ms`: what is left until the
    /// deadline.
    pub free: BudgetAmounts,
    /// What open reservations hold: requests and tool calls in flight.
    pub held: BudgetAmounts,
    /// What the run spent: the settled spends of every agent of the account
    /// and those of its closed children, in every dimension, the unlimited
    /// ones included.
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
    /// The kind of the account's current run; `None` in a ledger written
    /// before runs were recorded, whose every limit the principal set.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub kind: Option<RunKind>,
    /// Who decided each dimension's limit of the run.
    #[serde(skip_serializing_if = "BudgetSources::until_finished")]
    pub sources: BudgetSources,
    /// The programs the run started (a lower bound: its tool calls that
    /// run programs).
    #[serde(skip_serializing_if = "is_zero")]
    pub program_runs: u64,
}

#[allow(clippy::trivially_copy_pass_by_ref)] // serde's `skip_serializing_if` passes a reference.
fn is_zero(count: &u64) -> bool {
    *count == 0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_limit_is_a_number_or_unlimited_on_the_wire_and_unlimited_is_not_counted() {
        let asked = RunLimits {
            cost_micros: Some(LimitValue::Unlimited),
            requests: Some(LimitValue::At(3)),
            ..RunLimits::default()
        };
        let wire = serde_json::json!({"costMicros": "unlimited", "requests": 3});
        assert_eq!(serde_json::to_value(asked).unwrap(), wire);
        assert_eq!(serde_json::from_value::<RunLimits>(wire).unwrap(), asked);
        assert!(
            serde_json::from_value::<RunLimits>(serde_json::json!({"tokens": "lots"})).is_err()
        );
        assert_eq!(
            asked.counted(),
            BudgetLimits {
                requests: Some(3),
                ..BudgetLimits::default()
            }
        );
    }

    #[test]
    fn a_report_of_a_run_names_its_kind_sources_and_programs_on_the_wire() {
        let report = BudgetReport {
            kind: Some(RunKind::Loop),
            sources: BudgetSources {
                cost_micros: LimitSource::Preset("deep".to_owned()),
                requests: LimitSource::Set,
                ..BudgetSources::default()
            },
            program_runs: 2,
            ..BudgetReport::default()
        };
        let wire = serde_json::to_value(&report).unwrap();
        assert_eq!(
            (
                &wire["kind"],
                &wire["sources"]["costMicros"],
                &wire["sources"]["tokens"],
                &wire["programRuns"]
            ),
            (
                &serde_json::json!("loop"),
                &serde_json::json!({"source": "preset", "name": "deep"}),
                &serde_json::json!({"source": "until_finished"}),
                &serde_json::json!(2),
            )
        );
        assert_eq!(
            serde_json::from_value::<BudgetReport>(wire).unwrap(),
            report
        );
    }
}
