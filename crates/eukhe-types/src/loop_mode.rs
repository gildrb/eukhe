//! `/loop` wire state. The `loop_update` session event and the attach
//! snapshot's `state.loop` field carry a [`LoopStatus`] to every attached
//! surface (TUI, ACP, RPC, dashboard, an SDK client), so the shared
//! vocabulary lives in eukhe-types. The decisions are the compiled core's
//! (`bend/loop.bend`, called through `eukhe_bend::rules::loop_mode`); the
//! runtime (the durable state, the condition command, the hooks) lives in
//! eukhe-core.
//!
//! A client starts a loop by sending the prompt `/loop [count|duration]
//! [--while|--until '<command>'] [prompt]`, stops it with `/loop --stop`
//! ([`LOOP_STOP_COMMAND`]) and watches it through `loop_update`.

use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// The prompt text that stops a session's loop and never starts one.
pub const LOOP_STOP_COMMAND: &str = "/loop --stop";

/// The prompt text that shows a session's loop.
pub const LOOP_STATUS_COMMAND: &str = "/loop --status";

/// The condition of a loop: a shell command whose exit status decides.
/// `until`: the loop stops once the command succeeds; else (`--while`) it
/// stops once the command fails.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LoopCondition {
    pub command: String,
    pub until: bool,
}

/// What one run of the condition command showed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum LoopEvidence {
    /// The command exited with this status.
    Exited { code: u64 },
    /// The command ended with no exit status (a signal).
    NoStatus,
    /// The command outran `loop.conditionTimeoutMs`.
    TimedOut,
    /// The command could not start.
    SpawnFailed,
    /// The run was cancelled before it answered.
    Cancelled,
}

/// What a piece of evidence says of the loop's stop condition. On the wire
/// it is the number shared with the verified-done pillar: 0 confirmed,
/// 1 refuted, 2 broken, 3 unjudged.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopVerdict {
    /// The stop condition holds.
    Confirmed,
    /// The stop condition does not hold yet.
    Refuted,
    /// The check itself is broken: never read as either.
    Broken,
    /// Nothing was learned (the check was cancelled).
    Unjudged,
}

impl LoopVerdict {
    /// The wire number.
    #[must_use]
    pub fn tag(self) -> u8 {
        match self {
            LoopVerdict::Confirmed => 0,
            LoopVerdict::Refuted => 1,
            LoopVerdict::Broken => 2,
            LoopVerdict::Unjudged => 3,
        }
    }

    /// The verdict of a wire number.
    #[must_use]
    pub fn from_tag(tag: u8) -> Option<Self> {
        match tag {
            0 => Some(LoopVerdict::Confirmed),
            1 => Some(LoopVerdict::Refuted),
            2 => Some(LoopVerdict::Broken),
            3 => Some(LoopVerdict::Unjudged),
            _ => None,
        }
    }
}

impl Serialize for LoopVerdict {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_u8(self.tag())
    }
}

impl<'de> Deserialize<'de> for LoopVerdict {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let tag = u8::deserialize(deserializer)?;
        LoopVerdict::from_tag(tag)
            .ok_or_else(|| serde::de::Error::custom(format!("a loop verdict is 0 to 3, not {tag}")))
    }
}

/// Why a loop ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum LoopEnd {
    /// Its stop condition was confirmed by the condition command.
    Satisfied,
    /// The condition command broke (exit 126 or 127: it cannot run or is
    /// not found; no status, a timeout, a failed start).
    CheckBroke,
    /// The iteration count is used up.
    OutOfTurns,
    /// The time is used up.
    OutOfTime,
    /// Three turns failed in a row.
    TurnsFailed,
    /// The budget funds no further turn.
    OutOfBudget,
    /// The user stopped it.
    Stopped,
}

impl LoopEnd {
    /// The wire slug.
    #[must_use]
    pub fn slug(self) -> &'static str {
        match self {
            LoopEnd::Satisfied => "satisfied",
            LoopEnd::CheckBroke => "check_broke",
            LoopEnd::OutOfTurns => "out_of_turns",
            LoopEnd::OutOfTime => "out_of_time",
            LoopEnd::TurnsFailed => "turns_failed",
            LoopEnd::OutOfBudget => "out_of_budget",
            LoopEnd::Stopped => "stopped",
        }
    }
}

/// Where a loop is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "state", rename_all = "snake_case")]
pub enum LoopPhase {
    /// No loop.
    Off,
    /// On, waiting for the prompt to repeat.
    Armed,
    /// An iteration's turn is in flight.
    Turn,
    /// The turn settled; the condition command runs.
    Judging,
    /// Suspended by the user's interrupt, waiting for a new prompt.
    Paused,
    /// Over.
    Ended { end: LoopEnd },
}

impl LoopPhase {
    /// Whether a loop is on (armed, in a turn, judging or paused).
    #[must_use]
    pub fn is_on(self) -> bool {
        match self {
            LoopPhase::Armed | LoopPhase::Turn | LoopPhase::Judging | LoopPhase::Paused => true,
            LoopPhase::Off | LoopPhase::Ended { .. } => false,
        }
    }
}

/// The bound given at `/loop`: a count of automatic iterations or a span.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(
    tag = "kind",
    rename_all = "camelCase",
    rename_all_fields = "camelCase"
)]
pub enum LoopLimit {
    Iterations { iterations: u64 },
    Duration { duration_ms: u64 },
}

/// The last evidence a loop read, and the iteration it was read after.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LoopCheck {
    pub iteration: u64,
    pub evidence: LoopEvidence,
}

/// The state of one session's loop: the value the compiled core steps
/// (`bend/loop.bend` `St`), kept in the session's durable storage.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LoopState {
    pub phase: LoopPhase,
    /// The iterations started (the first turn is 1).
    pub iteration: u64,
    /// The automatic iterations left; absent with no count.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub remaining: Option<u64>,
    /// The deadline, in milliseconds since the epoch; absent with no span.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub deadline_ms: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub condition: Option<LoopCondition>,
    /// The prompt repeated; empty while armed or paused.
    pub prompt: String,
    /// The turns that failed in a row.
    pub failures: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub last_check: Option<LoopCheck>,
}

impl Default for LoopState {
    /// No loop.
    fn default() -> Self {
        Self {
            phase: LoopPhase::Off,
            iteration: 0,
            remaining: None,
            deadline_ms: None,
            condition: None,
            prompt: String::new(),
            failures: 0,
            last_check: None,
        }
    }
}

/// What every surface shows of a loop: its state, the bound it was started
/// with, the verdict of its last evidence (why it is still running, or why
/// it ended), and the last line the loop reported.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LoopStatus {
    #[serde(flatten)]
    pub state: LoopState,
    /// The bound given at `/loop`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub limit: Option<LoopLimit>,
    /// When the loop was started, in milliseconds since the epoch.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub started_at_ms: Option<u64>,
    /// The verdict of `lastCheck` on the loop's stop condition (0
    /// confirmed, 1 refuted, 2 broken, 3 unjudged). The check is fresh
    /// (read after the last turn) exactly when `lastCheck.iteration ==
    /// iteration`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub verdict: Option<LoopVerdict>,
    /// The last line the loop reported (its start, its end).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub message: Option<String>,
}

impl Default for LoopStatus {
    /// No loop.
    fn default() -> Self {
        Self {
            state: LoopState::default(),
            limit: None,
            started_at_ms: None,
            verdict: None,
            message: None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The wire shape clients read: the state flattened, the verdict a
    /// number, absent fields omitted.
    #[test]
    fn a_status_round_trips_in_its_wire_shape() {
        let status = LoopStatus {
            state: LoopState {
                phase: LoopPhase::Ended {
                    end: LoopEnd::Satisfied,
                },
                iteration: 3,
                remaining: Some(7),
                deadline_ms: None,
                condition: Some(LoopCondition {
                    command: "test -f done".to_owned(),
                    until: true,
                }),
                prompt: "fix it".to_owned(),
                failures: 0,
                last_check: Some(LoopCheck {
                    iteration: 3,
                    evidence: LoopEvidence::Exited { code: 0 },
                }),
            },
            limit: Some(LoopLimit::Iterations { iterations: 10 }),
            started_at_ms: Some(5),
            verdict: Some(LoopVerdict::Confirmed),
            message: None,
        };
        let text = serde_json::to_string(&status).expect("encode");
        assert_eq!(
            text,
            r#"{"phase":{"state":"ended","end":"satisfied"},"iteration":3,"remaining":7,"condition":{"command":"test -f done","until":true},"prompt":"fix it","failures":0,"lastCheck":{"iteration":3,"evidence":{"kind":"exited","code":0}},"limit":{"kind":"iterations","iterations":10},"startedAtMs":5,"verdict":0}"#
        );
        assert_eq!(
            serde_json::from_str::<LoopStatus>(&text).expect("decode"),
            status
        );
    }
}
