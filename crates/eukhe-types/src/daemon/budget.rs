//! The budget on the daemon wire (Rust-native): the `get_budget`,
//! `set_budget` and `add_budget` commands answer a [`BudgetReply`],
//! `audit_budget` a [`BudgetAuditReply`]; the `budget_update` session event
//! and the attach snapshot's `state.budget` carry the same
//! [`BudgetReport`]. The budget's own vocabulary is `crate::budget`.

use serde::{Deserialize, Serialize};

use crate::budget::{BudgetAmounts, BudgetReport};

/// The `get_budget`, `set_budget` and `add_budget` response data.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BudgetReply {
    /// The session's budget; `null` for a session without one.
    pub budget: Option<BudgetReport>,
}

/// The `audit_budget` response data.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct BudgetAuditReply {
    pub audit: BudgetAudit,
}

/// What an audit of a session's budget ledger found.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct BudgetAudit {
    /// How many records the ledger holds.
    pub records: u64,
    /// The sum of every settled spend: settlements, recoveries, and the
    /// spends of the children that ended.
    pub settled: BudgetAmounts,
    /// What the ledger reports as spent.
    pub spent: BudgetAmounts,
    /// Every record replays from the one before it and the settled spends
    /// add up to the reported total.
    pub exact: bool,
    /// The first record the compiled core does not reproduce from the
    /// record before it; `null` when every record replays.
    pub first_mismatch: Option<u64>,
}

#[cfg(test)]
mod tests {
    use serde_json::{json, Value};

    use super::*;
    use crate::budget::BudgetLimits;
    use crate::daemon::{rt, DaemonCommand, SessionEvent};
    use crate::JsonMap;

    fn amounts(cost_micros: u64, tokens: u64) -> BudgetAmounts {
        BudgetAmounts {
            cost_micros,
            tokens,
            ..BudgetAmounts::default()
        }
    }

    /// A budget of 5 dollars, 200k tokens and 10 minutes with 1 dollar and
    /// 1.5k tokens spent and 4 minutes left, as the ledger reports it to
    /// the root agent and as the wire carries it.
    fn report() -> (BudgetReport, Value) {
        let report = BudgetReport {
            session_id: "s1".to_string(),
            agent_session_id: "s1".to_string(),
            limits: BudgetLimits {
                cost_micros: Some(5_000_000),
                tokens: Some(200_000),
                time_ms: Some(600_000),
                ..BudgetLimits::default()
            },
            free: BudgetAmounts {
                time_ms: 240_000,
                ..amounts(4_000_000, 198_500)
            },
            spent: amounts(1_000_000, 1_500),
            deadline_ms: Some(1_800_000_000_000),
            ..BudgetReport::default()
        };
        let zero =
            json!({ "costMicros": 0, "tokens": 0, "timeMs": 0, "toolCalls": 0, "requests": 0 });
        let wire = json!({
            "sessionId": "s1",
            "agentSessionId": "s1",
            "limits": { "costMicros": 5_000_000, "tokens": 200_000, "timeMs": 600_000 },
            "free": { "costMicros": 4_000_000, "tokens": 198_500, "timeMs": 240_000, "toolCalls": 0, "requests": 0 },
            "held": zero,
            "spent": { "costMicros": 1_000_000, "tokens": 1_500, "timeMs": 0, "toolCalls": 0, "requests": 0 },
            "lent": zero,
            "over": zero,
            "phase": "working",
            "deadlineMs": 1_800_000_000_000_u64,
        });
        (report, wire)
    }

    /// Each budget command reads from its wire form as the typed command
    /// and writes the same wire form back.
    #[test]
    fn the_budget_commands_round_trip_on_the_wire() {
        let session = || "s1".to_string();
        let cases = [
            (
                json!({ "type": "get_budget", "activeSessionId": "s1" }),
                DaemonCommand::GetBudget {
                    id: None,
                    active_session_id: session(),
                    rest: JsonMap::default(),
                },
            ),
            (
                json!({
                    "type": "set_budget",
                    "activeSessionId": "s1",
                    "limits": { "costMicros": 5_000_000, "timeMs": 600_000 },
                }),
                DaemonCommand::SetBudget {
                    id: None,
                    active_session_id: session(),
                    limits: BudgetLimits {
                        cost_micros: Some(5_000_000),
                        time_ms: Some(600_000),
                        ..BudgetLimits::default()
                    },
                    rest: JsonMap::default(),
                },
            ),
            (
                json!({
                    "type": "add_budget",
                    "id": "c7",
                    "activeSessionId": "s1",
                    "amounts": { "costMicros": 1_000_000, "tokens": 0, "timeMs": 0, "toolCalls": 25, "requests": 3 },
                }),
                DaemonCommand::AddBudget {
                    id: Some("c7".to_string()),
                    active_session_id: session(),
                    amounts: BudgetAmounts {
                        cost_micros: 1_000_000,
                        tool_calls: 25,
                        requests: 3,
                        ..BudgetAmounts::default()
                    },
                    rest: JsonMap::default(),
                },
            ),
            (
                json!({ "type": "audit_budget", "activeSessionId": "s1" }),
                DaemonCommand::AuditBudget {
                    id: None,
                    active_session_id: session(),
                    rest: JsonMap::default(),
                },
            ),
        ];
        for (wire, command) in cases {
            assert_eq!(
                serde_json::from_value::<DaemonCommand>(wire.clone()).expect("parses"),
                command
            );
            assert_eq!(serde_json::to_value(&command).expect("serializes"), wire);
        }
        // An amount the client leaves out is zero.
        assert_eq!(
            serde_json::from_value::<DaemonCommand>(json!({
                "type": "add_budget",
                "activeSessionId": "s1",
                "amounts": { "tokens": 50_000 },
            }))
            .expect("parses"),
            DaemonCommand::AddBudget {
                id: None,
                active_session_id: session(),
                amounts: amounts(0, 50_000),
                rest: JsonMap::default(),
            }
        );
    }

    /// `budget_update` carries the whole report, or null for a session
    /// without a budget.
    #[test]
    fn the_budget_update_event_round_trips_on_the_wire() {
        let (report, report_wire) = report();
        let cases = [
            (
                json!({ "type": "budget_update", "budget": report_wire }),
                SessionEvent::BudgetUpdate {
                    budget: Some(report),
                },
            ),
            (
                json!({ "type": "budget_update", "budget": null }),
                SessionEvent::BudgetUpdate { budget: None },
            ),
        ];
        for (wire, event) in cases {
            assert_eq!(
                serde_json::from_value::<SessionEvent>(wire.clone()).expect("parses"),
                event
            );
            assert_eq!(serde_json::to_value(&event).expect("serializes"), wire);
        }
    }

    /// The replies' wire forms: the report under `budget` (null without a
    /// budget), the audit under `audit` with `firstMismatch` always there.
    #[test]
    fn the_budget_replies_round_trip_on_the_wire() {
        let (report, report_wire) = report();
        let reply = BudgetReply {
            budget: Some(report),
        };
        assert_eq!(
            serde_json::to_value(&reply).expect("serializes"),
            json!({ "budget": report_wire })
        );
        rt::<BudgetReply>(&json!({ "budget": report_wire }).to_string());
        rt::<BudgetReply>(r#"{"budget":null}"#);
        let audit = BudgetAuditReply {
            audit: BudgetAudit {
                records: 7,
                settled: amounts(1_000_000, 1_500),
                spent: amounts(1_000_000, 1_500),
                exact: true,
                first_mismatch: None,
            },
        };
        let spent = json!({ "costMicros": 1_000_000, "tokens": 1_500, "timeMs": 0, "toolCalls": 0, "requests": 0 });
        let wire = json!({
            "audit": {
                "records": 7,
                "settled": spent,
                "spent": spent,
                "exact": true,
                "firstMismatch": null,
            },
        });
        assert_eq!(serde_json::to_value(audit).expect("serializes"), wire);
        assert_eq!(
            serde_json::from_value::<BudgetAuditReply>(wire).expect("parses"),
            audit
        );
    }
}
