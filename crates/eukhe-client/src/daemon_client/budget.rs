//! A session's budget over the daemon wire: `get_budget`, `set_budget`,
//! `add_budget` and `audit_budget` as typed requests. The budget's changes
//! arrive on the event stream as `budget_update` session events
//! ([`DaemonClientEvent::SessionEvent`](super::DaemonClientEvent)), and an
//! attach snapshot carries the budget as `state.budget`.

use anyhow::{Context, Result};
use eukhe_types::budget::{BudgetAmounts, BudgetLimits, BudgetReport};
use eukhe_types::daemon::{BudgetAudit, BudgetAuditReply, BudgetReply, DaemonCommand};
use serde_json::{Map, Value};

use super::DaemonClient;

impl DaemonClient {
    /// The budget of the session `active_session_id`; `None` when the
    /// session has no budget.
    ///
    /// # Errors
    ///
    /// The request fails, the daemon refuses it
    /// ([`RequestRejected`](super::RequestRejected)), or its answer has
    /// another shape.
    pub async fn get_budget(&self, active_session_id: &str) -> Result<Option<BudgetReport>> {
        let data = self
            .request_ok(DaemonCommand::GetBudget {
                id: None,
                active_session_id: active_session_id.to_string(),
                rest: Map::default(),
            })
            .await?;
        let reply: BudgetReply =
            serde_json::from_value(data).context("read the get_budget answer")?;
        Ok(reply.budget)
    }

    /// Give the session `active_session_id` the budget `limits`; answers
    /// the new budget. A session that already has a budget refuses: add to
    /// it with [`Self::add_budget`].
    ///
    /// # Errors
    ///
    /// The request fails, the daemon refuses it
    /// ([`RequestRejected`](super::RequestRejected), with the ledger's
    /// message), or its answer has another shape.
    pub async fn set_budget(
        &self,
        active_session_id: &str,
        limits: BudgetLimits,
    ) -> Result<BudgetReport> {
        let data = self
            .request_ok(DaemonCommand::SetBudget {
                id: None,
                active_session_id: active_session_id.to_string(),
                limits,
                rest: Map::default(),
            })
            .await?;
        changed_budget("set_budget", data)
    }

    /// Add `amounts` to the budget of the session `active_session_id`, so
    /// a session that used its budget up works again; a session without a
    /// budget gets `amounts` as its budget. Answers the new budget.
    ///
    /// # Errors
    ///
    /// The request fails, the daemon refuses it
    /// ([`RequestRejected`](super::RequestRejected), with the ledger's
    /// message), or its answer has another shape.
    pub async fn add_budget(
        &self,
        active_session_id: &str,
        amounts: BudgetAmounts,
    ) -> Result<BudgetReport> {
        let data = self
            .request_ok(DaemonCommand::AddBudget {
                id: None,
                active_session_id: active_session_id.to_string(),
                amounts,
                rest: Map::default(),
            })
            .await?;
        changed_budget("add_budget", data)
    }

    /// Audit the budget ledger of the session `active_session_id`: every
    /// record replayed, and the settled spends against the reported total.
    ///
    /// # Errors
    ///
    /// The request fails, the daemon refuses it
    /// ([`RequestRejected`](super::RequestRejected): the session has no
    /// budget, or its ledger does not read), or its answer has another
    /// shape.
    pub async fn audit_budget(&self, active_session_id: &str) -> Result<BudgetAudit> {
        let data = self
            .request_ok(DaemonCommand::AuditBudget {
                id: None,
                active_session_id: active_session_id.to_string(),
                rest: Map::default(),
            })
            .await?;
        let reply: BudgetAuditReply =
            serde_json::from_value(data).context("read the audit_budget answer")?;
        Ok(reply.audit)
    }
}

/// The budget a `set_budget` or `add_budget` answer carries.
fn changed_budget(command: &str, data: Value) -> Result<BudgetReport> {
    let reply: BudgetReply =
        serde_json::from_value(data).with_context(|| format!("read the {command} answer"))?;
    reply
        .budget
        .with_context(|| format!("the daemon answered {command} without a budget"))
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use eukhe_types::daemon::SessionEvent;
    use serde_json::json;
    use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
    use tokio::net::UnixListener;
    use tokio::sync::mpsc;

    use super::*;
    use crate::daemon_client::{DaemonClientEvent, RequestRejected};

    fn amounts(cost_micros: u64, tokens: u64) -> BudgetAmounts {
        BudgetAmounts {
            cost_micros,
            tokens,
            ..BudgetAmounts::default()
        }
    }

    /// A budget of 5 dollars and 200k tokens with 1 dollar and 1.5k tokens
    /// spent: the typed report and its wire form.
    fn report() -> (BudgetReport, Value) {
        let report = BudgetReport {
            session_id: "s1".to_string(),
            limits: BudgetLimits {
                cost_micros: Some(5_000_000),
                tokens: Some(200_000),
                ..BudgetLimits::default()
            },
            free: amounts(4_000_000, 198_500),
            spent: amounts(1_000_000, 1_500),
            ..BudgetReport::default()
        };
        let zero = json!({ "costMicros": 0, "tokens": 0, "timeMs": 0, "toolCalls": 0 });
        let wire = json!({
            "sessionId": "s1",
            "limits": { "costMicros": 5_000_000, "tokens": 200_000 },
            "free": { "costMicros": 4_000_000, "tokens": 198_500, "timeMs": 0, "toolCalls": 0 },
            "held": zero,
            "spent": { "costMicros": 1_000_000, "tokens": 1_500, "timeMs": 0, "toolCalls": 0 },
            "lent": zero,
            "over": zero,
            "phase": "working",
        });
        (report, wire)
    }

    /// A scripted supervisor for one connection: the hello, then every
    /// command recorded on `seen` and answered as the daemon answers the
    /// budget commands. A command that changes the budget streams its
    /// `budget_update` ahead of its response. The session `empty` has no
    /// budget; the session `taken` has one already.
    async fn serve(listener: UnixListener, seen: mpsc::UnboundedSender<Value>, report: Value) {
        let (stream, _) = listener.accept().await.expect("accept");
        let (reader, mut writer) = stream.into_split();
        let mut lines = BufReader::new(reader).lines();
        let mut frames = vec![json!({
            "type": "daemon_hello",
            "protocol": { "name": "eukhe.daemon", "version": 7 },
            "clientId": "srv",
            "serverCapabilities": [],
        })];
        loop {
            for frame in frames.drain(..) {
                let line = format!("{frame}\n");
                writer.write_all(line.as_bytes()).await.expect("write");
            }
            let Ok(Some(line)) = lines.next_line().await else {
                return;
            };
            let envelope: Value = serde_json::from_str(&line).expect("an envelope");
            let command = envelope["command"].clone();
            let kind = command["type"].as_str().unwrap_or_default();
            let session = command["activeSessionId"].as_str().unwrap_or_default();
            let answer = match (kind, session) {
                ("get_budget", "empty") => Ok(json!({ "budget": null })),
                ("set_budget", "taken") => Err("session taken already has a budget"),
                ("set_budget" | "add_budget", _) => {
                    frames.push(json!({
                        "type": "session_event",
                        "activeSessionId": session,
                        "event": { "type": "budget_update", "budget": report },
                    }));
                    Ok(json!({ "budget": report }))
                }
                ("audit_budget", _) => Ok(json!({
                    "audit": {
                        "records": 9,
                        "settled": { "costMicros": 900_000, "tokens": 1_500 },
                        "spent": report["spent"],
                        "exact": false,
                        "firstMismatch": 4,
                    },
                })),
                _ => panic!("the test sends no {kind} for {session}"),
            };
            let mut response = json!({
                "type": "response",
                "id": envelope["id"],
                "command": kind,
                "success": answer.is_ok(),
            });
            match answer {
                Ok(data) => response["data"] = data,
                Err(error) => response["error"] = json!(error),
            }
            frames.push(response);
            let _ = seen.send(command);
        }
    }

    /// Each helper sends its command under its wire name and reads the
    /// typed answer; a refused `set_budget` is the daemon's typed
    /// rejection with the ledger's message; the `budget_update` event
    /// arrives as the session event it is.
    #[tokio::test]
    async fn the_budget_requests_send_the_wire_commands_and_read_the_typed_answers() {
        let dir = tempfile::TempDir::new().expect("tempdir");
        let socket = dir.path().join("d.sock");
        let listener = UnixListener::bind(&socket).expect("bind");
        let (seen, mut commands) = mpsc::unbounded_channel();
        let (report, wire) = report();
        tokio::spawn(serve(listener, seen, wire));
        let (client, mut events) = DaemonClient::connect(&socket).await.expect("connect");

        let limits = |cost_micros, tokens| BudgetLimits {
            cost_micros,
            tokens,
            ..BudgetLimits::default()
        };
        let none = client.get_budget("empty").await.expect("get_budget");
        let limited = client
            .set_budget("s1", limits(Some(5_000_000), Some(200_000)))
            .await
            .expect("set_budget");
        let added = client
            .add_budget("s1", amounts(1_000_000, 0))
            .await
            .expect("add_budget");
        let audit = client.audit_budget("s1").await.expect("audit_budget");
        let refused = client
            .set_budget("taken", limits(None, Some(7)))
            .await
            .expect_err("a session that has a budget refuses");
        let (session, event) = match tokio::time::timeout(Duration::from_secs(2), events.recv())
            .await
            .expect("an event in time")
        {
            Some(DaemonClientEvent::SessionEvent {
                active_session_id,
                event,
                ..
            }) => (active_session_id, *event),
            other => panic!("not a session event: {other:?}"),
        };
        client.close();

        assert_eq!(
            (none, limited, added, audit, session, event),
            (
                None,
                report.clone(),
                report.clone(),
                BudgetAudit {
                    records: 9,
                    settled: amounts(900_000, 1_500),
                    spent: amounts(1_000_000, 1_500),
                    exact: false,
                    first_mismatch: Some(4),
                },
                "s1".to_string(),
                SessionEvent::BudgetUpdate {
                    budget: Some(report),
                },
            )
        );
        assert_eq!(
            refused.downcast_ref::<RequestRejected>(),
            Some(&RequestRejected {
                command: "set_budget".to_string(),
                message: "session taken already has a budget".to_string(),
                error_info: None,
            })
        );
        let mut sent = Vec::new();
        while let Ok(command) = commands.try_recv() {
            sent.push(command);
        }
        assert_eq!(
            sent,
            vec![
                json!({ "type": "get_budget", "activeSessionId": "empty" }),
                json!({
                    "type": "set_budget",
                    "activeSessionId": "s1",
                    "limits": { "costMicros": 5_000_000, "tokens": 200_000 },
                }),
                json!({
                    "type": "add_budget",
                    "activeSessionId": "s1",
                    "amounts": { "costMicros": 1_000_000, "tokens": 0, "timeMs": 0, "toolCalls": 0, "requests": 0 },
                }),
                json!({ "type": "audit_budget", "activeSessionId": "s1" }),
                json!({
                    "type": "set_budget",
                    "activeSessionId": "taken",
                    "limits": { "tokens": 7 },
                }),
            ]
        );
    }
}
