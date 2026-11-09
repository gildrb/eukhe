//! The turns the supervisor ends itself: a worker it killed because it
//! stopped answering (`responsiveness.rs`), or a session whose worker
//! crashed past the restart budget (`supervision.rs`). Restarting such a
//! worker would resume the very run that hung or crashed, so the
//! supervisor keeps one notice per session file until a worker reopens
//! that session: the reopen (the relaunch's create replay, or the next
//! launch over the file) carries it as `interruptedRun`, and the worker
//! opens the storage without resuming the run (`StoredWork::Stop`: the
//! run's tasks are aborted before scheduling starts, so no model request
//! or tool of it runs again) and writes the notice as a display-only row
//! (`worker/create.rs` `write_interrupted_run_notice`). Every client then
//! shows why the turn ended, and none waits on a run that will not answer.

use std::collections::HashMap;

use eukhe_types::daemon::{DaemonOutbound, SessionEvent};
use serde_json::{json, Value};

use crate::registry::canonical_session_file_string;

/// Why the supervisor ended a session's run.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum InterruptedRun {
    /// The worker left the responsiveness probe unanswered this many ms.
    Unresponsive { after_ms: u64 },
    /// The worker crashed this many times inside the restart window.
    CrashLoop { failures: u32 },
}

impl InterruptedRun {
    /// The row the reopened session shows: what happened, and the next step.
    fn notice(self) -> String {
        match self {
            Self::Unresponsive { after_ms } => format!(
                "The session worker stopped responding for {}s; Eukhe restarted it and stopped the turn. Send the message again to retry.",
                after_ms / 1_000
            ),
            Self::CrashLoop { failures } => format!(
                "The session worker crashed {failures} times in a row; Eukhe stopped restarting it and stopped the turn. Send the message again to retry."
            ),
        }
    }
}

impl super::Supervisor {
    /// A session given up with nobody to end its turn: the clients that
    /// follow it through the supervisor see the notice row (the one the
    /// reopened transcript keeps), the turn fail with it, and the run end,
    /// so none keeps showing it busy.
    pub(super) fn end_followed_turn(&self, active_session_id: &str, run: InterruptedRun) {
        let row = eukhe_types::session::AgentMessage::Custom(eukhe_types::session::CustomMessage {
            custom_type: eukhe_types::custom_type::WORKER_RESTART_NOTICE_CUSTOM_TYPE.to_string(),
            content: eukhe_types::ai::UserContent::Text(run.notice()),
            display: true,
            details: None,
            timestamp: crate::util::now_ms(),
            rest: serde_json::Map::default(),
        });
        for event in [
            SessionEvent::MessageStart {
                message: row.clone(),
                assistant_message_event: None,
            },
            SessionEvent::MessageEnd { message: row },
            SessionEvent::TurnEnd {
                answer: None,
                error: Some(run.notice()),
            },
            SessionEvent::AgentEnd {
                messages: Vec::new(),
            },
        ] {
            let outbound = DaemonOutbound::SessionEvent {
                active_session_id: active_session_id.to_string(),
                event,
                meta: None,
                rest: serde_json::Map::default(),
            };
            match serde_json::to_vec(&outbound) {
                Ok(line) => self.publish_session_line(
                    active_session_id,
                    &super::subscribers::event_line(line),
                ),
                Err(error) => self.log_line(&format!(
                    "the turn end of given-up session {active_session_id} did not serialize: {error}"
                )),
            }
        }
    }
}

/// One declared notice: the `interruptedRun` payload a reopen carries, and
/// its identity (a newer declaration supersedes it).
#[derive(Debug, Clone, PartialEq)]
struct Declared {
    notice: String,
    declared_at: String,
}

/// The pending notices, keyed by the canonical session file.
#[derive(Debug, Default)]
pub(crate) struct InterruptedRuns {
    pending: std::sync::Mutex<HashMap<String, Declared>>,
}

impl InterruptedRuns {
    /// Declare that the supervisor ended the run of the session in
    /// `session_file`.
    pub(crate) fn declare(&self, session_file: &str, run: InterruptedRun) {
        let declared = Declared {
            notice: run.notice(),
            declared_at: format!("{}#{}", crate::util::now_iso(), uuid::Uuid::new_v4()),
        };
        self.pending
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .insert(canonical_session_file_string(session_file), declared);
    }

    /// The `interruptedRun` field a create over `session_file` carries, if
    /// the supervisor ended that session's run.
    pub(crate) fn payload_for(&self, session_file: &str) -> Option<Value> {
        self.pending
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .get(&canonical_session_file_string(session_file))
            .map(|declared| {
                json!({
                    "notice": declared.notice,
                    "declaredAt": declared.declared_at,
                })
            })
    }

    /// A reopen over `session_file` answered `create` for the notice it
    /// carried (`payload`): a stopped run retires that declaration (a
    /// newer one stays), a failed stop keeps it for the next reopen.
    pub(crate) fn settle(&self, session_file: &str, payload: &Value, create_data: Option<&Value>) {
        let persisted = create_data
            .and_then(|data| data.get("interruptedRunPersisted"))
            .and_then(Value::as_bool)
            .unwrap_or(false);
        if !persisted {
            return;
        }
        let declared_at = payload.get("declaredAt").and_then(Value::as_str);
        let mut pending = self
            .pending
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let key = canonical_session_file_string(session_file);
        if pending
            .get(&key)
            .is_some_and(|declared| Some(declared.declared_at.as_str()) == declared_at)
        {
            pending.remove(&key);
        }
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::{InterruptedRun, InterruptedRuns};

    /// A declaration rides every reopen of its session until one reports
    /// the run stopped; a reopen that failed to stop it, or one that
    /// carried an older declaration, retires nothing.
    #[test]
    fn a_notice_rides_each_reopen_until_one_stops_the_run() {
        let runs = InterruptedRuns::default();
        assert_eq!(runs.payload_for("/s/a.jsonl"), None);
        runs.declare(
            "/s/a.jsonl",
            InterruptedRun::Unresponsive { after_ms: 60_000 },
        );
        let first = runs.payload_for("/s/a.jsonl").expect("declared");
        assert_eq!(
            first["notice"],
            "The session worker stopped responding for 60s; Eukhe restarted it and stopped the turn. Send the message again to retry."
        );
        assert_eq!(runs.payload_for("/s/b.jsonl"), None);
        runs.settle(
            "/s/a.jsonl",
            &first,
            Some(&json!({ "interruptedRunPersisted": false })),
        );
        assert_eq!(runs.payload_for("/s/a.jsonl"), Some(first.clone()));
        runs.declare("/s/a.jsonl", InterruptedRun::CrashLoop { failures: 6 });
        let second = runs.payload_for("/s/a.jsonl").expect("redeclared");
        runs.settle(
            "/s/a.jsonl",
            &first,
            Some(&json!({ "interruptedRunPersisted": true })),
        );
        assert_eq!(runs.payload_for("/s/a.jsonl"), Some(second.clone()));
        runs.settle(
            "/s/a.jsonl",
            &second,
            Some(&json!({ "interruptedRunPersisted": true })),
        );
        assert_eq!(runs.payload_for("/s/a.jsonl"), None);
    }
}
