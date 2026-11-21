//! The turns the supervisor interrupts itself: a worker it killed because
//! it stopped answering (`responsiveness.rs`), or a session whose worker
//! crashed past the restart budget (`supervision.rs`). Resuming such a run
//! as it stood would run the step that hung or crashed again, so the
//! supervisor keeps one declaration per session file until a worker reopens
//! that session: the reopen (the relaunch's create replay, or the next
//! launch over the file) carries it as `interruptedRun`, and the worker
//! opens the storage without resuming the run (`StoredWork::Stop`: the
//! run's tasks are aborted before scheduling starts) and continues the turn
//! with a harness continuation, at most three times a turn, else ends the
//! run with its report (`worker/interrupted_run.rs`; the compiled core
//! decides: `eukhe_bend::rules::restart_turn`). A give-up relaunches the
//! worker by itself unless the session's last relaunch never opened it or
//! ended its turn at the cap, so a crash loop goes on without anyone
//! watching and still ends.

use std::collections::HashMap;

use eukhe_bend::rules::restart_turn::{self, GaveUp, Prior};
use eukhe_types::daemon::{DaemonOutbound, SessionEvent};
use serde_json::{json, Value};

use crate::registry::canonical_session_file_string;

/// Why the supervisor interrupted a session's run.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum InterruptedRun {
    /// The worker left the responsiveness probe unanswered this many ms.
    Unresponsive { after_ms: u64 },
    /// The worker crashed this many times inside the restart window.
    CrashLoop { failures: u32 },
}

impl InterruptedRun {
    /// What happened, the start of the row the reopened session shows.
    fn cause(self) -> String {
        match self {
            Self::Unresponsive { after_ms } => format!(
                "The session worker stopped responding for {}s",
                after_ms / 1_000
            ),
            Self::CrashLoop { failures } => {
                format!("The session worker crashed {failures} times in a row")
            }
        }
    }

    /// The row of a worker given up for good: the run ended.
    fn given_up(self) -> String {
        format!(
            "{}; Eukhe stopped restarting it and ended the run.",
            self.cause()
        )
    }
}

impl super::Supervisor {
    /// A session given up with nobody to end its turn: the clients that
    /// follow it through the supervisor see the notice row, the turn fail
    /// with it, and the run end, so none keeps showing it busy.
    pub(super) fn end_followed_turn(&self, active_session_id: &str, run: InterruptedRun) {
        let row = eukhe_types::session::AgentMessage::Custom(eukhe_types::session::CustomMessage {
            custom_type: eukhe_types::custom_type::WORKER_RESTART_NOTICE_CUSTOM_TYPE.to_string(),
            content: eukhe_types::ai::UserContent::Text(run.given_up()),
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
                error: Some(run.given_up()),
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

/// One declaration: the `interruptedRun` payload a reopen carries, and its
/// identity (a newer declaration supersedes it).
#[derive(Debug, Clone, PartialEq)]
struct Declared {
    cause: String,
    declared_at: String,
}

/// What the supervisor holds for one session; none: its last relaunch is
/// clear.
#[derive(Debug, Clone, PartialEq)]
enum Record {
    /// A declaration no reopen settled yet.
    Pending(Declared),
    /// The last reopen, by the worker `worker_id`, ended the turn at the
    /// cap; the session's next run in that worker, or a client's launch of
    /// the session, clears it.
    Ended { worker_id: String },
}

/// The supervisor's records, keyed by the canonical session file.
#[derive(Debug, Default)]
pub(crate) struct InterruptedRuns {
    records: std::sync::Mutex<HashMap<String, Record>>,
}

impl InterruptedRuns {
    fn records(&self) -> std::sync::MutexGuard<'_, HashMap<String, Record>> {
        self.records
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    /// Declare that the supervisor interrupted the run of the session in
    /// `session_file`.
    pub(crate) fn declare(&self, session_file: &str, run: InterruptedRun) {
        let declared = Declared {
            cause: run.cause(),
            declared_at: format!("{}#{}", crate::util::now_iso(), uuid::Uuid::new_v4()),
        };
        self.records().insert(
            canonical_session_file_string(session_file),
            Record::Pending(declared),
        );
    }

    /// The restart budget gave up the worker of the session in
    /// `session_file`: the compiled core decides from its last relaunch
    /// whether the worker relaunches (its reopen decides the turn) or is
    /// given up. Either way the run is declared interrupted: the reopen
    /// that comes stops the run that crashed.
    pub(crate) fn give_up(&self, session_file: &str, run: InterruptedRun) -> GaveUp {
        let key = canonical_session_file_string(session_file);
        let prior = match self.records().get(&key) {
            None => Prior::Clear,
            Some(Record::Pending(_)) => Prior::Unsettled,
            Some(Record::Ended { .. }) => Prior::Ended,
        };
        let next = restart_turn::gave_up(prior);
        self.declare(session_file, run);
        next
    }

    /// The `interruptedRun` field a create over `session_file` carries, if
    /// the supervisor interrupted that session's run.
    pub(crate) fn payload_for(&self, session_file: &str) -> Option<Value> {
        match self
            .records()
            .get(&canonical_session_file_string(session_file))
        {
            Some(Record::Pending(declared)) => Some(json!({
                "cause": declared.cause,
                "declaredAt": declared.declared_at,
            })),
            Some(Record::Ended { .. }) | None => None,
        }
    }

    /// A client launches a worker over `session_file`: a new start, so a
    /// turn an earlier worker ended at the cap no longer holds back the
    /// next give-up (a pending declaration rides the launch).
    pub(crate) fn launched(&self, session_file: &str) {
        let key = canonical_session_file_string(session_file);
        let mut records = self.records();
        if matches!(records.get(&key), Some(Record::Ended { .. })) {
            records.remove(&key);
        }
    }

    /// A reopen over `session_file` by the worker `worker_id` answered
    /// `create` for the declaration it carried (`payload`): a persisted one
    /// retires that declaration (a newer one stays), and a reopen that
    /// ended the turn at the cap is remembered until the worker's next
    /// run; a failed one keeps it for the next reopen.
    pub(crate) fn settle(
        &self,
        session_file: &str,
        worker_id: &str,
        payload: &Value,
        create_data: Option<&Value>,
    ) {
        let flag = |key: &str| {
            create_data
                .and_then(|data| data.get(key))
                .and_then(Value::as_bool)
                .unwrap_or(false)
        };
        if !flag("interruptedRunPersisted") {
            return;
        }
        let declared_at = payload.get("declaredAt").and_then(Value::as_str);
        let key = canonical_session_file_string(session_file);
        let mut records = self.records();
        let settled = matches!(
            records.get(&key),
            Some(Record::Pending(declared)) if Some(declared.declared_at.as_str()) == declared_at
        );
        if !settled {
            return;
        }
        if flag("interruptedRunEnded") {
            records.insert(
                key,
                Record::Ended {
                    worker_id: worker_id.to_string(),
                },
            );
        } else {
            records.remove(&key);
        }
    }

    /// A run started in the worker `worker_id`: a turn it ended at the cap
    /// no longer holds back the next give-up.
    pub(crate) fn run_started(&self, worker_id: &str) {
        self.records().retain(
            |_, record| !matches!(record, Record::Ended { worker_id: ended } if ended == worker_id),
        );
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::{GaveUp, InterruptedRun, InterruptedRuns};

    /// A declaration rides every reopen of its session until one reports
    /// it persisted; a reopen that failed, or one that carried an older
    /// declaration, retires nothing.
    #[test]
    fn a_declaration_rides_each_reopen_until_one_persists_it() {
        let runs = InterruptedRuns::default();
        assert_eq!(runs.payload_for("/s/a.jsonl"), None);
        runs.declare(
            "/s/a.jsonl",
            InterruptedRun::Unresponsive { after_ms: 60_000 },
        );
        let first = runs.payload_for("/s/a.jsonl").expect("declared");
        assert_eq!(
            first["cause"],
            "The session worker stopped responding for 60s"
        );
        assert_eq!(runs.payload_for("/s/b.jsonl"), None);
        runs.settle(
            "/s/a.jsonl",
            "a",
            &first,
            Some(&json!({ "interruptedRunPersisted": false })),
        );
        assert_eq!(runs.payload_for("/s/a.jsonl"), Some(first.clone()));
        runs.declare("/s/a.jsonl", InterruptedRun::CrashLoop { failures: 6 });
        let second = runs.payload_for("/s/a.jsonl").expect("redeclared");
        runs.settle(
            "/s/a.jsonl",
            "a",
            &first,
            Some(&json!({ "interruptedRunPersisted": true })),
        );
        assert_eq!(runs.payload_for("/s/a.jsonl"), Some(second.clone()));
        runs.settle(
            "/s/a.jsonl",
            "a",
            &second,
            Some(&json!({ "interruptedRunPersisted": true })),
        );
        assert_eq!(runs.payload_for("/s/a.jsonl"), None);
    }

    /// A crash loop relaunches its worker by itself; it is given up only
    /// when the last relaunch never opened the session, or when the last
    /// reopen ended the turn at the cap and no run started since.
    #[test]
    fn a_crash_loop_relaunches_until_its_relaunch_fails_or_its_turn_ends() {
        let runs = InterruptedRuns::default();
        let crash = InterruptedRun::CrashLoop { failures: 6 };
        let settle = |ended: bool| {
            let payload = runs.payload_for("/s/a.jsonl").expect("declared");
            runs.settle(
                "/s/a.jsonl",
                "a",
                &payload,
                Some(&json!({ "interruptedRunPersisted": true, "interruptedRunEnded": ended })),
            );
        };
        let first = runs.give_up("/s/a.jsonl", crash);
        let unsettled = runs.give_up("/s/a.jsonl", crash);
        settle(false);
        let continued = runs.give_up("/s/a.jsonl", crash);
        settle(true);
        let ended = runs.give_up("/s/a.jsonl", crash);
        settle(true);
        runs.run_started("other");
        let other_run = runs.give_up("/s/a.jsonl", crash);
        settle(true);
        runs.run_started("a");
        let next_run = runs.give_up("/s/a.jsonl", crash);
        assert_eq!(
            [first, unsettled, continued, ended, other_run, next_run],
            [
                GaveUp::Relaunch,
                GaveUp::Retire,
                GaveUp::Relaunch,
                GaveUp::Retire,
                GaveUp::Retire,
                GaveUp::Relaunch,
            ]
        );
    }
}
