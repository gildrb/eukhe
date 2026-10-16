//! The supervisor's operator-note surface: the session-channel notes, the
//! rotating log line, and the spawn-ledger assembly.
use super::subscribers::{event_line, EventLine};
use super::{paths, util, Arc, Result, Supervisor, Value};

impl Supervisor {
    /// Publish one supervisor-built session frame: serialized once, then
    /// shared by every attached connection.
    pub(crate) fn publish_session_event(&self, active_session_id: &str, frame: &Value) {
        match serde_json::to_vec(frame) {
            Ok(json) => self.publish_session_line(active_session_id, &event_line(json)),
            Err(error) => self.log_line(&format!(
                "session frame serialization failed (session {active_session_id}): {error}"
            )),
        }
    }

    /// Publish one session line to the session's attached connections
    /// (the send-time delivery pass — TS `handleWorkerFrame`'s fan-out
    /// evaluates the attached set in the same pass that writes). A full
    /// queue drops the frame and the stall-cycle transition lands in the
    /// daemon log (finding 4a visibility).
    pub(crate) fn publish_session_line(&self, active_session_id: &str, line: &EventLine) {
        let outcome = self.session_subscribers.publish(active_session_id, line);
        if !outcome.lagged.is_empty() {
            self.log_line(&format!(
                "clients {} lagged on the session event queue: frames dropped (session {active_session_id})",
                outcome.lagged.join(", ")
            ));
        }
    }

    pub(crate) fn log_line(&self, message: &str) {
        self.log.append(&format!("[{}] {message}", util::now_iso()));
    }

    /// The spawn ledger for one sessions dir (TS `rlmSpawnLedgerFor`): the
    /// default dir's ledger is memoized; any other dir constructs a fresh
    /// instance (its seeding no-ops when its ledger file exists).
    pub(crate) async fn rlm_spawn_ledger_for(
        self: &Arc<Self>,
        session_dir: Option<&str>,
    ) -> Result<std::sync::Arc<crate::rlm_ledger::RlmSpawnLedger>> {
        let default_dir = paths::sessions_dir(&self.options.agent_dir)?;
        let requested = match session_dir {
            Some(dir) => paths::expand_tilde(dir)?,
            None => default_dir.clone(),
        };
        if requested != default_dir {
            let log = paths::RotatingLog::new(paths::daemon_log_path(
                &self.options.socket_path,
                &self.options.agent_dir,
            ));
            return Ok(std::sync::Arc::new(crate::rlm_ledger::RlmSpawnLedger::new(
                &self.options.agent_dir,
                &requested,
                move |message| {
                    log.append(&format!("[{}] {message}", util::now_iso()));
                },
            )));
        }
        let mut cached = self.rlm_ledger.lock().await;
        if let Some(ledger) = cached.as_ref() {
            return Ok(std::sync::Arc::clone(ledger));
        }
        let log = paths::RotatingLog::new(paths::daemon_log_path(
            &self.options.socket_path,
            &self.options.agent_dir,
        ));
        let ledger = std::sync::Arc::new(crate::rlm_ledger::RlmSpawnLedger::new(
            &self.options.agent_dir,
            &requested,
            move |message| {
                log.append(&format!("[{}] {message}", util::now_iso()));
            },
        ));
        *cached = Some(std::sync::Arc::clone(&ledger));
        Ok(ledger)
    }
}
