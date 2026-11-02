//! The main session's workers from the interface (docs/interface.md,
//! "Worker pane"): the workers main's roster row lists, the live pane on
//! the first one (a watch attach), the pane keys, and pause and resume
//! (`/pause`, `/resume`, Esc twice within [`PAUSE_ESCAPE_WINDOW`] while a
//! worker runs).
//!
//! Pause and resume are the daemon's (`pause_workers` /
//! `resume_workers`): a pause lets the running model request and tool
//! calls finish and starts nothing new; nothing is killed. The interface
//! only asks and shows the answer.

use eukhe_types::daemon::{DaemonClientKind, SessionWorker, WorkerRunState};
use serde::Deserialize;
use serde_json::{Map, Value};

use super::{AgentView, DaemonCommand, SessionUi};
use crate::chat::StatusKind;
use crate::worker_pane::{PaneMode, WorkerPane};

/// The double-Escape window that pauses a running worker.
pub(super) const PAUSE_ESCAPE_WINDOW: std::time::Duration = std::time::Duration::from_secs(1);

/// What a worker request asked.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum WorkerAction {
    Pause,
    Resume,
}

/// A worker request's answer, folded back on the UI loop.
#[derive(Debug)]
pub(crate) enum WorkerOutcome {
    /// The pane's watch attach answered (the attach data, or the failure).
    Attached {
        worker: String,
        result: Result<Value, String>,
    },
    /// A pause or resume answered: main's workers after it, or the
    /// failure.
    Control {
        /// The main session that asked: another session's answer is
        /// dropped.
        main: String,
        action: WorkerAction,
        result: Result<Vec<SessionWorker>, String>,
    },
}

/// A pane key.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum PaneKey {
    /// `app.worker.toggle`: show or hide the pane.
    Toggle,
    /// `app.worker.full`: the full view, or back from it.
    Full,
}

/// The pane's mode after `key`.
fn after_key(mode: PaneMode, key: PaneKey) -> PaneMode {
    match (key, mode) {
        (PaneKey::Toggle, PaneMode::Hidden) | (PaneKey::Full, PaneMode::Full) => PaneMode::Docked,
        (PaneKey::Toggle, PaneMode::Docked | PaneMode::Full) => PaneMode::Hidden,
        (PaneKey::Full, PaneMode::Hidden | PaneMode::Docked) => PaneMode::Full,
    }
}

impl SessionUi {
    /// Main's workers, from its own roster row (`summary.workers`).
    fn roster_workers(&self) -> Vec<SessionWorker> {
        self.roster
            .iter()
            .filter_map(|row| row.get("summary"))
            .find(|summary| {
                summary.get("activeSessionId").and_then(Value::as_str)
                    == Some(self.active_session_id.as_str())
            })
            .and_then(|summary| summary.get("workers"))
            .and_then(|workers| Vec::<SessionWorker>::deserialize(workers).ok())
            .unwrap_or_default()
    }

    /// Follow main's roster row: the workers it lists, and the pane on
    /// the first one that is not stopped (a new worker gets a pane and its
    /// watch attach; a pane whose worker left goes, its watch detached).
    pub(super) fn sync_workers(&mut self, view: &mut AgentView) {
        let workers = self.roster_workers();
        self.set_workers(workers, view);
    }

    fn set_workers(&mut self, workers: Vec<SessionWorker>, view: &mut AgentView) {
        self.workers = workers;
        let shown = self
            .workers
            .iter()
            .find(|worker| worker.state != WorkerRunState::Stopped)
            .or_else(|| {
                // A stopped worker keeps its pane (it says `stopped`).
                view.worker_pane.as_ref().and_then(|pane| {
                    self.workers
                        .iter()
                        .find(|worker| worker.active_session_id == pane.active_session_id)
                })
            })
            .cloned();
        match (shown, view.worker_pane.as_mut()) {
            (Some(worker), Some(pane)) if pane.active_session_id == worker.active_session_id => {
                pane.state = worker.state;
                pane.name = worker.name;
            }
            (Some(worker), _) => {
                let mode = view
                    .worker_pane
                    .as_ref()
                    .map_or(PaneMode::Docked, |pane| pane.mode);
                self.drop_worker_pane(view);
                let mut pane = WorkerPane::new(
                    worker.active_session_id.clone(),
                    worker.name,
                    worker.state,
                    view.theme.clone(),
                );
                pane.mode = mode;
                view.worker_pane = Some(pane);
                self.watch_worker(worker.active_session_id);
            }
            (None, Some(_)) => self.drop_worker_pane(view),
            (None, None) => {}
        }
        self.dirty = true;
    }

    /// Take the pane down and detach its watch.
    fn drop_worker_pane(&self, view: &mut AgentView) {
        let Some(pane) = view.worker_pane.take() else {
            return;
        };
        let client = self.client.clone();
        tokio::spawn(async move {
            // The watch only fed the pane: a failed detach leaves a
            // display-only subscription that ends with the connection.
            let _ = client
                .request_ok(DaemonCommand::Detach {
                    id: None,
                    active_session_id: Some(pane.active_session_id),
                    rest: Map::default(),
                })
                .await;
        });
    }

    /// Watch-attach the worker `worker` off the UI loop; the answer folds
    /// back as [`WorkerOutcome::Attached`].
    fn watch_worker(&self, worker: String) {
        let client = self.client.clone();
        let updates = self.agents_updates.clone();
        tokio::spawn(async move {
            let result = crate::saved_sessions::attach(&client, &worker, DaemonClientKind::Watch)
                .await
                .map_err(|error| format!("{error:#}"));
            let _ = updates.send(super::AgentsUpdate::Worker(WorkerOutcome::Attached {
                worker,
                result,
            }));
        });
    }

    /// A worker of main runs now (the double Escape pauses it).
    pub(super) fn worker_running(&self) -> bool {
        self.workers
            .iter()
            .any(|worker| worker.state == WorkerRunState::Running)
    }

    /// A worker of main is paused (bare `/resume` resumes it).
    pub(super) fn worker_paused(&self) -> bool {
        self.workers
            .iter()
            .any(|worker| worker.state == WorkerRunState::Paused)
    }

    /// Ask the daemon to pause or resume main's workers, off the UI loop.
    pub(super) fn control_workers(&mut self, action: WorkerAction, view: &mut AgentView) {
        if self.workers.is_empty() {
            self.note_as("This session has no worker.", StatusKind::Warning, view);
            return;
        }
        let main = self.active_session_id.clone();
        let command = match action {
            WorkerAction::Pause => DaemonCommand::PauseWorkers {
                id: None,
                active_session_id: main.clone(),
                own_run: None,
                rest: Map::default(),
            },
            WorkerAction::Resume => DaemonCommand::ResumeWorkers {
                id: None,
                active_session_id: main.clone(),
                own_run: None,
                rest: Map::default(),
            },
        };
        self.note(
            match action {
                WorkerAction::Pause => {
                    "Pausing the worker: the running model request and tool calls finish, nothing new starts."
                }
                WorkerAction::Resume => "Resuming the worker where it paused.",
            },
            view,
        );
        let client = self.client.clone();
        let updates = self.agents_updates.clone();
        tokio::spawn(async move {
            let result = client
                .request_ok(command)
                .await
                .map_err(|error| format!("{error:#}"))
                .and_then(|data| {
                    data.get("workers")
                        .cloned()
                        .map(Vec::<SessionWorker>::deserialize)
                        .transpose()
                        .map(Option::unwrap_or_default)
                        .map_err(|error| format!("the daemon answered no workers: {error}"))
                });
            let _ = updates.send(super::AgentsUpdate::Worker(WorkerOutcome::Control {
                main,
                action,
                result,
            }));
        });
    }

    /// Fold one worker request's answer.
    pub(super) fn apply_worker_outcome(&mut self, outcome: WorkerOutcome, view: &mut AgentView) {
        match outcome {
            WorkerOutcome::Attached { worker, result } => {
                if let Some(pane) = view
                    .worker_pane
                    .as_mut()
                    .filter(|pane| pane.active_session_id == worker)
                {
                    pane.attached(result);
                }
            }
            WorkerOutcome::Control {
                main,
                action,
                result,
            } => {
                if main != self.active_session_id {
                    return;
                }
                match result {
                    Ok(workers) => {
                        if workers.is_empty() {
                            self.note_as("This session has no worker.", StatusKind::Warning, view);
                        }
                        self.set_workers(workers, view);
                    }
                    Err(error) => {
                        let verb = match action {
                            WorkerAction::Pause => "pause",
                            WorkerAction::Resume => "resume",
                        };
                        self.error_row(&format!("Could not {verb} the worker: {error}"), view);
                    }
                }
            }
        }
        self.dirty = true;
    }

    /// One pane key: show, hide, or the full view. Without a worker the
    /// key says so.
    pub(super) fn worker_pane_key(&mut self, key: PaneKey, view: &mut AgentView) {
        match view.worker_pane.as_mut() {
            Some(pane) => pane.mode = after_key(pane.mode, key),
            None => self.note_as("This session has no worker.", StatusKind::Warning, view),
        }
        self.dirty = true;
    }

    /// Esc on the full pane returns to the docked pane; `false` when the
    /// pane is not in its full view (the Esc goes on).
    pub(super) fn leave_full_worker_pane(&mut self, view: &mut AgentView) -> bool {
        match view.worker_pane.as_mut() {
            Some(pane) if pane.mode == PaneMode::Full => {
                pane.mode = PaneMode::Docked;
                self.dirty = true;
                true
            }
            Some(_) | None => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{after_key, PaneKey};
    use crate::worker_pane::PaneMode;

    #[test]
    fn pane_keys_move_between_hidden_docked_and_full() {
        let modes = [PaneMode::Hidden, PaneMode::Docked, PaneMode::Full];
        assert_eq!(
            modes.map(|mode| (
                after_key(mode, PaneKey::Toggle),
                after_key(mode, PaneKey::Full)
            )),
            [
                (PaneMode::Docked, PaneMode::Full),
                (PaneMode::Hidden, PaneMode::Full),
                (PaneMode::Hidden, PaneMode::Docked),
            ]
        );
    }
}
