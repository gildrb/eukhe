//! The `/workflows` page's session surface: the page open (the
//! `/workflows` command and the dock's workflow group), the view's key
//! loop, the 2-second refresh over the daemon's `workflow_activity` lane,
//! and the `workflow_cancel` action.

use std::time::Duration;

use anyhow::Result;
use eukhe_types::daemon::DaemonCommand;
use eukhe_types::workflow::WorkflowRunSnapshot;
use serde_json::{Map, Value};

use super::AgentView;
use crate::session_ui::{picker_viewport_rows, UI_REQUEST_TIMEOUT_MS};
use crate::workflow_view::{parse_workflow_runs, WorkflowView, WorkflowViewAction};

/// One background refresh's delivery: the session it asked about and the
/// epoch it was issued under (a late or foreign reply never repaints).
pub(crate) struct WorkflowUpdate {
    session: String,
    epoch: u64,
    runs: Result<Vec<WorkflowRunSnapshot>, String>,
}

/// The workflow lane's state on the session UI.
#[derive(Default)]
pub(crate) struct WorkflowLane {
    /// The last good runs (the dock count and the page mount).
    pub(crate) runs: Vec<WorkflowRunSnapshot>,
    in_flight: bool,
    epoch: u64,
}

impl super::SessionUi {
    /// Whether the daemon advertises the `workflow_activity` lane.
    pub(crate) fn workflow_activity_supported(&self) -> bool {
        self.client
            .hello()
            .get("serverCapabilities")
            .and_then(Value::as_array)
            .is_some_and(|caps| {
                caps.iter()
                    .any(|cap| cap.as_str() == Some("workflow_activity"))
            })
    }

    /// Open the `/workflows` page from the cached runs, then refresh.
    pub(crate) fn open_workflows_page(&mut self, view: &mut AgentView) {
        if !self.workflow_activity_supported() {
            self.note(
                "The workflows page needs a daemon that advertises the workflow lane",
                view,
            );
            return;
        }
        view.workflow_view = Some(WorkflowView::new(
            self.workflow_lane.runs.clone(),
            picker_viewport_rows(view.terminal_rows()),
        ));
        self.subagents_focused = false;
        self.dirty = true;
        self.spawn_workflow_refresh();
    }

    /// One key press while the page is open.
    pub(crate) async fn handle_workflow_view_key(
        &mut self,
        key: crossterm::event::KeyEvent,
        view: &mut AgentView,
    ) -> Result<()> {
        let Some(id) = super::key_event_to_id(&key) else {
            return Ok(());
        };
        if id == "ctrl+c" {
            self.exit_guard.note_ctrl_c_handled();
        }
        let action = view
            .workflow_view
            .as_mut()
            .map(|page| page.handle_key(&id, view.editor.keybindings()));
        self.dirty = true;
        match action {
            Some(WorkflowViewAction::None) | None => {}
            Some(WorkflowViewAction::Close) => view.workflow_view = None,
            Some(WorkflowViewAction::OpenAgents) => {
                view.workflow_view = None;
                if self.return_to_agents_view {
                    self.open_scoped_agents_view(view);
                } else {
                    self.note("The agents view needs a daemon-hosted session", view);
                }
            }
            Some(WorkflowViewAction::Cancel { run_id }) => {
                let cancelled = self
                    .bounded_request(
                        Duration::from_millis(UI_REQUEST_TIMEOUT_MS),
                        DaemonCommand::WorkflowCancel {
                            id: None,
                            active_session_id: self.active_session_id.clone(),
                            run_id: run_id.clone(),
                            rest: Map::default(),
                        },
                    )
                    .await;
                match cancelled {
                    Ok(_) => self.toast(&format!("Workflow run {run_id} cancelled"), view),
                    Err(error) => match view.workflow_view.as_mut() {
                        Some(page) => page.set_error(Some(format!("{error:#}"))),
                        None => self.error_row(&format!("{error:#}"), view),
                    },
                }
                self.spawn_workflow_refresh();
            }
        }
        Ok(())
    }

    /// Fetch the runs in the background; at most one fetch in flight.
    pub(crate) fn spawn_workflow_refresh(&mut self) {
        if !self.workflow_activity_supported() || self.workflow_lane.in_flight {
            return;
        }
        self.workflow_lane.in_flight = true;
        self.workflow_lane.epoch += 1;
        let epoch = self.workflow_lane.epoch;
        let client = self.client.clone();
        let session = self.active_session_id.clone();
        let tx = self.workflow_updates.clone();
        tokio::spawn(async move {
            let request = client.request_ok(DaemonCommand::WorkflowActivity {
                id: None,
                active_session_id: session.clone(),
                rest: Map::default(),
            });
            let runs =
                match tokio::time::timeout(Duration::from_millis(UI_REQUEST_TIMEOUT_MS), request)
                    .await
                {
                    Ok(Ok(data)) => parse_workflow_runs(&data)
                        .ok_or_else(|| "malformed workflow reply (no runs list)".to_owned()),
                    Ok(Err(error)) => Err(format!("{error:#}")),
                    Err(_) => Err("timed out waiting for the Eukhe daemon response".to_owned()),
                };
            let _ = tx.send(WorkflowUpdate {
                session,
                epoch,
                runs,
            });
        });
    }

    /// Fold one delivery into the cache, the open page, and the dock.
    pub(crate) fn apply_workflow_update(&mut self, update: WorkflowUpdate, view: &mut AgentView) {
        self.workflow_lane.in_flight = false;
        if update.session != self.active_session_id || update.epoch != self.workflow_lane.epoch {
            return;
        }
        match update.runs {
            Ok(runs) => {
                if let Some(page) = view.workflow_view.as_mut() {
                    page.set_error(None);
                    page.apply_runs(runs.clone());
                }
                self.workflow_lane.runs = runs;
            }
            Err(message) => {
                if let Some(page) = view.workflow_view.as_mut() {
                    page.set_error(Some(message));
                }
            }
        }
        self.sync_activity_dock(view);
        self.dirty = true;
    }
}
