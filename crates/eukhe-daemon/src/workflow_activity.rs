//! The `workflow_activity` and `workflow_cancel` worker arms: the
//! `/workflows` view's lane over the main conversation's dynamic workflow
//! runs (`eukhe_core::durable::workflow`).

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::durable::workflow::{cancel_run, snapshots};
use serde_json::{json, Value};

use crate::protocol::{response_failure, response_success, DaemonResponse};
use crate::worker::Worker;

impl Worker {
    /// `workflow_activity`: `{runs: [WorkflowRunSnapshot]}`, newest first.
    pub(crate) async fn handle_workflow_activity(&self) -> DaemonResponse {
        const COMMAND: &str = "workflow_activity";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let main = match hosted.main() {
            Ok(main) => main,
            Err(error) => return response_failure(None, COMMAND, &error.to_string(), None),
        };
        let runs = match snapshots(
            hosted.harness(),
            main.id(),
            &hosted.deps().session_id,
            &BACKGROUND_CONTEXT,
        )
        .await
        {
            Ok(runs) => runs,
            Err(error) => return response_failure(None, COMMAND, &error.to_string(), None),
        };
        response_success(None, COMMAND, Some(json!({ "runs": runs })))
    }

    /// `workflow_cancel`: cancel the run `runId`; `{cancelled}` is `false`
    /// when no running run has that id.
    pub(crate) async fn handle_workflow_cancel(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "workflow_cancel";
        let Some(run_id) = payload
            .get("runId")
            .and_then(Value::as_str)
            .filter(|run| !run.is_empty())
        else {
            return response_failure(None, COMMAND, "runId is required", None);
        };
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let main = match hosted.main() {
            Ok(main) => main,
            Err(error) => return response_failure(None, COMMAND, &error.to_string(), None),
        };
        match cancel_run(hosted.harness(), main.id(), run_id, &BACKGROUND_CONTEXT).await {
            Ok(cancelled) => {
                response_success(None, COMMAND, Some(json!({ "cancelled": cancelled })))
            }
            Err(error) => response_failure(None, COMMAND, &format!("{error:#}"), None),
        }
    }
}
