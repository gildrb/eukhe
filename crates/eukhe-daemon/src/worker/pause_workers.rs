//! `pause_workers` / `resume_workers`: pause or resume a session's worker
//! tree. Without `ownRun` (a client on main): main's workers and their
//! trees (`eukhe_core::durable::children::pause_workers`); main keeps
//! talking. With `ownRun` (a parent on its child): this session's own run
//! and every child with work in flight
//! (`eukhe_core::durable::children::pause_own_tree`). A pause cancels
//! nothing: running model requests and tool calls finish, and the next
//! request, tool call or spawn waits. The reply is `{workers}`, this
//! session's worker rows after the change.

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::durable::children::{list_workers, pause_own_tree, pause_workers, PauseAction};
use serde_json::{json, Value};

use super::{response_failure, response_success, Worker};
use crate::protocol::DaemonResponse;

impl Worker {
    pub(crate) async fn handle_pause_workers(
        &self,
        payload: &Value,
        action: PauseAction,
    ) -> DaemonResponse {
        let command = match action {
            PauseAction::Pause => "pause_workers",
            PauseAction::Resume => "resume_workers",
        };
        let hosted = match self.hosted(command) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let main = match hosted.main() {
            Ok(main) => main,
            Err(error) => return response_failure(None, command, &error.to_string(), None),
        };
        let Some(host) = hosted.deps().children.clone() else {
            return response_failure(
                None,
                command,
                "This session has no child runtime: it has no workers",
                None,
            );
        };
        let cx = &BACKGROUND_CONTEXT;
        let own_run = payload.get("ownRun").and_then(Value::as_bool) == Some(true);
        let workers = if own_run {
            match pause_own_tree(
                hosted.harness(),
                host.as_ref(),
                &hosted.deps().run_pause,
                main.id(),
                action,
                cx,
            )
            .await
            {
                Ok(()) => list_workers(hosted.harness(), main.id(), cx)
                    .await
                    .map_err(anyhow::Error::new),
                Err(error) => Err(error),
            }
        } else {
            pause_workers(hosted.harness(), host.as_ref(), main.id(), action, cx).await
        };
        match workers {
            Ok(workers) => {
                self.push_roster_delta();
                response_success(None, command, Some(json!({ "workers": workers })))
            }
            Err(error) => response_failure(None, command, &format!("{error:#}"), None),
        }
    }
}
