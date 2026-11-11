//! The acceptance commands (`set_acceptance`, `get_acceptance`): a client
//! of the session (an SDK, a script) sets the checks of the session's task
//! as its owner, and reads its acceptance. Both answer the main
//! conversation's `AcceptanceState`; the `acceptance_update` event carries
//! every later change.

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::durable::acceptance::{acceptance_state, set_acceptance};
use eukhe_types::acceptance::{owner_checks, AcceptanceState, CheckSpec};
use serde::Deserialize;
use serde_json::Value;

use crate::protocol::{response_failure, response_success, DaemonResponse};
use crate::worker::Worker;

/// The payload of `set_acceptance` (the `DaemonCommand::SetAcceptance`
/// fields; the routing fields are ignored).
#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct AcceptanceRequest {
    /// The explicit checks; none clears them.
    #[serde(default)]
    checks: Vec<CheckSpec>,
    /// The most returns in a row; the current cap when absent.
    #[serde(default)]
    max_returns: Option<u64>,
    /// Whether the intent check joins the explicit ones; absent is true.
    #[serde(default)]
    intent: Option<bool>,
}

impl AcceptanceRequest {
    /// The request in `payload`.
    ///
    /// # Errors
    ///
    /// `checks` is not a list of checks, or a field has the wrong type.
    pub(crate) fn parse(payload: &Value) -> Result<Self, serde_json::Error> {
        Self::deserialize(payload)
    }

    /// The checks the owner sets: the explicit ones, then the intent
    /// check unless the request turns it off.
    pub(crate) fn specs(self) -> (Vec<CheckSpec>, Option<u64>) {
        (
            owner_checks(self.checks, self.intent.unwrap_or(true)),
            self.max_returns,
        )
    }
}

/// The response data of an acceptance command.
fn state_data(state: &AcceptanceState) -> Value {
    serde_json::to_value(state).unwrap_or(Value::Null)
}

impl Worker {
    /// `set_acceptance { checks?, maxReturns?, intent? }`: set the checks
    /// of the main conversation's task as its owner and answer the new
    /// `AcceptanceState`. A check with no command or condition, or more
    /// checks than a task may carry, answers as the command's error.
    pub(crate) async fn handle_set_acceptance(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "set_acceptance";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let request = match AcceptanceRequest::parse(payload) {
            Ok(request) => request,
            Err(error) => {
                return response_failure(
                    None,
                    COMMAND,
                    &format!("Invalid acceptance checks: {error}"),
                    None,
                );
            }
        };
        let (specs, max_returns) = request.specs();
        let set = async {
            let main = hosted.main()?;
            let state = set_acceptance(
                hosted.harness(),
                main.id(),
                specs,
                max_returns,
                &hosted.deps().cwd,
                &BACKGROUND_CONTEXT,
            )
            .await?;
            anyhow::Ok(state)
        }
        .await;
        match set {
            Ok(state) => {
                // The change reaches attached clients as `acceptance_update`;
                // answer once it is on the wire.
                hosted.events_delivered().await;
                response_success(None, COMMAND, Some(state_data(&state)))
            }
            Err(error) => response_failure(None, COMMAND, &format!("{error:#}"), None),
        }
    }

    /// `get_acceptance`: the main conversation's `AcceptanceState`.
    pub(crate) async fn handle_get_acceptance(&self) -> DaemonResponse {
        const COMMAND: &str = "get_acceptance";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let read = async {
            let main = hosted.main()?;
            let state = acceptance_state(hosted.harness(), main.id(), &BACKGROUND_CONTEXT).await?;
            anyhow::Ok(state)
        }
        .await;
        match read {
            Ok(state) => response_success(None, COMMAND, Some(state_data(&state))),
            Err(error) => response_failure(None, COMMAND, &format!("{error:#}"), None),
        }
    }
}

#[cfg(test)]
mod tests;
