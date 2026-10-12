//! The daemon's language servers: the supervisor hosts one
//! [`LspService`] shared by every session (servers keyed by project root),
//! and each worker's sessions reach it over the supervisor link
//! ([`LinkLsp`]) with the `lsp` command.

use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;

use eukhe_lsp::LspHost;
use eukhe_types::lsp::{LspError, LspRequest, LspResponse};
use serde_json::json;

use crate::protocol::{response_failure, response_success, DaemonResponse};
use crate::supervisor::Supervisor;
use crate::supervisor_link::SupervisorLink;

/// Link deadline of one LSP request. The service bounds its own work
/// (initialize 10 s, project load 15 s, each request 30 s, the late
/// diagnostics window 12 s); this only catches a supervisor that stops
/// answering.
const LINK_TIMEOUT: Duration = Duration::from_mins(2);

impl Supervisor {
    /// `lsp`: answer one worker's LSP request from the shared service.
    pub(crate) async fn handle_lsp(
        self: &Arc<Self>,
        command_id: &str,
        type_name: &str,
        worker_token: &str,
        request: &LspRequest,
    ) -> DaemonResponse {
        if self.registry.find_by_token(worker_token).await.is_none() {
            return response_failure(
                Some(command_id),
                type_name,
                "Worker authentication failed",
                None,
            );
        }
        match self.lsp.call(request.clone()).await {
            Ok(response) => response_success(Some(command_id), type_name, Some(json!(response))),
            Err(error) => DaemonResponse {
                data: Some(json!(error)),
                ..response_failure(Some(command_id), type_name, &error.to_string(), None)
            },
        }
    }
}

/// A worker's LSP authority: the supervisor's shared service, one link
/// connection per request.
pub(crate) struct LinkLsp {
    link: SupervisorLink,
    worker_token: String,
}

impl LinkLsp {
    pub(crate) fn new(supervisor_socket_path: PathBuf, worker_token: String) -> Self {
        Self {
            link: SupervisorLink::new(supervisor_socket_path),
            worker_token,
        }
    }
}

impl LspHost for LinkLsp {
    async fn call(&self, request: LspRequest) -> Result<LspResponse, LspError> {
        let command = json!({
            "type": "lsp",
            "workerToken": self.worker_token,
            "request": request,
        });
        let response = self
            .link
            .request(command, LINK_TIMEOUT)
            .await
            .map_err(|error| LspError::Unreachable {
                reason: format!("{error:#}"),
            })?;
        let data = response.data.ok_or_else(|| LspError::Unreachable {
            reason: response
                .error
                .clone()
                .unwrap_or_else(|| "the supervisor answered without data".to_owned()),
        })?;
        if response.success {
            serde_json::from_value(data).map_err(|error| LspError::Unreachable {
                reason: format!("invalid LSP response: {error}"),
            })
        } else {
            Err(
                serde_json::from_value(data).map_err(|error| LspError::Unreachable {
                    reason: format!("invalid LSP error: {error}"),
                })?,
            )
        }
    }
}

#[cfg(test)]
mod tests;
