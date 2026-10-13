//! Language servers for eukhe sessions: the server table (data), root-marker
//! discovery, a JSON-RPC client over stdio, the pool of started servers
//! keyed by (server, workspace root, configuration fingerprint) with crash
//! backoff, document synchronization, diagnostics with an inline window and
//! a late window, navigation, rename, and code actions.
//!
//! Servers are local executables only (a project's `node_modules/.bin`, then
//! `PATH`); nothing is downloaded. Nothing starts until a request needs it.
//!
//! A session reaches language servers through an [`LspHandle`]: the daemon
//! worker's handle asks the supervisor's shared [`LspService`]; a session
//! without a daemon runs a private [`LspService`] in-process.

mod client;
mod diagnostics;
mod edits;
mod pool;
mod position;
mod protocol;
mod rpc;
mod servers;
mod service;

use std::future::Future;
use std::pin::Pin;
use std::sync::Arc;

use eukhe_types::lsp::{LspError, LspRequest, LspResponse};

pub use diagnostics::DiagnosticsLedger;
pub use edits::{apply_text_edits, EditError};
pub use servers::ServerTable;
pub use service::{read_text, LspService, INLINE_DIAGNOSTICS_WAIT, LATE_DIAGNOSTICS_WAIT};

/// The authority a session's LSP requests go to.
///
/// Implementations answer each [`LspRequest`] with the matching
/// [`LspResponse`] variant (see [`eukhe_types::lsp::LspOp`]) or a typed
/// [`LspError`]; they never start servers except to answer a request. The
/// daemon worker implements it over its supervisor link; [`LspService`] is
/// the in-process authority.
pub trait LspHost: Send + Sync {
    /// Answer one request.
    fn call(
        &self,
        request: LspRequest,
    ) -> impl Future<Output = Result<LspResponse, LspError>> + Send;
}

impl LspHost for LspService {
    async fn call(&self, request: LspRequest) -> Result<LspResponse, LspError> {
        LspService::call(self, request).await
    }
}

type CallFuture = Pin<Box<dyn Future<Output = Result<LspResponse, LspError>> + Send>>;

/// An [`LspHost`] as a session takes it (type-erased).
#[derive(Clone)]
pub struct LspHandle {
    call: Arc<dyn Fn(LspRequest) -> CallFuture + Send + Sync>,
}

impl LspHandle {
    #[must_use]
    pub fn new<H: LspHost + 'static>(host: Arc<H>) -> Self {
        Self {
            call: Arc::new(move |request| {
                let host = Arc::clone(&host);
                Box::pin(async move { host.call(request).await })
            }),
        }
    }

    /// See [`LspHost::call`].
    #[must_use]
    pub fn call(&self, request: LspRequest) -> CallFuture {
        (self.call)(request)
    }
}
