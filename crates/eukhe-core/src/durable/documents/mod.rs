//! `eukhe.documents`: the session's documents (`eukhe_docs::Documents`,
//! one edit store per session) behind the wire `read`, `edit`, `grep`, and
//! `glob` tools and the kernel's `fs.*` host requests. Both entry points
//! decode through one contract per function and share the store, so a
//! `read()` in the kernel makes its lines anchorable for the `edit` tool and
//! the other way round. Every committed write reaches the session's
//! language servers, and its result carries their diagnostics.

mod contract;
mod requests;
mod tool;

use std::sync::Arc;

use eukhe_docs::Documents;
use eukhe_durable::harness::define::define_extension;
use eukhe_durable::harness::types::Extension;

use self::contract::Function;
use super::lsp::SessionLsp;
use super::HostDeps;

/// The extension's name.
pub const DOCUMENTS_EXTENSION: &str = "eukhe.documents";

/// The wire `edit` tool's name.
pub const EDIT_TOOL_NAME: &str = Function::Edit.name();

/// What the requests and the tools share.
pub(crate) struct DocumentsHost {
    documents: Documents,
    lsp: Arc<SessionLsp>,
}

/// The documents extension of one session, over the session's documents
/// ([`HostDeps::documents`]) and language servers.
#[must_use]
pub fn extension(deps: &Arc<HostDeps>) -> Arc<Extension> {
    let host = Arc::new(DocumentsHost {
        documents: deps.documents.clone(),
        lsp: Arc::clone(&deps.lsp),
    });
    requests::register(&deps.host_requests, &host);
    define_extension(Extension {
        tools: [
            Function::Read,
            Function::Edit,
            Function::Grep,
            Function::Glob,
        ]
        .into_iter()
        .map(|function| tool::document_tool(function, &host, deps))
        .collect(),
        ..Extension::named(DOCUMENTS_EXTENSION)
    })
}
