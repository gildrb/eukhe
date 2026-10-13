//! `eukhe.documents`: the session's documents (`eukhe_docs::Documents`,
//! one edit store per session) behind the wire `read`, `edit`, `grep`, and
//! `glob` tools and the kernel's `fs.*` host requests. Both entry points
//! decode through one contract per function and share the store, so a
//! `read()` in the kernel makes its lines anchorable for the `edit` tool and
//! the other way round.

mod contract;
mod requests;
mod tool;

use std::sync::Arc;

use eukhe_docs::Documents;
use eukhe_durable::harness::define::define_extension;
use eukhe_durable::harness::types::Extension;

use self::contract::Function;
use super::HostDeps;

/// The extension's name.
pub const DOCUMENTS_EXTENSION: &str = "eukhe.documents";

/// The wire `edit` tool's name.
pub const EDIT_TOOL_NAME: &str = Function::Edit.name();

/// What the requests and the tools share.
pub(crate) struct DocumentsHost {
    documents: Documents,
}

/// The documents extension of one session. Path locks live under
/// `<agent dir>/locks`, shared by every session of the eukhe home.
#[must_use]
pub fn extension(deps: &Arc<HostDeps>) -> Arc<Extension> {
    let host = Arc::new(DocumentsHost {
        documents: Documents::new(
            deps.agent_dir.join("locks"),
            eukhe_types::platform::home_dir(),
        ),
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
