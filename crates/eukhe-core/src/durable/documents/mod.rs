//! `eukhe.documents`: the session's documents (`eukhe_docs::Documents`,
//! one edit store per session) behind the wire `read`, `edit`, `grep`, and
//! `glob` tools and the kernel's `fs.*` host requests. Both entry points
//! decode through one contract per function and share the store, so a
//! `read()` in the kernel makes its lines anchorable for the `edit` tool and
//! the other way round. `read` also serves the internal URLs (`urls`), and
//! `ssh://` through the user's own `ssh` program (`ssh`).

mod contract;
mod requests;
mod ssh;
mod tool;
mod urls;

use std::path::PathBuf;
use std::sync::{Arc, Weak};

use eukhe_docs::Documents;
use eukhe_durable::harness::define::define_extension;
use eukhe_durable::harness::types::Extension;

use self::contract::Function;
use super::HostDeps;
use crate::memory::Memory;
use crate::resources::LoadedResources;

/// The extension's name.
pub const DOCUMENTS_EXTENSION: &str = "eukhe.documents";

/// The wire `edit` tool's name.
pub const EDIT_TOOL_NAME: &str = Function::Edit.name();

/// What the requests and the tools share.
pub(crate) struct DocumentsHost {
    documents: Documents,
    /// The root of `repo://`: the session's working directory.
    workspace: PathBuf,
    /// The skills `skill://` serves.
    resources: Arc<LoadedResources>,
    /// The chat memory `memory://` serves; `None` without one.
    memory: Option<Memory>,
    /// The session (its MCP servers and kernels) `mcp://` reads through;
    /// weak: the session's host requests own this host.
    deps: Weak<HostDeps>,
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
        workspace: deps.cwd.clone(),
        resources: Arc::clone(&deps.resources),
        memory: deps.memory.clone(),
        deps: Arc::downgrade(deps),
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
