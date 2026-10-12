//! `eukhe.documents`: the session's documents (`eukhe_docs::Documents`,
//! one edit store per session) behind the kernel's `fs.*` host requests and
//! the wire `edit` tool. Both entry points share the store, so a `read()` in
//! the kernel makes its lines anchorable for the tool.

mod requests;
mod tool;

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_docs::Documents;
use eukhe_durable::harness::define::define_extension;
use eukhe_durable::harness::types::Extension;
use eukhe_durable::types::{ConversationId, ROOT_CONVERSATION_ID};

use super::{HostCall, HostDeps};

pub use tool::EDIT_TOOL_NAME;

/// The extension's name.
pub const DOCUMENTS_EXTENSION: &str = "eukhe.documents";

/// What the requests and the tool share.
pub(crate) struct DocumentsHost {
    documents: Documents,
    /// The kernel cwd each conversation's last `fs.*` request came from.
    kernel_cwds: Mutex<HashMap<ConversationId, PathBuf>>,
}

impl DocumentsHost {
    fn remember_cwd(&self, call: &HostCall, cwd: PathBuf) {
        let conversation = call
            .call
            .as_ref()
            .map_or(ROOT_CONVERSATION_ID, |api| api.conversation_id());
        self.kernel_cwds
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .insert(conversation, cwd);
    }

    fn kernel_cwd(&self, conversation: ConversationId) -> Option<PathBuf> {
        self.kernel_cwds
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .get(&conversation)
            .cloned()
    }
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
        kernel_cwds: Mutex::new(HashMap::new()),
    });
    requests::register(&deps.host_requests, &host);
    define_extension(Extension {
        tools: vec![tool::edit_tool(&host, deps)],
        ..Extension::named(DOCUMENTS_EXTENSION)
    })
}
