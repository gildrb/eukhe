//! `eukhe.documents`: the session's documents (`eukhe_docs::Documents`,
//! one edit store per session) behind the kernel's `fs.*` host requests.

mod requests;

use std::sync::Arc;

use eukhe_docs::Documents;
use eukhe_durable::harness::define::define_extension;
use eukhe_durable::harness::types::Extension;

use super::HostDeps;

/// The extension's name.
pub const DOCUMENTS_EXTENSION: &str = "eukhe.documents";

/// The documents extension of one session. Path locks live under
/// `<agent dir>/locks`, shared by every session of the eukhe home.
#[must_use]
pub fn extension(deps: &Arc<HostDeps>) -> Arc<Extension> {
    let documents = Arc::new(Documents::new(
        deps.agent_dir.join("locks"),
        eukhe_types::platform::home_dir(),
    ));
    requests::register(&deps.host_requests, &documents);
    define_extension(Extension::named(DOCUMENTS_EXTENSION))
}
