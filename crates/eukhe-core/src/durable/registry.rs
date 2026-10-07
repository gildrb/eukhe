//! The extension registry of an eukhe session, installed in prompt order:
//! `eukhe.prompt`, `eukhe.rlm`, `eukhe.optchat`, `eukhe.goals`,
//! `eukhe.children`.

use std::sync::Arc;

use eukhe_durable::harness::registry::{create_registry, Registry};
use eukhe_durable::session::SessionResult;

use super::deps::HostDeps;
use super::{children, goals, optchat, prompt, rlm};

/// A registry with every eukhe extension of the session installed.
///
/// # Errors
///
/// An extension fails to install (duplicate names).
pub fn create_eukhe_registry(deps: &Arc<HostDeps>) -> SessionResult<Registry> {
    let registry = create_registry();
    registry.install(prompt::extension(deps))?;
    registry.install(rlm::extension(deps))?;
    if let Some(extension) = optchat::extension(deps) {
        registry.install(extension)?;
    }
    registry.install(goals::extension(deps))?;
    registry.install(children::extension(deps))?;
    Ok(registry)
}
