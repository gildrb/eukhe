//! The extension registry of an eukhe session, installed in prompt order:
//! `eukhe.prompt`, `eukhe.settings`, `eukhe.rlm`, `eukhe.digest`,
//! `eukhe.compaction`, `eukhe.retry_outcome`, `eukhe.optchat`,
//! `eukhe.goals`, `eukhe.children`, `eukhe.workflow`, `eukhe.documents`, `eukhe.shell`,
//! `eukhe.dyn`, `codemode`. Every tool
//! schema is built with the intent `i` and a version
//! (`tool_contract::build`), and the roster is fixed once every extension
//! is installed : a tool that comes later goes behind
//! `dyn`.

use std::sync::Arc;

use eukhe_durable::harness::registry::{create_registry, Registry};
use eukhe_durable::harness::types::{Extension, ToolRegistration};
use eukhe_durable::session::SessionResult;

use super::deps::HostDeps;
use super::{
    children, codemode, compaction, digest, documents, goals, optchat, prompt, retry_outcome, rlm,
    settings, shell, tool_contract, tool_surface, workflow,
};

/// A registry with every eukhe extension of the session installed and its
/// roster fixed.
///
/// # Errors
///
/// An extension fails to install (duplicate names).
pub fn create_eukhe_registry(deps: &Arc<HostDeps>) -> SessionResult<Registry> {
    let registry = create_registry();
    let install = |extension: Arc<Extension>| {
        let tools = extension
            .tools
            .iter()
            .map(|tool| {
                Arc::new(ToolRegistration {
                    parameters: tool_contract::build(&tool.parameters),
                    ..(**tool).clone()
                })
            })
            .collect();
        registry.install(Arc::new(Extension {
            tools,
            ..(*extension).clone()
        }))
    };
    install(prompt::extension(deps))?;
    install(settings::extension(deps))?;
    install(rlm::extension(deps))?;
    install(digest::extension(deps))?;
    install(compaction::extension(deps))?;
    install(retry_outcome::extension(deps))?;
    if let Some(extension) = optchat::extension(deps) {
        install(extension)?;
    }
    install(goals::extension(deps))?;
    install(children::extension(deps))?;
    install(workflow::extension(deps))?;
    install(documents::extension(deps))?;
    install(shell::extension(deps))?;
    install(tool_surface::extension(deps))?;
    install(codemode::extension(deps))?;
    registry.fix_roster();
    Ok(registry)
}
