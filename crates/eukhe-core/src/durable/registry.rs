//! The extension registry of an eukhe session, installed in prompt order:
//! `eukhe.prompt`, `eukhe.settings`, `eukhe.rlm`,
//! `eukhe.compaction`, `eukhe.retry_outcome`, `eukhe.optchat`,
//! `eukhe.goals`, `eukhe.children`, `eukhe.workflow`, `eukhe.documents`, `eukhe.shell`,
//! `eukhe.dyn`, `codemode`, and last `eukhe.closing`, whose `<critical>`
//! block ends the system prompt. Every tool
//! schema is built with the intent `i` and a version
//! (`tool_contract::build`), and the roster is fixed once every extension
//! is installed: a tool that comes later goes behind `dyn`. Every tool's
//! `execute` runs behind the session's budget gate
//! (`budget::BudgetGate::wrap_tool`). Main (a root
//! in the `main-worker` shape, [`SessionShape::Main`]) offers only the
//! compiled core's main roster (`eukhe_bend::rules::runners::main_roster`):
//! read-only tools and the worker tools; every other session offers no
//! worker tool.

use std::sync::Arc;

use eukhe_bend::rules::runners::{self, ChatMemory};
use eukhe_durable::harness::registry::{create_registry, Registry};
use eukhe_durable::harness::types::{Extension, ToolRegistration};
use eukhe_durable::session::SessionResult;

use super::deps::{HostDeps, SessionShape};
use super::{
    children, codemode, compaction, documents, goals, optchat, prompt, retry_outcome, rlm,
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
    // Main offers only the tools of its roster; any other session offers
    // every tool its extensions bring.
    let offered: Option<Vec<String>> = match deps.shape {
        SessionShape::Single => None,
        SessionShape::Main => {
            // `eukhe.optchat` installs in every session; main's roster
            // takes its tools when main has chat memory.
            let chat = if deps.memory.is_some() {
                ChatMemory::On
            } else {
                ChatMemory::Off
            };
            Some(
                runners::main_roster(chat)
                    .into_iter()
                    .map(|tool| tool.name)
                    .collect(),
            )
        }
    };
    let install = |extension: Arc<Extension>| {
        let tools = extension
            .tools
            .iter()
            .filter(|tool| {
                offered
                    .as_ref()
                    .is_none_or(|names| names.contains(&tool.name))
            })
            .map(|tool| {
                Arc::new(ToolRegistration {
                    parameters: tool_contract::build(&tool.parameters),
                    // Every tool call passes the session's budget.
                    execute: deps.budget.wrap_tool(&tool.name, Arc::clone(&tool.execute)),
                    ..(**tool).clone()
                })
            })
            .collect();
        registry.install(Arc::new(Extension {
            tools,
            ..(*extension).clone()
        }))
    };
    let [prompt_extension, closing_extension] = prompt::extensions(deps);
    install(prompt_extension)?;
    install(settings::extension(deps))?;
    install(rlm::extension(deps))?;
    install(compaction::extension(deps))?;
    install(retry_outcome::extension(deps))?;
    install(optchat::extension(deps))?;
    // The loop decides a final answer before the goal does.
    install(super::loop_mode::extension(deps))?;
    install(goals::extension(deps))?;
    install(children::extension(deps))?;
    install(workflow::extension(deps))?;
    install(documents::extension(deps))?;
    install(shell::extension(deps))?;
    install(tool_surface::extension(deps))?;
    install(codemode::extension(deps))?;
    install(closing_extension)?;
    registry.fix_roster();
    Ok(registry)
}
