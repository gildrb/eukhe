//! The extension registry of an eukhe session, installed in prompt order:
//! `eukhe.prompt`, `eukhe.settings`, `eukhe.undo` (a top-level session
//! with durable storage), `eukhe.rlm`,
//! `eukhe.compaction`, `eukhe.retry_outcome`, `eukhe.optchat`,
//! `eukhe.acceptance`, `eukhe.goals`, `eukhe.children`, `eukhe.workflow`, `eukhe.documents`, `eukhe.shell`,
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
//! worker tool. A help leaf of the agent tree offers that roster too, so
//! it holds only the read-only tools: it writes nothing.

use std::sync::Arc;

use eukhe_bend::rules::runners::{self, ChatMemory};
use eukhe_durable::harness::registry::{create_registry, Registry};
use eukhe_durable::harness::types::{Extension, ToolRegistration};
use eukhe_durable::session::SessionResult;
use eukhe_types::daemon::agent_tree::TreeRole;

use super::deps::{HostDeps, SessionShape};
use super::{
    acceptance, budget, children, codemode, compaction, directors, documents, goals, optchat,
    prompt, retry_outcome, rlm, settings, shell, tool_contract, tool_surface, workflow,
};

/// A registry with every eukhe extension of the session installed and its
/// roster fixed.
///
/// # Errors
///
/// An extension fails to install (duplicate names).
pub fn create_eukhe_registry(deps: &Arc<HostDeps>) -> SessionResult<Registry> {
    let registry = create_registry();
    // Main and a help leaf offer only the tools of main's roster (a help
    // leaf installs no worker tool, so it keeps the read-only ones); any
    // other session offers every tool its extensions bring.
    let help_leaf = deps
        .role
        .tree
        .as_ref()
        .is_some_and(|place| place.role == TreeRole::Help);
    let offered: Option<Vec<String>> = match (deps.shape, help_leaf) {
        (SessionShape::Single, false) => None,
        (SessionShape::Single, true) => Some(
            runners::main_roster(ChatMemory::Off)
                .into_iter()
                .map(|tool| tool.name)
                .collect(),
        ),
        (SessionShape::Main, _) => {
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
    // A top-level session's turn snapshots start at the first request
    // preparation and hold its tools until taken.
    if let Some(snapshots) = &deps.turn_snapshots {
        install(crate::undo::extension(deps, snapshots))?;
    }
    install(rlm::extension(deps))?;
    install(compaction::extension(deps))?;
    install(retry_outcome::extension(deps))?;
    install(optchat::extension(deps))?;
    // The loop decides a final answer before the acceptance verifier and
    // the goal do: while a loop runs, its next iteration owns the boundary.
    install(super::loop_mode::extension(deps))?;
    install(acceptance::extension(deps))?;
    install(goals::extension(deps))?;
    // After the Director stack's step: the work-left Director decides only
    // a final answer the stack did not continue.
    install(directors::work_left_extension(deps))?;
    install(children::extension(deps))?;
    // After a paused child run's wait: the notices due are written just
    // before the request reads its context.
    install(budget::extension(deps))?;
    install(workflow::extension(deps))?;
    install(documents::extension(deps))?;
    install(shell::extension(deps))?;
    install(tool_surface::extension(deps))?;
    install(codemode::extension(deps))?;
    install(closing_extension)?;
    // A root numbers its runs and reports each run's end; every session
    // records the MCP calls its kernel makes.
    super::ran_effects::install(deps);
    super::ran_effects::register_host_requests(deps);
    registry.fix_roster();
    Ok(registry)
}
