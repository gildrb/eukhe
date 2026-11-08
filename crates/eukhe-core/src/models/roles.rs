//! The model of every role (`eukhe_types::model_roles::ModelRole`): the
//! role's own setting, else the all-roles model `modelRoles.all` (every
//! role but speech and dictation), else the role's default (`Default`;
//! the consumer's own chain: chat the startup chain, memory
//! `auxiliaryModel` then the session model, main's worker the parent's
//! model, …). The compiled core
//! decides the source (`bend/model_roles.bend`); this module gathers the
//! settings and reads the selector of the source it picked. Nothing here
//! writes settings.

use eukhe_bend::rules::model_roles::role_sources;
use eukhe_bend::{expect_core, Entry};
use eukhe_types::model_roles::ModelRole;

use crate::settings::cvar::{table, Cvars, Decl};

pub use eukhe_bend::rules::model_roles::RoleSource;

#[cfg(test)]
mod tests;

/// Where one role's model comes from, and its selector.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RoleModel {
    pub role: ModelRole,
    pub source: RoleSource,
    /// `Own`: the role's own setting; `All`: `modelRoles.all`; `Default`:
    /// `None` (the consumer's default chain).
    pub selector: Option<String>,
}

impl RoleModel {
    /// The selector as `(provider, model id)`, split at the first `/` (a
    /// provider name has none; a model id may). A selector without `/`
    /// names no provider: `("", selector)`, which no catalog model has.
    #[must_use]
    pub fn provider_model(&self) -> Option<(&str, &str)> {
        self.selector
            .as_deref()
            .map(|selector| selector.split_once('/').unwrap_or(("", selector)))
    }
}

/// The setting of `role`'s own model; `None` for the chat, whose own
/// model is two settings (`defaultProvider`/`defaultModel`).
#[must_use]
pub fn own_decl(role: ModelRole) -> Option<&'static Decl> {
    match role {
        ModelRole::Chat => None,
        ModelRole::Memory => Some(&table::MEMORY_MODEL),
        ModelRole::Auxiliary => Some(&table::AUXILIARY_MODEL),
        ModelRole::Image => Some(&table::IMAGE_MODEL),
        ModelRole::Subagent => Some(&table::SUBAGENT_DEFAULT_MODEL),
        ModelRole::Worker => Some(&table::WORKER_MODEL),
        ModelRole::Gateway => Some(&table::GATEWAY_SIGNAL_MODEL),
        ModelRole::Query => Some(&table::RLM_QUERY_MODEL),
        ModelRole::Titles => Some(&table::MODEL_ROLE_TINY),
        ModelRole::Judge => Some(&table::MODEL_ROLE_JUDGE),
        ModelRole::Translate => Some(&table::MODEL_ROLE_TRANSLATE),
        ModelRole::Speech => Some(&table::MODEL_ROLE_SPEECH),
        ModelRole::Dictation => Some(&table::MODEL_ROLE_DICTATION),
    }
}

/// The role's own setting (trimmed; `None` when blank). Chat:
/// `defaultProvider/defaultModel`, set when both are.
fn own_selector(cvars: &Cvars, role: ModelRole) -> Option<String> {
    if let Some(decl) = own_decl(role) {
        return cvars.optional_text(decl);
    }
    let provider = cvars.optional_text(&table::DEFAULT_PROVIDER)?;
    let model = cvars.optional_text(&table::DEFAULT_MODEL)?;
    Some(format!("{provider}/{model}"))
}

/// The roles the all-roles model reaches: those the compiled core's
/// table fills from it when no role has its own setting (every role that
/// takes a chat model; never speech or dictation). `/model --all` clears
/// their own settings (`laws/model_roles.bend` `all_switch_runs_n`,
/// `all_switch_keeps_others`).
#[must_use]
pub fn all_roles_reach() -> Vec<ModelRole> {
    expect_core(Entry::ModelRoles, role_sources(|_| false, true))
        .into_iter()
        .filter_map(|(role, source)| match source {
            RoleSource::All => Some(role),
            RoleSource::Own | RoleSource::Default => None,
        })
        .collect()
}

/// Every role's model source, in `ModelRole::ALL` order (the compiled
/// core decides; a failure there is an inconsistent build).
#[must_use]
pub fn role_table(cvars: &Cvars) -> Vec<RoleModel> {
    let owns = ModelRole::ALL.map(|role| (role, own_selector(cvars, role)));
    let all = cvars.optional_text(&table::MODEL_ROLE_ALL);
    let sources = expect_core(
        Entry::ModelRoles,
        role_sources(
            |role| {
                owns.iter()
                    .any(|(owner, own)| *owner == role && own.is_some())
            },
            all.is_some(),
        ),
    );
    // The core answers one row per role in `ModelRole::ALL` order (the
    // wrapper's decoder checks it), so the rows pair with `owns`.
    owns.into_iter()
        .zip(sources)
        .map(|((role, own), (_, source))| RoleModel {
            role,
            source,
            selector: match source {
                RoleSource::Own => own,
                RoleSource::All => all.clone(),
                RoleSource::Default => None,
            },
        })
        .collect()
}

/// The model source of `role` ([`role_table`]'s row).
///
/// # Panics
///
/// Never: the table holds every role.
#[must_use]
pub fn role_model(cvars: &Cvars, role: ModelRole) -> RoleModel {
    role_table(cvars)
        .into_iter()
        .find(|row| row.role == role)
        .expect("the role table holds every role")
}

/// A role the all-roles model does not run after `/model --all`: a
/// setting the global write does not clear (a project's) still names
/// another model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AllRolesOverride {
    pub role: ModelRole,
    /// The model the role runs on.
    pub selector: String,
    /// The setting that names it.
    pub setting: &'static str,
    /// The file that sets it.
    pub file: String,
}

/// The roles the all-roles model reaches ([`all_roles_reach`]) that do
/// not run on `selector` in `settings`, in role order, with the setting
/// and the file that names their model.
#[must_use]
pub fn all_roles_overrides(
    settings: &crate::settings::SettingsManager,
    selector: &str,
) -> Vec<AllRolesOverride> {
    let reach = all_roles_reach();
    role_table(settings.cvars())
        .into_iter()
        .filter(|row| reach.contains(&row.role))
        .filter_map(|row| {
            let runs = row.selector.filter(|runs| runs != selector)?;
            let decl = match row.source {
                RoleSource::Own => own_decl(row.role).unwrap_or(&table::DEFAULT_MODEL),
                RoleSource::All => &table::MODEL_ROLE_ALL,
                RoleSource::Default => return None,
            };
            Some(AllRolesOverride {
                role: row.role,
                selector: runs,
                setting: decl.id,
                file: settings.config_file(decl)?,
            })
        })
        .collect()
}
