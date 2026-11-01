//! The model of every role (`eukhe_types::model_roles::ModelRole`): the
//! role's own setting, else the all-roles model `modelRoles.all` (every
//! role but speech and dictation), else the role's default (`Default`;
//! the consumer's own chain: chat the startup chain, memory
//! `auxiliaryModel` then the session model, …). The compiled core
//! decides the source (`bend/model_roles.bend`); this module gathers the
//! settings and reads the selector of the source it picked. Nothing here
//! writes settings.

use eukhe_bend::rules::model_roles::role_sources;
use eukhe_bend::{expect_core, Entry};
use eukhe_types::model_roles::ModelRole;

use crate::settings::cvar::{table, Cvars};

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

/// The role's own setting (trimmed; `None` when blank). Chat:
/// `defaultProvider/defaultModel`, set when both are.
fn own_selector(cvars: &Cvars, role: ModelRole) -> Option<String> {
    let decl = match role {
        ModelRole::Chat => {
            let provider = cvars.optional_text(&table::DEFAULT_PROVIDER)?;
            let model = cvars.optional_text(&table::DEFAULT_MODEL)?;
            return Some(format!("{provider}/{model}"));
        }
        ModelRole::Memory => &table::MEMORY_MODEL,
        ModelRole::Auxiliary => &table::AUXILIARY_MODEL,
        ModelRole::Image => &table::IMAGE_MODEL,
        ModelRole::Subagent => &table::SUBAGENT_DEFAULT_MODEL,
        ModelRole::Gateway => &table::GATEWAY_SIGNAL_MODEL,
        ModelRole::Query => &table::RLM_QUERY_MODEL,
        ModelRole::Titles => &table::MODEL_ROLE_TINY,
        ModelRole::Judge => &table::MODEL_ROLE_JUDGE,
        ModelRole::Translate => &table::MODEL_ROLE_TRANSLATE,
        ModelRole::Speech => &table::MODEL_ROLE_SPEECH,
        ModelRole::Dictation => &table::MODEL_ROLE_DICTATION,
    };
    cvars.optional_text(decl)
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
