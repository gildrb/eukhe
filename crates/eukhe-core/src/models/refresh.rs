//! The explicit model-list refresh (`eukhe model refresh`, the daemon's
//! `refresh_models`): each selected provider's own listing endpoint is
//! asked for the models it offers now; the chat models the built-in
//! catalog lacks and every id the listing named land in the overlay
//! `<agent_dir>/models-refresh.json` (`eukhe_models::overlay`), which every
//! catalog build reads beside the built-in catalog (the registry's
//! `compose`, the session collection) and `eukhe model list` reads to mark
//! the models the account is not offered.
//! Only the commands call [`refresh_models`]; nothing refreshes on its own.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use eukhe_ai::capabilities::{Capability, Support};
use eukhe_ai::models::{Models, ModelsCapabilityOptions};
use eukhe_models::overlay::{
    overlay_models, provider_listing, with_provider_listing, ProviderListing, RefreshOverlay,
};
use eukhe_types::ai::Model;
use eukhe_types::models_refresh::{
    AddedModel, ModelsRefreshReport, ProviderRefresh, RefreshOutcome, SkipReason,
};

use crate::auth::AuthStorage;
use crate::models::ModelRegistry;
use crate::settings::storage::{atomic_write_with, AtomicWriteOptions};

/// The overlay's file name in the agent dir.
pub const OVERLAY_FILE_NAME: &str = "models-refresh.json";

/// Which providers a refresh asks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProviderSelection {
    /// Every provider with credentials.
    SignedIn,
    /// These providers, in this order.
    Named(Vec<String>),
}

/// A finished refresh: its report and every model of the overlay the
/// built-in catalog lacks (what a running session joins).
#[derive(Debug, Clone, PartialEq)]
pub struct Refreshed {
    pub report: ModelsRefreshReport,
    pub models: Vec<Model>,
}

fn overlay_path(agent_dir: &Path) -> PathBuf {
    agent_dir.join(OVERLAY_FILE_NAME)
}

/// The overlay of `agent_dir`; empty when the file is missing. A file that
/// does not read is logged and counts as empty (the next refresh rewrites
/// it).
#[must_use]
pub fn load_overlay(agent_dir: &Path) -> RefreshOverlay {
    let path = overlay_path(agent_dir);
    let text = match std::fs::read_to_string(&path) {
        Ok(text) => text,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            return RefreshOverlay::default();
        }
        Err(error) => {
            tracing::warn!("{} does not read: {error}", path.display());
            return RefreshOverlay::default();
        }
    };
    serde_json::from_str(&text).unwrap_or_else(|error| {
        tracing::warn!("{} does not parse: {error}", path.display());
        RefreshOverlay::default()
    })
}

/// The overlay models of `agent_dir` that `pinned` (the built-in catalog)
/// lacks.
#[must_use]
pub fn overlay_catalog_models(agent_dir: &Path, pinned: &[Model]) -> Vec<Model> {
    overlay_models(pinned, &load_overlay(agent_dir))
}

/// Write `overlay` atomically (temp file and rename, synced).
fn save_overlay(agent_dir: &Path, overlay: &RefreshOverlay) -> anyhow::Result<()> {
    let text = serde_json::to_string_pretty(overlay)?;
    atomic_write_with(
        &overlay_path(agent_dir),
        &format!("{text}\n"),
        AtomicWriteOptions { fsync: true },
    )
}

/// The providers a refresh considers, with whether each has credentials:
/// every provider with credentials, sorted, or the named ones in order
/// (each once).
fn selected_providers(
    registry: &ModelRegistry,
    selection: &ProviderSelection,
) -> Vec<(String, Credentials)> {
    let signed_in: BTreeSet<&str> = registry
        .get_available()
        .into_iter()
        .map(|model| model.provider.as_str())
        .collect();
    let known: BTreeSet<&str> = registry
        .get_all()
        .map(|model| model.provider.as_str())
        .collect();
    match selection {
        ProviderSelection::SignedIn => signed_in
            .iter()
            .map(|provider| ((*provider).to_owned(), Credentials::Present))
            .collect(),
        ProviderSelection::Named(names) => {
            let mut seen = BTreeSet::new();
            names
                .iter()
                .filter(|name| seen.insert(name.as_str()))
                .map(|name| {
                    let credentials = if signed_in.contains(name.as_str()) {
                        Credentials::Present
                    } else if known.contains(name.as_str()) {
                        Credentials::Missing
                    } else {
                        Credentials::UnknownProvider
                    };
                    (name.clone(), credentials)
                })
                .collect()
        }
    }
}

/// Whether a provider can be asked.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Credentials {
    Present,
    Missing,
    /// No model of the catalog names the provider.
    UnknownProvider,
}

/// What asking one provider came to, before it is reported.
enum Asked {
    Listing(Option<ProviderListing>),
    Skipped(SkipReason),
    Failed(String),
}

/// Ask `provider`'s listing endpoint through its first chat model that has
/// one.
async fn ask_provider(
    models: &Models,
    pinned: &[Model],
    provider: &str,
    credentials: Credentials,
) -> Asked {
    match credentials {
        Credentials::Present => {}
        Credentials::Missing => return Asked::Skipped(SkipReason::NotSignedIn),
        Credentials::UnknownProvider => return Asked::Skipped(SkipReason::NotInCatalog),
    }
    let Some(model) = models.get_models(Some(provider)).into_iter().find(|model| {
        matches!(
            models.capabilities(model).support(Capability::ListModels),
            Support::Native { .. }
        )
    }) else {
        return Asked::Skipped(SkipReason::NoListingEndpoint);
    };
    match models
        .list_models(&model, ModelsCapabilityOptions::default())
        .await
    {
        Ok(listed) => Asked::Listing(provider_listing(pinned, provider, &listed)),
        Err(error) => Asked::Failed(
            error
                .to_string()
                .split_whitespace()
                .collect::<Vec<_>>()
                .join(" "),
        ),
    }
}

/// The report row of one asked provider.
fn outcome(asked: &Asked) -> RefreshOutcome {
    match asked {
        Asked::Listing(listing) => RefreshOutcome::Refreshed {
            added: listing
                .iter()
                .flat_map(|listing| &listing.added)
                .map(|model| AddedModel {
                    id: model.id.clone(),
                    name: model.name.clone(),
                })
                .collect(),
            known: listing.as_ref().map_or(0, |listing| listing.known),
        },
        Asked::Skipped(reason) => RefreshOutcome::Skipped { reason: *reason },
        Asked::Failed(error) => RefreshOutcome::Failed {
            error: error.clone(),
        },
    }
}

/// The UTC ISO 8601 form of `instant`.
fn iso(instant: SystemTime) -> String {
    let millis = instant.duration_since(UNIX_EPOCH).map_or(0, |duration| {
        i64::try_from(duration.as_millis()).unwrap_or(i64::MAX)
    });
    crate::session::manager::format_iso(millis)
}

/// Refresh the selected providers' model lists into `agent_dir`'s
/// overlay, asking through `models` (credentials resolve like a chat
/// request); `now` dates the refresh. Providers are asked at once; one
/// failing never stops the others. A provider whose listing answered
/// replaces its overlay models; the others keep theirs.
///
/// # Errors
///
/// The overlay does not write.
pub async fn refresh_models(
    agent_dir: &Path,
    models: &Models,
    selection: &ProviderSelection,
    now: SystemTime,
) -> anyhow::Result<Refreshed> {
    let registry = ModelRegistry::create(
        AuthStorage::create(agent_dir),
        agent_dir.join("models.json"),
    );
    let pinned = ModelRegistry::built_in_catalog_models();
    let providers = selected_providers(&registry, selection);
    let asked = futures::future::join_all(
        providers
            .iter()
            .map(|(provider, credentials)| ask_provider(models, pinned, provider, *credentials)),
    )
    .await;
    let rows: Vec<ProviderRefresh> = providers
        .iter()
        .zip(&asked)
        .map(|((provider, _), asked)| ProviderRefresh {
            provider: provider.clone(),
            outcome: outcome(asked),
        })
        .collect();
    let refreshed_at = iso(now);
    let answered: Vec<(&str, Option<ProviderListing>)> = providers
        .iter()
        .zip(asked)
        .filter_map(|((provider, _), asked)| match asked {
            Asked::Listing(listing) => Some((provider.as_str(), listing)),
            Asked::Skipped(_) | Asked::Failed(_) => None,
        })
        .collect();
    let previous = load_overlay(agent_dir);
    let overlay = if answered.is_empty() {
        previous
    } else {
        let overlay = answered
            .into_iter()
            .fold(previous, |overlay, (provider, listing)| {
                with_provider_listing(overlay, provider, listing, &refreshed_at)
            });
        save_overlay(agent_dir, &overlay)?;
        overlay
    };
    Ok(Refreshed {
        report: ModelsRefreshReport {
            refreshed_at,
            providers: rows,
        },
        models: overlay_models(pinned, &overlay),
    })
}

/// The `HH:MM` local time of the UTC ISO instant `iso`; the instant as
/// given when it does not read.
#[must_use]
pub fn local_clock(iso: &str) -> String {
    crate::platform::local_time::parse_utc_iso(iso)
        .and_then(|instant| crate::platform::local_time::local_time(instant).ok())
        .map_or_else(
            || iso.to_owned(),
            |local| format!("{:02}:{:02}", local.hour, local.minute),
        )
}

/// The report as text lines: the time (`clock`), then per provider its
/// outcome and each added model.
#[must_use]
pub fn report_lines(report: &ModelsRefreshReport, clock: &str) -> Vec<String> {
    if report.providers.is_empty() {
        return vec!["No signed-in provider has a model-listing endpoint.".to_owned()];
    }
    let rows = report.providers.iter().flat_map(|row| {
        let provider = &row.provider;
        match &row.outcome {
            RefreshOutcome::Refreshed { added, known } => std::iter::once(format!(
                "{provider}: {} new, {known} already known",
                added.len()
            ))
            .chain(
                added
                    .iter()
                    .map(|model| format!("  {provider}/{}  {}", model.id, model.name)),
            )
            .collect::<Vec<_>>(),
            RefreshOutcome::Skipped { reason } => {
                let reason = match reason {
                    SkipReason::NoListingEndpoint => "no model-listing endpoint",
                    SkipReason::NotSignedIn => "not signed in",
                    SkipReason::NotInCatalog => "unknown provider",
                };
                vec![format!("{provider}: skipped: {reason}")]
            }
            RefreshOutcome::Failed { error } => vec![format!("{provider}: failed: {error}")],
        }
    });
    std::iter::once(format!("Model lists refreshed at {clock}"))
        .chain(rows)
        .collect()
}

#[cfg(test)]
#[path = "refresh_tests.rs"]
mod tests;
