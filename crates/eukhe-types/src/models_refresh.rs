//! The report of a model-list refresh (`eukhe model refresh`, the daemon's
//! `refresh_models`): per provider, the models its listing added to the
//! local overlay, or why it was skipped or failed.

use serde::{Deserialize, Serialize};

/// One refresh: when it ran (UTC ISO 8601) and each provider's outcome,
/// in provider order.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ModelsRefreshReport {
    pub refreshed_at: String,
    pub providers: Vec<ProviderRefresh>,
}

/// One provider's outcome.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ProviderRefresh {
    pub provider: String,
    #[serde(flatten)]
    pub outcome: RefreshOutcome,
}

/// What a provider's refresh came to.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "snake_case")]
pub enum RefreshOutcome {
    /// The listing answered: the models it added (the built-in catalog
    /// lacks them) and how many listed models the catalog has.
    Refreshed {
        added: Vec<AddedModel>,
        known: usize,
    },
    /// Nothing was asked.
    Skipped { reason: SkipReason },
    /// The listing request failed.
    Failed { error: String },
}

/// A model a listing added.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AddedModel {
    pub id: String,
    pub name: String,
}

/// Why a provider was not asked.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SkipReason {
    /// The provider has no model-listing endpoint.
    NoListingEndpoint,
    /// A named provider has no credentials.
    NotSignedIn,
    /// No model of the catalog names a named provider.
    NotInCatalog,
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    #[test]
    fn the_report_reads_back_from_its_json() {
        let report = ModelsRefreshReport {
            refreshed_at: "2026-11-14T10:00:00.000Z".to_owned(),
            providers: vec![
                ProviderRefresh {
                    provider: "openai-codex".to_owned(),
                    outcome: RefreshOutcome::Refreshed {
                        added: vec![AddedModel {
                            id: "gpt-6.2".to_owned(),
                            name: "GPT-6.2".to_owned(),
                        }],
                        known: 3,
                    },
                },
                ProviderRefresh {
                    provider: "xai".to_owned(),
                    outcome: RefreshOutcome::Skipped {
                        reason: SkipReason::NoListingEndpoint,
                    },
                },
            ],
        };
        let value = serde_json::to_value(&report).expect("json");
        assert_eq!(
            (
                value.clone(),
                serde_json::from_value::<ModelsRefreshReport>(value).expect("report")
            ),
            (
                json!({
                    "refreshedAt": "2026-11-14T10:00:00.000Z",
                    "providers": [
                        {
                            "provider": "openai-codex",
                            "status": "refreshed",
                            "added": [{ "id": "gpt-6.2", "name": "GPT-6.2" }],
                            "known": 3
                        },
                        { "provider": "xai", "status": "skipped", "reason": "no_listing_endpoint" }
                    ]
                }),
                report
            )
        );
    }
}
