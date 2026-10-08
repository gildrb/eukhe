//! Provider failover on the durable path: the failover policy and the
//! candidate chain of the old engine's `session_engine/provider_failover.rs`
//! (the TS backup-model retry, `_handleBackupModelRetry`), over the pi-ai
//! catalog.
//!
//! The durable Harness already owns the per-provider quick retries (its
//! durable attempt loop with backoff, the old engine's quick-retry loop).
//! What it cannot do is move a turn to a sibling provider: when a whole
//! provider is down, every retry hits the same outage and the turn dies.
//! The provider runtime (see [`super::provider`]) wraps the provider stream
//! functions and adds exactly that move — after a retryable provider
//! failure, the request re-routes to the next configured provider serving
//! the same model id, immediately (the TS backup retry re-issues with
//! `delayMs: 0`), bounded by the old engine's whole-episode ceiling.

use eukhe_types::pi_ai::Model;

/// The provider-failover policy (settings `retry.failover`): whether a
/// provider outage may re-route to a sibling provider serving the same
/// model, and the whole-episode switch ceiling.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProviderFailoverPolicy {
    pub enabled: bool,
    /// Maximum switches to sibling providers per request (the old
    /// per-provider retry budget maps to the Harness's own durable retries;
    /// the switch budget is the old whole-episode ceiling).
    pub max_switches: u32,
}

/// Default policy: failover on, up to [`MAX_TOTAL_PROVIDER_RETRIES`]
/// provider attempts per request (the old engine's whole-episode ceiling —
/// the SANCTIONED DIVERGENCE of 2026-09-23: the per-provider budget alone
/// let a chain of N candidate providers stack 5xN retries into the ~30
/// attempts the operator ruled too many).
pub const DEFAULT_PROVIDER_FAILOVER_POLICY: ProviderFailoverPolicy = ProviderFailoverPolicy {
    enabled: true,
    max_switches: MAX_TOTAL_PROVIDER_RETRIES,
};

/// The whole-episode provider-attempt ceiling (the old
/// `MAX_TOTAL_PROVIDER_RETRIES`): a request walks at most this many provider
/// attempts (the primary plus switches) before the final failure surfaces.
pub const MAX_TOTAL_PROVIDER_RETRIES: u32 = 8;

/// The `"provider/model-id"` reference of a model (the wire's `backupModel`
/// and `restoredModel` vocabulary).
#[must_use]
pub fn model_reference(model: &Model) -> String {
    format!("{}/{}", model.provider, model.id)
}

/// Provider-failover candidates for `current`: the other auth-configured
/// providers serving the same model id, in catalog order starting after
/// `current`'s provider, one per provider (the old engine's
/// `failover_candidates`, ported verbatim over the pi-ai catalog).
///
/// Rotation keeps the chain stable for every starting provider: with
/// catalog order A, B, C the candidates for B are C then A.
#[must_use]
pub fn failover_candidates(current: &Model, available: &[Model]) -> Vec<Model> {
    // Same model id, other providers: first catalog entry wins per provider.
    let mut candidates: Vec<&Model> = Vec::new();
    for model in available
        .iter()
        .filter(|model| model.id == current.id && model.provider != current.provider)
    {
        if !candidates
            .iter()
            .any(|candidate| candidate.provider == model.provider)
        {
            candidates.push(model);
        }
    }
    // Rotate so the provider after `current` (by catalog position) leads:
    // with catalog order A, B, C the candidates for B are C then A.
    let current_position = available
        .iter()
        .position(|model| model.provider == current.provider);
    if let Some(position) = current_position {
        candidates.sort_by_key(|candidate| {
            let candidate_position = available
                .iter()
                .position(|model| model.provider == candidate.provider)
                .unwrap_or(usize::MAX);
            if candidate_position > position {
                candidate_position
            } else {
                candidate_position + available.len()
            }
        });
    }
    candidates.into_iter().cloned().collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use eukhe_types::pi_ai::{Modality, ModelCost};

    fn catalog_model(provider: &str, id: &str) -> Model {
        Model {
            id: id.to_owned(),
            name: format!("{provider} {id}"),
            api: "faux".to_owned(),
            provider: provider.to_owned(),
            base_url: String::new(),
            input: vec![Modality::Text],
            input_limits: None,
            cost: ModelCost::default(),
            headers: None,
            model_type: None,
            reasoning: false,
            thinking_level_map: None,
            prompt_cache: None,
            context_window: 100_000,
            max_tokens: 4_096,
            sampling_params: None,
            sampling_params_by_thinking_level: None,
            compat: None,
            featured: None,
        }
    }

    fn catalog() -> Vec<Model> {
        vec![
            catalog_model("alpha", "shared-1"),
            catalog_model("beta", "shared-1"),
            catalog_model("gamma", "shared-1"),
            catalog_model("beta", "other-model"),
        ]
    }

    #[test]
    fn orders_candidates_by_catalog_after_the_current_provider() {
        let candidates = failover_candidates(&catalog_model("beta", "shared-1"), &catalog());
        assert_eq!(
            candidates
                .iter()
                .map(|model| model.provider.as_str())
                .collect::<Vec<_>>(),
            ["gamma", "alpha"]
        );
    }

    #[test]
    fn keeps_one_candidate_per_provider_and_only_the_same_model_id() {
        let candidates = failover_candidates(&catalog_model("alpha", "shared-1"), &catalog());
        assert_eq!(
            candidates
                .iter()
                .map(|model| (model.provider.as_str(), model.id.as_str()))
                .collect::<Vec<_>>(),
            [("beta", "shared-1"), ("gamma", "shared-1")]
        );
        assert!(failover_candidates(&catalog_model("beta", "other-model"), &catalog()).is_empty());
    }

    #[test]
    fn the_model_reference_is_the_wire_vocabulary() {
        assert_eq!(
            model_reference(&catalog_model("prime-inference", "glm-5.3")),
            "prime-inference/glm-5.3"
        );
    }
}
