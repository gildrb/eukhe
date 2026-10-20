//! Provider failover on the durable path: the failover policy, the
//! candidate chain (the TS backup-model retry, `_handleBackupModelRetry`,
//! over the pi-ai catalog) and the walk over it ([`next_switch`]).
//!
//! The durable Harness already owns the per-provider quick retries (its
//! durable attempt loop with backoff).
//! What it cannot do is move a turn to a sibling provider: when a whole
//! provider is down, every retry hits the same outage and the turn dies.
//! The provider runtime (see [`super::provider`]) wraps the provider stream
//! functions and adds exactly that move: after a retryable provider
//! failure, the request re-routes to the next configured provider serving
//! the same model id. One request visits every provider of its chain once,
//! at once; it returns to a provider it left only after the failover
//! backoff and the server's wait of that provider's failure. The Bend
//! model `bend/retry.bend` walks the same way; `laws/retry.bend` states
//! its laws.

use eukhe_types::pi_ai::Model;

/// The provider-failover policy (settings `retry.failover`): whether a
/// provider outage may re-route to a sibling provider serving the same
/// model, how many switches one request may make, and the backoff of a
/// return to a provider the request already left.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProviderFailoverPolicy {
    pub enabled: bool,
    /// Switches per request (`retry.failover.maxRetries`).
    pub max_switches: u32,
    /// The wait before the first return to a provider; it doubles each
    /// return (`retry.failover.baseDelayMs`). A return never goes out at
    /// once: with `0` it waits only for a server's wait, else not at all.
    pub base_delay_ms: u64,
    /// The longest wait before a return (`retry.failover.maxDelayMs`): a
    /// provider whose server asks for longer is not returned to.
    pub max_delay_ms: u64,
}

/// One failed attempt of a request: the chain index of its provider and
/// the wait (ms) its server asked for, if any.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Tried {
    pub at: usize,
    pub server_wait_ms: Option<u64>,
}

/// The next attempt of a request: the chain index of its provider, after
/// `delay_ms`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Switch {
    pub to: usize,
    pub delay_ms: u64,
}

/// The next attempt of a request whose chain holds `len` providers (the
/// primary at 0, then its failover candidates), after the failed attempts
/// `tried` (oldest first; the last one just failed). While a provider of
/// the chain was not tried, the next such one in chain order after the
/// last, at once. Once every one was tried, the next one in chain order
/// after the last whose return wait is positive and at most
/// `max_delay_ms`: the backoff (`base_delay_ms` doubled per earlier return,
/// capped at `max_delay_ms`), and never less than the server's wait of
/// that provider's last failure. Never the provider that just failed;
/// `None` when the switches are spent or no provider may be tried.
#[must_use]
pub fn next_switch(len: usize, tried: &[Tried], policy: &ProviderFailoverPolicy) -> Option<Switch> {
    let last = tried.last()?;
    let switches = tried.len() - 1;
    if u32::try_from(switches).map_or(true, |switches| switches >= policy.max_switches) {
        return None;
    }
    // Chain order after the last attempt's provider, which it never holds:
    // the walk never goes back at once to the provider that just failed.
    let order = (last.at + 1..len).chain(0..last.at.min(len));
    let visited = |at: usize| tried.iter().any(|attempt| attempt.at == at);
    if (0..len).all(visited) {
        let returns = u32::try_from(tried.len() - len).unwrap_or(u32::MAX);
        let backoff = policy
            .base_delay_ms
            .saturating_mul(2u64.saturating_pow(returns))
            .min(policy.max_delay_ms);
        return order
            .map(|at| {
                let server = tried
                    .iter()
                    .rev()
                    .find(|attempt| attempt.at == at)
                    .and_then(|attempt| attempt.server_wait_ms)
                    .unwrap_or(0);
                Switch {
                    to: at,
                    delay_ms: backoff.max(server),
                }
            })
            .find(|switch| switch.delay_ms > 0 && switch.delay_ms <= policy.max_delay_ms);
    }
    order
        .filter(|at| !visited(*at))
        .map(|at| Switch {
            to: at,
            delay_ms: 0,
        })
        .next()
}

/// The `"provider/model-id"` reference of a model (the wire's `backupModel`
/// and `restoredModel` vocabulary).
#[must_use]
pub fn model_reference(model: &Model) -> String {
    format!("{}/{}", model.provider, model.id)
}

/// Provider-failover candidates for `current`: the other auth-configured
/// providers serving the same model id, in catalog order starting after
/// `current`'s provider, one per provider, over the pi-ai catalog.
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
