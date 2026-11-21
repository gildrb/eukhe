//! Model fallback on the durable path: when a request's model cannot go on
//! (its retries ran out, its provider's login expired, its usage limit
//! holds), the provider runtime ([`super::provider`]) moves the request to
//! another model the user configured whose provider has credentials. This
//! module gathers those candidates ([`configured_models`]) and asks the
//! compiled core which one ([`step`]: `bend/fallback.bend`,
//! `eukhe_bend::rules::fallback`; laws `laws/fallback.bend`). Eukhe never
//! signs in by itself: a provider without credentials is no candidate.

use eukhe_bend::rules::fallback::{self as rules, Choice, Why};
use eukhe_bend::{expect_core, Entry};
use eukhe_types::ai::Model as RegistryModel;
use eukhe_types::model_roles::ModelRoleGroup;
use eukhe_types::pi_ai::Model;

use super::failover::model_reference;
use crate::models::resolver::scope_matches;
use crate::models::roles::role_table;
use crate::settings::SettingsManager;

/// What a request does after its model failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Step {
    /// The run's own retry goes on with the model.
    Keep,
    /// The request goes on with the candidate at this place.
    Switch(usize),
    /// The request waits for the usage limit's reset at `until_ms`.
    Hold { until_ms: u64 },
    /// The request ends with the failure.
    End,
}

/// The models the user configured, in the order a failed request tries
/// them ([`configured_references`]), as the runtime's models: each is one
/// of `available` (its provider has credentials), once.
#[must_use]
pub fn configured_models(settings: &SettingsManager, available: &[Model]) -> Vec<Model> {
    let registry: Vec<RegistryModel> = available
        .iter()
        .filter_map(|model| eukhe_models::pi_ai_model::registry_model(model).ok())
        .collect();
    configured_references(settings, &registry)
        .iter()
        .filter_map(|reference| {
            available
                .iter()
                .find(|model| model_reference(model) == *reference)
                .cloned()
        })
        .collect()
}

/// The models the user configured ("provider/model-id"), in the order a
/// failed request tries them: the `enabledModels` scope, then the model of
/// each role that takes a chat model, in `ModelRole::ALL` order (the chat
/// role's is `defaultProvider`/`defaultModel`). Each is one of `available`
/// (its provider has credentials), once.
#[must_use]
pub fn configured_references(
    settings: &SettingsManager,
    available: &[RegistryModel],
) -> Vec<String> {
    let reference = |model: &RegistryModel| format!("{}/{}", model.provider, model.id);
    let scoped = settings
        .get_enabled_models()
        .map(|patterns| scope_matches(&patterns, available).models)
        .unwrap_or_default()
        .into_iter()
        .map(|scoped| reference(&scoped.model));
    let roles = role_table(settings.cvars())
        .into_iter()
        .filter(|row| match row.role.group() {
            ModelRoleGroup::Chat => true,
            ModelRoleGroup::Local => false,
        })
        .filter_map(|row| {
            let (provider, id) = row.provider_model()?;
            available
                .iter()
                .find(|model| model.provider == provider && model.id == id)
                .map(reference)
        });
    let mut references: Vec<String> = Vec::new();
    for candidate in scoped.chain(roles) {
        if !references.contains(&candidate) {
            references.push(candidate);
        }
    }
    references
}

/// What a request does after its model failed for `why`, with the
/// `candidates` in order and the models it already `tried` (its own model
/// first) (`rules::choose`). Each model is named by its first place in
/// `candidates`, then in `tried`.
#[must_use]
pub fn step(why: Why, candidates: &[Model], tried: &[Model]) -> Step {
    let ids: Vec<String> = candidates
        .iter()
        .chain(tried)
        .map(model_reference)
        .collect();
    let id = |model: &Model| {
        let reference = model_reference(model);
        let at = ids
            .iter()
            .position(|known| *known == reference)
            .unwrap_or(0);
        u64::try_from(at).unwrap_or(u64::MAX)
    };
    let candidate_ids: Vec<u64> = candidates.iter().map(id).collect();
    let tried_ids: Vec<u64> = tried.iter().map(id).collect();
    match expect_core(
        Entry::Fallback,
        rules::choose(why, &candidate_ids, &tried_ids),
    ) {
        Choice::Keep => Step::Keep,
        Choice::Switch(at) => usize::try_from(at)
            .ok()
            .filter(|at| *at < candidates.len())
            .map_or(Step::End, Step::Switch),
        Choice::Hold { until_ms } => Step::Hold { until_ms },
        Choice::End => Step::End,
    }
}

/// Why a request left `from`, for the run's report: the failure, with the
/// provider's own error.
#[must_use]
pub fn reason(why: Why, from: &Model, error: &str) -> String {
    match why {
        Why::Failed { failures, .. } => format!(
            "{} failed {failures} time{} in a row ({error})",
            model_reference(from),
            if failures == 1 { "" } else { "s" }
        ),
        Why::Login => format!("{} has no usable login ({error})", from.provider),
        Why::Quota { until_ms } => format!(
            "the usage limit of {} holds until {} ({error})",
            from.provider,
            crate::session::manager::format_iso(i64::try_from(until_ms).unwrap_or(i64::MAX))
        ),
        Why::Unset => "no model was chosen".to_owned(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use eukhe_types::pi_ai::{Modality, ModelCost};

    fn model(provider: &str, id: &str) -> Model {
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

    /// A model the user configured whose provider has credentials is a
    /// candidate, in the scope's order, then the roles'; one without
    /// credentials (absent from `available`) never is.
    #[test]
    fn candidates_are_the_configured_models_with_credentials() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(
            dir.path().join("settings.json"),
            serde_json::json!({
                "enabledModels": ["beta/b-1", "gamma/g-1"],
                "defaultProvider": "alpha",
                "defaultModel": "a-1",
                "subagentDefaultModel": "beta/b-2",
                "auxiliaryModel": "delta/d-1",
            })
            .to_string(),
        )
        .unwrap();
        let settings = SettingsManager::create(dir.path(), dir.path());
        let available = [
            model("alpha", "a-1"),
            model("beta", "b-1"),
            model("beta", "b-2"),
            model("delta", "d-1"),
        ];
        let references: Vec<String> = configured_models(&settings, &available)
            .iter()
            .map(model_reference)
            .collect();
        assert_eq!(
            references,
            ["beta/b-1", "alpha/a-1", "delta/d-1", "beta/b-2"]
        );
    }

    /// The core's choice names a candidate model by its place: past the
    /// tried ones.
    #[test]
    fn the_step_names_the_first_untried_candidate() {
        let candidates = [model("p", "a"), model("q", "b"), model("r", "c")];
        let [a, b, c] = &candidates;
        assert_eq!(
            [
                step(Why::Login, &candidates, &candidates[..1]),
                step(Why::Login, &candidates, &candidates),
                step(
                    Why::Quota { until_ms: 7 },
                    &candidates,
                    &[c.clone(), a.clone(), b.clone()]
                ),
                step(
                    Why::Failed {
                        failures: 1,
                        retries: 3
                    },
                    &candidates,
                    &candidates[..1]
                ),
            ],
            [
                Step::Switch(1),
                Step::End,
                Step::Hold { until_ms: 7 },
                Step::Keep
            ]
        );
    }
}
