//! Model fallback on the durable path: when a request's model cannot go on
//! (its retries ran out, its provider's login expired, its usage limit
//! holds), the provider runtime ([`super::provider`]) moves the request to
//! another model the user configured whose provider has credentials, else
//! to the default model of another provider the user is signed in to. This
//! module gathers those candidates ([`configured_models`]) and defaults
//! ([`signed_in_defaults`]), asks the compiled core which one ([`step`]:
//! `bend/fallback.bend`, `eukhe_bend::rules::fallback`; laws
//! `laws/fallback.bend`), and writes the report of a run that ends
//! ([`end_report`]). Eukhe never signs in by itself: a provider without
//! credentials is no candidate.

use eukhe_ai::quirks::provider_defaults;
use eukhe_bend::rules::fallback::{self as rules, Choice, Why};
use eukhe_bend::{expect_core, Entry};
use eukhe_types::ai::Model as RegistryModel;
use eukhe_types::model_roles::ModelRole;
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
    /// The request goes on with the model at this place of the candidates,
    /// then the defaults.
    Switch(usize),
    /// The request waits for the usage limit's reset at `until_ms`.
    Hold { until_ms: u64 },
    /// The request ends with this failure: the cause its report names.
    End(Why),
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

/// The models the user configured to do the run's work ("provider/model-id"),
/// in the order a failed request tries them: the `enabledModels` scope, then
/// the model of each work role ([`does_work`]), in `ModelRole::ALL` order
/// (the chat role's is `defaultProvider`/`defaultModel`). A model configured
/// only for a side job (memory, summaries, titles, judgments, translation,
/// `rlm.query`) is none. Each is one of `available` (its provider has
/// credentials), once.
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
        .filter(|row| does_work(row.role))
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

/// Whether `role`'s model does the run's work (the chat, the worker,
/// subagents, turns with images, the phone gateway), so a failed run may
/// go on with it. A side job's model (memory, summaries, `rlm.query`,
/// titles, judgments, translation, speech, dictation) never takes the run.
const fn does_work(role: ModelRole) -> bool {
    match role {
        ModelRole::Chat
        | ModelRole::Image
        | ModelRole::Subagent
        | ModelRole::Worker
        | ModelRole::Gateway => true,
        ModelRole::Memory
        | ModelRole::Auxiliary
        | ModelRole::Query
        | ModelRole::Titles
        | ModelRole::Judge
        | ModelRole::Translate
        | ModelRole::Speech
        | ModelRole::Dictation => false,
    }
}

/// The default model of each provider the user is signed in to, in
/// provider id order: each is one of `available` (its provider has
/// credentials) and the provider's default
/// ([`eukhe_ai::quirks::provider_defaults`]).
#[must_use]
pub fn signed_in_defaults(available: &[Model]) -> Vec<Model> {
    provider_defaults()
        .filter_map(|(provider, id)| {
            available
                .iter()
                .find(|model| model.provider == provider && model.id == id)
                .cloned()
        })
        .collect()
}

/// What a request does after its model failed for `why`, with the
/// configured `candidates` in order, the signed-in `defaults` in order,
/// and the models it already `tried` (its own model first)
/// (`rules::choose`). Each model is named by its first place in
/// `candidates`, then `defaults`, then `tried`; a switch names its place
/// in `candidates` then `defaults`.
#[must_use]
pub fn step(why: Why, candidates: &[Model], defaults: &[Model], tried: &[Model]) -> Step {
    let offered: Vec<&Model> = candidates.iter().chain(defaults).collect();
    let ids: Vec<String> = offered
        .iter()
        .copied()
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
    let default_ids: Vec<u64> = defaults.iter().map(id).collect();
    let tried_ids: Vec<u64> = tried.iter().map(id).collect();
    match expect_core(
        Entry::Fallback,
        rules::choose(why, &candidate_ids, &default_ids, &tried_ids),
    ) {
        Choice::Keep => Step::Keep,
        Choice::Switch(at) => usize::try_from(at)
            .ok()
            .filter(|at| *at < offered.len())
            .map_or(Step::End(why), Step::Switch),
        Choice::Hold { until_ms } => Step::Hold { until_ms },
        Choice::End(cause) => Step::End(cause),
    }
}

/// The fix an end report on a provider without a usable login names,
/// before the provider's id.
pub(crate) const LOGIN_FIX: &str = "Fix: run eukhe and type /login";

/// The report of a request that ended because `from` failed for `cause`
/// ([`Step::End`]) and no other model could take it: the cause and the
/// one command that fixes it. `None` for a cause with no such command
/// (the provider's own failure stands).
#[must_use]
pub fn end_report(cause: Why, from: &Model, error: &str) -> Option<String> {
    match cause {
        Why::Login => Some(format!(
            "The run ended: {}, and no other signed-in provider can take the run. {LOGIN_FIX} {}",
            reason(cause, from, error),
            from.provider
        )),
        Why::Failed { .. } | Why::Quota { .. } | Why::Unset => None,
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

    /// The candidates of the settings `settings` over `available`.
    fn candidates(settings: &serde_json::Value, available: &[Model]) -> Vec<String> {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(dir.path().join("settings.json"), settings.to_string()).unwrap();
        let settings = SettingsManager::create(dir.path(), dir.path());
        configured_models(&settings, available)
            .iter()
            .map(model_reference)
            .collect()
    }

    /// A model the user configured to do the run's work whose provider has
    /// credentials is a candidate: the scope's in its order, then the work
    /// roles' (chat, image, subagent, worker, gateway); one without
    /// credentials (absent from `available`) never is.
    #[test]
    fn candidates_are_the_work_models_with_credentials() {
        let available = [
            model("alpha", "a-1"),
            model("alpha", "a-2"),
            model("beta", "b-1"),
            model("beta", "b-2"),
            model("epsilon", "e-1"),
            model("zeta", "z-1"),
        ];
        assert_eq!(
            candidates(
                &serde_json::json!({
                    "enabledModels": ["beta/b-1", "gamma/g-1"],
                    "defaultProvider": "alpha",
                    "defaultModel": "a-1",
                    "imageModel": "epsilon/e-1",
                    "subagentDefaultModel": "beta/b-2",
                    "workerModel": "alpha/a-2",
                    "gateway": { "signal": { "model": "zeta/z-1" } },
                }),
                &available
            ),
            [
                "beta/b-1",
                "alpha/a-1",
                "epsilon/e-1",
                "beta/b-2",
                "alpha/a-2",
                "zeta/z-1"
            ]
        );
    }

    /// A model configured only for a side job (memory, summaries,
    /// `rlm.query`) is no candidate, though its provider has credentials;
    /// the same model configured for work too keeps its work place.
    #[test]
    fn a_side_jobs_model_is_a_candidate_only_when_it_also_does_work() {
        let available = [
            model("alpha", "a-1"),
            model("beta", "b-1"),
            model("delta", "d-1"),
            model("memory", "m-1"),
            model("query", "q-1"),
        ];
        assert_eq!(
            candidates(
                &serde_json::json!({
                    "enabledModels": ["beta/b-1"],
                    "defaultProvider": "alpha",
                    "defaultModel": "a-1",
                    "memory": { "model": "memory/m-1" },
                    "auxiliaryModel": "delta/d-1",
                    "rlm": { "queryModel": "query/q-1" },
                }),
                &available
            ),
            ["beta/b-1", "alpha/a-1"]
        );
        assert_eq!(
            candidates(
                &serde_json::json!({
                    "enabledModels": ["beta/b-1"],
                    "defaultProvider": "alpha",
                    "defaultModel": "a-1",
                    "memory": { "model": "beta/b-1" },
                    "auxiliaryModel": "alpha/a-1",
                }),
                &available
            ),
            ["beta/b-1", "alpha/a-1"]
        );
    }

    /// The default model of every provider with credentials, in provider
    /// id order: another model of a signed-in provider is none, nor is the
    /// default of a provider without credentials.
    #[test]
    fn defaults_are_the_signed_in_providers_default_models() {
        let default = |provider: &str| {
            model(
                provider,
                eukhe_ai::quirks::provider_default_model(provider).unwrap(),
            )
        };
        let available = [
            model("openai-codex", "not-the-default"),
            default("openai-codex"),
            default("anthropic"),
            model("faux", "f-1"),
        ];
        assert_eq!(
            signed_in_defaults(&available),
            [default("anthropic"), default("openai-codex")]
        );
    }

    /// The core's choice names a model by its place: past the tried ones,
    /// the candidates first, then the defaults; an end carries its cause.
    #[test]
    fn the_step_names_the_first_untried_candidate_then_default() {
        let candidates = [model("p", "a"), model("q", "b"), model("r", "c")];
        let [a, b, c] = &candidates;
        let defaults = [b.clone(), model("s", "d")];
        assert_eq!(
            [
                step(Why::Login, &candidates, &[], &candidates[..1]),
                step(Why::Login, &candidates, &[], &candidates),
                step(Why::Login, &candidates, &defaults, &candidates),
                step(
                    Why::Quota { until_ms: 7 },
                    &candidates,
                    &[],
                    &[c.clone(), a.clone(), b.clone()]
                ),
                step(
                    Why::Failed {
                        failures: 1,
                        retries: 3
                    },
                    &candidates,
                    &defaults,
                    &candidates[..1]
                ),
            ],
            [
                Step::Switch(1),
                Step::End(Why::Login),
                Step::Switch(4),
                Step::Hold { until_ms: 7 },
                Step::Keep
            ]
        );
    }

    /// An end on a provider without a usable login names the cause and
    /// the command that signs in again; every other end keeps the
    /// provider's own failure.
    #[test]
    fn an_end_on_a_login_names_the_login_command() {
        let from = model("anthropic", "claude-haiku-4-5");
        assert_eq!(
            [
                end_report(Why::Login, &from, "OAuth refresh failed for anthropic: 400"),
                end_report(
                    Why::Failed {
                        failures: 4,
                        retries: 3
                    },
                    &from,
                    "overloaded"
                ),
            ],
            [
                Some(
                    "The run ended: anthropic has no usable login (OAuth refresh failed for anthropic: 400), and no other signed-in provider can take the run. Fix: run eukhe and type /login anthropic"
                        .to_owned()
                ),
                None,
            ]
        );
    }
}
