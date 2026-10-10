//! The compiled transport table.
//!
//! The compiled model catalog (`eukhe_ai::models_generated`, ported from the TS
//! `models.generated.ts`) is the hand-maintained table of transports the
//! client implements: 42 `(provider, api, baseUrl)` tuples across 31 public
//! providers, plus the 110 offline Prime Inference entries (one transport
//! tuple of its own). It only changes with a client
//! release — the catalog can select among these transports but never
//! introduce one.

use std::collections::HashSet;
use std::sync::LazyLock;

use crate::Model;

/// The compiled catalog, shared as one immutable list (the TS
/// `installedModels`).
#[must_use]
pub fn compiled_models() -> &'static [Model] {
    static COMPILED: LazyLock<Vec<Model>> = LazyLock::new(|| {
        let mut models: Vec<Model> = eukhe_ai::models_generated::get_providers()
            .into_iter()
            .flat_map(eukhe_ai::models_generated::get_models)
            .cloned()
            .collect();
        models.shrink_to_fit();
        models
    });
    &COMPILED
}

/// Distinct compiled `(provider, api, baseUrl)` tuples (Prime Inference
/// excluded — its entries ship as their own compiled section).
#[must_use]
pub fn compiled_transport_tuples() -> Vec<(&'static str, &'static str, &'static str)> {
    let mut tuples: Vec<(&'static str, &'static str, &'static str)> = Vec::new();
    let mut seen: HashSet<(&str, &str, &str)> = HashSet::new();
    for model in compiled_models() {
        if model.provider == "prime-inference" {
            continue;
        }
        if seen.insert((
            model.provider.as_str(),
            model.api.as_str(),
            model.base_url.as_str(),
        )) {
            tuples.push((
                model.provider.as_str(),
                model.api.as_str(),
                model.base_url.as_str(),
            ));
        }
    }
    tuples
}

/// The compiled Prime Inference entries (joined into every resolved
/// catalog). Private ids (internal/, dev/, ids containing `:`) never ship
/// compiled.
#[must_use]
pub fn prime_inference_offline_entries() -> Vec<Model> {
    compiled_models()
        .iter()
        .filter(|model| {
            model.provider == "prime-inference"
                && !crate::prime_inference::is_private_prime_inference_model_id(&model.id)
        })
        .cloned()
        .collect()
}
