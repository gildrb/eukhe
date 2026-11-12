//! The quirks rulebook's provider defaults against the catalogs: each
//! default names a model of its provider.

use std::collections::BTreeSet;

use eukhe_ai::providers::prime_inference::PRIME_INFERENCE_PROVIDER_ID;
use eukhe_ai::providers::prime_inference_models::PRIME_INFERENCE_MODELS;
use eukhe_models::transports;
use serde_json::Value;

/// The shipped models asset (see `parity.rs`).
const FIXTURE: &str = include_str!("fixtures/catalog.v1.json");

/// Each provider default names a model of its provider: the Prime
/// Inference default a model of the compiled Prime list, every other
/// default a model of the built-in catalog (the compiled catalog and the
/// bundled asset that fills in the models it lacks).
#[test]
fn default_is_in_catalog() {
    let fixture: Value = serde_json::from_str(FIXTURE).expect("fixture parses");
    let built_in: BTreeSet<(&str, &str)> = fixture["models"]
        .as_array()
        .expect("the fixture lists models")
        .iter()
        .map(|row| {
            (
                row["provider"].as_str().expect("a row has a provider"),
                row["id"].as_str().expect("a row has an id"),
            )
        })
        .chain(
            transports::compiled_models()
                .iter()
                .map(|model| (model.provider.as_str(), model.id.as_str())),
        )
        .collect();
    let missing: Vec<(&str, &str)> = eukhe_ai::quirks::provider_defaults()
        .filter(|(provider, model)| {
            if *provider == PRIME_INFERENCE_PROVIDER_ID {
                !PRIME_INFERENCE_MODELS.contains_key(*model)
            } else {
                !built_in.contains(&(*provider, *model))
            }
        })
        .collect();
    assert_eq!(missing, Vec::new());
}
