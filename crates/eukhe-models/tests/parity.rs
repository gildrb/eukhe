//! Parity verifier: parse the shipped models asset (the pinned models.dev
//! snapshot mapped through `crates/eukhe-models/catalog/overrides.json`;
//! refresh with `scripts/generate-catalog-fixture.py`) against the strict
//! schema and transport pinning. Real data, real scale: 202 entries across
//! 22 providers, 0 skipped.

use std::collections::{BTreeSet, HashSet};

use eukhe_models::pinning::{parse_provider_model_catalog, PinnedTemplates};
use eukhe_models::schema::{parse_model_catalog, InvalidEntries};
use eukhe_models::transports;
use serde_json::Value;

const FIXTURE: &str = include_str!("fixtures/catalog.v1.json");

fn fixture() -> Value {
    serde_json::from_str(FIXTURE).expect("fixture parses")
}

#[test]
fn parses_the_real_payload_with_zero_failures() {
    let parsed =
        parse_model_catalog(&fixture(), InvalidEntries::Reject).expect("real payload parses");
    let providers: BTreeSet<&str> = parsed.models.iter().map(|m| m.provider.as_str()).collect();
    assert_eq!(parsed.models.len(), 202, "the full bundled catalog");
    assert_eq!(providers.len(), 22, "22 providers");
    // No entry ever carries headers from catalog data.
    assert!(parsed.models.iter().all(|model| model.headers.is_none()));
}

#[test]
fn every_real_entry_survives_transport_pinning() {
    let pinned = parse_provider_model_catalog(&fixture(), &PinnedTemplates::from_compiled())
        .expect("pinned");
    assert_eq!(
        pinned.len(),
        202,
        "real catalog data selects only compiled transports"
    );
    let headers = pinned
        .iter()
        .filter(|model| model.headers.is_some())
        .count();
    assert!(headers > 0, "template headers are applied at parse time");
}

#[test]
fn passes_the_packer_gates() {
    // The build lane's gate: >= 20 distinct (provider, api, baseUrl) tuples.
    let parsed = parse_model_catalog(&fixture(), InvalidEntries::Reject).unwrap();
    let tuples: HashSet<(&str, &str, &str)> = parsed
        .models
        .iter()
        .map(|m| (m.provider.as_str(), m.api.as_str(), m.base_url.as_str()))
        .collect();
    assert!(tuples.len() >= 20, "packer gate: >=20 transport tuples");
    // Compiled transports (the pi-ai table plus the supplemental
    // transports) agree entry-by-entry with the fixture's tuples.
    let compiled: HashSet<(&str, &str, &str)> = transports::compiled_transport_tuples()
        .into_iter()
        .collect();
    assert!(
        parsed.models.iter().all(|m| compiled.contains(&(
            m.provider.as_str(),
            m.api.as_str(),
            m.base_url.as_str()
        ))),
        "fixture is compiled-transport-shaped"
    );
}

/// The bundle only fills in: no entry is a model the compiled catalog
/// has, so a compiled model keeps its compiled entry in the union.
#[test]
fn the_bundle_carries_no_compiled_model() {
    let parsed = parse_model_catalog(&fixture(), InvalidEntries::Reject).unwrap();
    let compiled: HashSet<(&str, &str)> = transports::compiled_models()
        .iter()
        .map(|m| (m.provider.as_str(), m.id.as_str()))
        .collect();
    let overlap: Vec<(&str, &str)> = parsed
        .models
        .iter()
        .map(|m| (m.provider.as_str(), m.id.as_str()))
        .filter(|key| compiled.contains(key))
        .collect();
    assert_eq!(overlap, Vec::<(&str, &str)>::new());
}

#[test]
fn skip_invalid_keeps_the_real_payload_whole() {
    let parsed = parse_model_catalog(&fixture(), InvalidEntries::SkipInvalid).expect("skip mode");
    assert_eq!(parsed.models.len(), 202, "no real entry is skipped");
}
