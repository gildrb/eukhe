//! The bridge between the session-model resolution
//! ([`super::resolve_open_model`] over [`super::resolve_session_model`])
//! and its Bend model (`bend/default_model.bend`, whose laws `PROOF.bend`
//! proves). For each resolution the Rust test writes a models.json into a
//! temp dir (a provider `keyed` with credentials and `n` models `k0..`,
//! and a model `u0` added to the built-in provider `anthropic`, which has
//! no credentials), saves a default model and maybe an `enabledModels`
//! scope, runs the real resolution, and prints the session it opens; the
//! model prints the same from the scenario.
//! `bend/bridge_default_model.bend` documents the scenario format.
//!
//! [`compare`] runs it (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::fmt::Write as _;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_durable::testing::bridge::{compare, Rng, Scenario};
use serde_json::json;

use super::tests::{offline_models, settings};
use super::{resolve_open_model, OpenModel};
use crate::models::DefaultMiss;

/// The model number of the saved default `u0` (in the catalog, no
/// credentials).
const UNKEYED: u64 = 10;
/// The model number of the saved default `keyed/gone` (not in the catalog).
const GONE: u64 = 20;

/// The model number of the model id `id` (`k<j>` is `j`).
fn number(id: &str) -> u64 {
    match id {
        "u0" => UNKEYED,
        "gone" => GONE,
        keyed => keyed
            .strip_prefix('k')
            .and_then(|j| j.parse().ok())
            .unwrap_or_else(|| panic!("an unknown model id {keyed}")),
    }
}

/// One resolution: its scenario line for the model, and the line of the
/// session the Rust resolution opens.
async fn resolution(rng: &mut Rng) -> (String, String) {
    let temp = tempfile::tempdir().unwrap();
    let keyed = rng.range(0, 3);
    let mut providers = serde_json::Map::new();
    if keyed > 0 {
        let models: Vec<_> = (0..keyed)
            .map(|j| json!({ "id": format!("k{j}") }))
            .collect();
        providers.insert(
            "keyed".to_owned(),
            json!({
                "baseUrl": "http://127.0.0.1:9/v1", "apiKey": "bridge-key",
                "api": "openai-completions", "models": models
            }),
        );
    }
    providers.insert(
        "anthropic".to_owned(),
        json!({ "models": [{ "id": "u0" }] }),
    );
    std::fs::write(
        temp.path().join("models.json"),
        json!({ "providers": providers }).to_string(),
    )
    .unwrap();
    let loaded = offline_models(temp.path());
    assert_eq!(loaded.diagnostics, Vec::<String>::new());

    // The saved default: none, a keyed model, the unkeyed model, or a
    // model the catalog does not have.
    let saved: Option<(&str, String)> = match rng.below(4) {
        0 => None,
        1 if keyed > 0 => Some(("keyed", format!("k{}", rng.below(keyed)))),
        1 | 2 => Some(("anthropic", "u0".to_owned())),
        _ => Some(("keyed", "gone".to_owned())),
    };
    // A scope of some keyed models, in a random order.
    let scope: Vec<u64> = if keyed > 0 && rng.chance(40) {
        let mut scope: Vec<u64> = (0..keyed).filter(|_| rng.chance(60)).collect();
        if scope.is_empty() {
            scope.push(rng.below(keyed));
        }
        if rng.chance(50) {
            scope.reverse();
        }
        scope
    } else {
        Vec::new()
    };

    let mut value = serde_json::Map::new();
    if let Some((provider, id)) = &saved {
        value.insert("defaultProvider".to_owned(), json!(provider));
        value.insert("defaultModel".to_owned(), json!(id));
    }
    if !scope.is_empty() {
        let patterns: Vec<String> = scope.iter().map(|j| format!("keyed/k{j}")).collect();
        value.insert("enabledModels".to_owned(), json!(patterns));
    }
    let settings = settings(serde_json::Value::Object(value));

    // The scenario line: what the catalogs say of the saved default, and
    // the chain's pick without it (the first scoped model, else the first
    // keyed model).
    let next = match (scope.first(), keyed) {
        (Some(j), _) => j + 1,
        (None, 0) => 0,
        (None, _) => 1,
    };
    let line = match &saved {
        None => format!("0 0 0 0 {next}"),
        Some((_, id)) => {
            let in_catalog = id != "gone";
            let has_key = id.starts_with('k');
            let out = !scope.is_empty() && !scope.iter().any(|j| format!("k{j}") == *id);
            format!(
                "{} {} {} {} {next}",
                number(id) + 1,
                u8::from(in_catalog),
                u8::from(has_key),
                u8::from(out)
            )
        }
    };

    let opened: OpenModel =
        resolve_open_model(&loaded.models, &settings, None, None, &BACKGROUND_CONTEXT)
            .await
            .unwrap();
    let mut session = match &opened.resolved {
        Some(resolved) => {
            let is_saved = saved.as_ref().is_some_and(|(provider, id)| {
                resolved.model.provider == *provider && resolved.model.model_id == *id
            });
            if is_saved {
                "S".to_owned()
            } else {
                format!("O {}", number(&resolved.model.model_id))
            }
        }
        None => "X".to_owned(),
    };
    let notes = opened
        .resolved
        .as_ref()
        .and_then(|resolved| resolved.substituted.as_ref())
        .into_iter()
        .chain(opened.refused.as_ref());
    for note in notes {
        let reason = match note.reason {
            DefaultMiss::NotInCatalog => 0,
            DefaultMiss::NoCredentials => 1,
            DefaultMiss::NotInScope => 2,
        };
        write!(session, " N {} {reason}", number(&note.wanted.model_id)).unwrap();
    }
    (line, session)
}

#[tokio::test]
async fn the_rust_session_model_resolution_equals_the_bend_model() {
    let mut scenarios = Vec::new();
    for seed in 1..=20 {
        let mut rng = Rng(seed);
        let mut events = String::new();
        let mut transcript = String::new();
        for _ in 0..8 {
            let (line, session) = resolution(&mut rng).await;
            writeln!(events, "{line}").unwrap();
            writeln!(transcript, "{session}").unwrap();
        }
        scenarios.push(Scenario {
            name: seed.to_string(),
            events,
            transcript,
        });
    }
    compare("bend/bridge_default_model.bend", scenarios);
}
