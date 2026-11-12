//! Agreement with the reference implementation's policy code (credited in
//! THIRD-PARTY-NOTICES) over two catalogs: the reference implementation's
//! bundled catalog and Eukhe's (`crates/eukhe-ai/src/providers/data/*.json`
//! plus `crates/eukhe-models/tests/fixtures/catalog.v1.json`).
//!
//! The fixtures were generated at reference commit c28b3e3 by one bun process
//! running the reference catalog's TypeScript unchanged (a copy of its
//! sources with two workspace-heavy modules stubbed: `identity/index.ts`
//! re-exporting only `classifyModel`, `utils.ts` only `isRecord`):
//!
//! - `fixtures/reference_model_tokenizers.json`: for every bundled reference
//!   model (decoded with the reference `model-catalog-format.ts`) the
//!   provider, id, wire id (`requestModelId`, when it differs), the
//!   materialized `Model.tokenizer` and `resolveModelTokenizer(wire id,
//!   provider)`; for every Eukhe catalog `(provider, id)` the
//!   `resolveModelTokenizer(id, provider)`.
//! - `fixtures/reference_image_rules.json`: for every Eukhe and reference
//!   catalog `(provider, id, api)`, plus wire-only targets, the reference
//!   `resolveImageTokenization` (as a key into the distinct rules) and
//!   `resolveThinkingReplayTokens`.
//!
//! Regenerate after a reference catalog/rules bump or an Eukhe catalog change
//! (the coverage test below names the rows the fixture lacks).

use std::collections::HashSet;
use std::path::Path;

use eukhe_tokens::{
    AutoLevel, ImageTokenization, ModelRef, ModelTokenizer, PatchSizing, ThinkingReplayTokens,
    resolve_image_tokenization, resolve_model_tokenizer, resolve_thinking_replay_tokens,
};
use serde_json::Value;

const TOKENIZERS: &str = include_str!("fixtures/reference_model_tokenizers.json");
const IMAGE_RULES: &str = include_str!("fixtures/reference_image_rules.json");

fn parse(fixture: &str) -> Value {
    serde_json::from_str(fixture).expect("fixture is JSON")
}

fn rows<'a>(fixture: &'a Value, key: &str) -> &'a [Value] {
    fixture[key].as_array().expect("fixture rows")
}

fn text(value: &Value) -> &str {
    value.as_str().expect("fixture string")
}

fn tokenizer_name(model_id: &str, provider: &str) -> Option<&'static str> {
    resolve_model_tokenizer(model_id, provider).map(ModelTokenizer::name)
}

#[test]
fn reference_bundled_catalog_tokenizers_agree() {
    let fixture = parse(TOKENIZERS);
    let rows = rows(&fixture, "reference_catalog");
    let mut mismatches = Vec::new();
    let mut copied_pins = 0;
    for row in rows {
        let (provider, id) = (text(&row[0]), text(&row[1]));
        let wire = row[2].as_str().unwrap_or(id);
        let (materialized, expected) = (row[3].as_str(), row[4].as_str());
        let actual = tokenizer_name(wire, provider);
        if actual != expected {
            mismatches.push(format!(
                "{provider}/{id}: reference {expected:?}, eukhe {actual:?}"
            ));
        }
        // The reference generator keeps a copied tokenizer only on ids its
        // policy cannot classify (GitLab Duo aliases of Claude models and the
        // like).
        if materialized != expected {
            assert_eq!(
                expected, None,
                "{provider}/{id} materializes {materialized:?}"
            );
            copied_pins += 1;
        }
    }
    assert!(rows.len() > 5000, "{} reference rows", rows.len());
    assert_eq!(copied_pins, 16);
    assert!(
        mismatches.is_empty(),
        "{} mismatches:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
}

#[test]
fn eukhe_catalog_tokenizers_agree_with_reference() {
    let fixture = parse(TOKENIZERS);
    let mut mismatches = Vec::new();
    for row in rows(&fixture, "eukhe_catalog") {
        let (provider, id, expected) = (text(&row[0]), text(&row[1]), row[2].as_str());
        let actual = tokenizer_name(id, provider);
        if actual != expected {
            mismatches.push(format!(
                "{provider}/{id}: reference {expected:?}, eukhe {actual:?}"
            ));
        }
    }
    assert!(
        mismatches.is_empty(),
        "{} mismatches:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
}

/// Every `(provider, id, api)` of Eukhe's compiled catalog.
fn eukhe_catalog() -> Vec<(String, String, String)> {
    let crates = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates dir");
    let mut models = Vec::new();
    let mut push = |model: &Value| {
        models.push((
            text(&model["provider"]).to_owned(),
            text(&model["id"]).to_owned(),
            text(&model["api"]).to_owned(),
        ));
    };
    let data = crates.join("eukhe-ai/src/providers/data");
    for entry in std::fs::read_dir(&data).expect("eukhe-ai provider data") {
        let path = entry.expect("data entry").path();
        if path.extension().is_none_or(|ext| ext != "json") {
            continue;
        }
        let groups: Value =
            serde_json::from_str(&std::fs::read_to_string(&path).expect("data file"))
                .expect("JSON");
        for group in groups.as_object().expect("api groups").values() {
            group
                .as_object()
                .expect("models")
                .values()
                .for_each(&mut push);
        }
    }
    let v1 = crates.join("eukhe-models/tests/fixtures/catalog.v1.json");
    let v1: Value =
        serde_json::from_str(&std::fs::read_to_string(v1).expect("catalog.v1")).expect("JSON");
    v1["models"]
        .as_array()
        .expect("models")
        .iter()
        .for_each(push);
    models
}

#[test]
fn fixtures_cover_the_eukhe_catalog() {
    let tokenizers = parse(TOKENIZERS);
    let covered: HashSet<(&str, &str)> = rows(&tokenizers, "eukhe_catalog")
        .iter()
        .map(|row| (text(&row[0]), text(&row[1])))
        .collect();
    let image_fixture = parse(IMAGE_RULES);
    let priced: HashSet<(&str, &str, &str)> = rows(&image_fixture, "rows")
        .iter()
        .map(|row| (text(&row[1]), text(&row[2]), text(&row[3])))
        .collect();
    let catalog = eukhe_catalog();
    assert!(catalog.len() > 1000, "{} Eukhe catalog rows", catalog.len());
    let missing: Vec<String> = catalog
        .iter()
        .filter(|(provider, id, api)| {
            !covered.contains(&(provider.as_str(), id.as_str()))
                || !priced.contains(&(provider.as_str(), id.as_str(), api.as_str()))
        })
        .map(|(provider, id, api)| format!("{provider}/{id} ({api})"))
        .collect();
    assert!(
        missing.is_empty(),
        "regenerate the reference fixtures; {} Eukhe catalog rows are missing:\n{}",
        missing.len(),
        missing.join("\n")
    );
}

fn sizing(value: &Value) -> PatchSizing {
    PatchSizing {
        max_edge: number(&value["maxEdge"]),
        patch_budget: value.get("patchBudget").map(number),
    }
}

fn number(value: &Value) -> u32 {
    u32::try_from(value.as_u64().expect("integer")).expect("u32")
}

/// The reference `ImageTokenization` JSON as the Rust rule.
fn image_rule(rule: &Value) -> ImageTokenization {
    let verified = rule
        .get("verified")
        .and_then(Value::as_bool)
        .unwrap_or(false);
    match text(&rule["regime"]) {
        "openai-patch" => ImageTokenization::OpenAiPatch {
            multiplier: rule["multiplier"].as_f64().expect("multiplier"),
            low: sizing(&rule["low"]),
            high: sizing(&rule["high"]),
            original: sizing(&rule["original"]),
            auto: match text(&rule["auto"]) {
                "high" => AutoLevel::High,
                "original" => AutoLevel::Original,
                other => panic!("auto {other}"),
            },
            verified,
        },
        "anthropic-patch" => ImageTokenization::AnthropicPatch {
            max_edge: number(&rule["maxEdge"]),
            max_tokens: number(&rule["maxTokens"]),
            verified,
        },
        "deepseek-patch" => ImageTokenization::DeepSeekPatch {
            patch_size: number(&rule["patchSize"]),
            downsample: number(&rule["downsample"]),
            max_tokens: number(&rule["maxTokens"]),
            min_pixels: number(&rule["minPixels"]),
            verified,
        },
        "fixed" => ImageTokenization::Fixed {
            tokens: number(&rule["tokens"]),
            verified,
        },
        other => panic!("regime {other}"),
    }
}

#[test]
fn image_and_thinking_replay_rules_agree_with_reference() {
    let fixture = parse(IMAGE_RULES);
    let rules = fixture["rules"].as_object().expect("rules");
    let rows = rows(&fixture, "rows");
    let mut mismatches = Vec::new();
    for row in rows {
        let (provider, id, api) = (text(&row[1]), text(&row[2]), text(&row[3]));
        let model = ModelRef { id, provider, api };
        let expected = row[4].as_str().map(|key| image_rule(&rules[key]));
        let actual = resolve_image_tokenization(model);
        if actual != expected {
            mismatches.push(format!(
                "{provider}/{id} ({api}) image: reference {expected:?}, eukhe {actual:?}"
            ));
        }
        let replay = match text(&row[5]) {
            "output" => ThinkingReplayTokens::Output,
            "signature" => ThinkingReplayTokens::Signature,
            other => panic!("thinking replay {other}"),
        };
        if resolve_thinking_replay_tokens(model) != replay {
            mismatches.push(format!(
                "{provider}/{id} ({api}) thinking replay: reference {replay:?}"
            ));
        }
    }
    assert!(rows.len() > 7000, "{} image rows", rows.len());
    assert!(
        mismatches.is_empty(),
        "{} mismatches:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
}
