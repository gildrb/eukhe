//! Port of `test/xiaomi-models.test.ts` (one test per `it.each` row).

use eukhe_pi_ai::compat::get_models;

const DEPRECATED_MODEL_IDS: [&str; 3] = ["mimo-v2-flash", "mimo-v2-omni", "mimo-v2-pro"];
const REPLACEMENT_MODEL_IDS: [&str; 2] = ["mimo-v2.5", "mimo-v2.5-pro"];

fn model_ids(provider: &str) -> Vec<String> {
    get_models(provider)
        .into_iter()
        .map(|model| model.id)
        .collect()
}

fn omits_deprecated_models_from(provider: &str) {
    let model_ids = model_ids(provider);
    for model_id in DEPRECATED_MODEL_IDS {
        assert!(
            !model_ids.iter().any(|id| id == model_id),
            "{provider} contains {model_id}"
        );
    }
}

fn keeps_replacement_models_on(provider: &str) {
    let model_ids = model_ids(provider);
    for model_id in REPLACEMENT_MODEL_IDS {
        assert!(
            model_ids.iter().any(|id| id == model_id),
            "{provider} lacks {model_id}"
        );
    }
}

#[test]
fn omits_deprecated_models_from_xiaomi() {
    omits_deprecated_models_from("xiaomi");
}

#[test]
fn omits_deprecated_models_from_xiaomi_token_plan_cn() {
    omits_deprecated_models_from("xiaomi-token-plan-cn");
}

#[test]
fn omits_deprecated_models_from_xiaomi_token_plan_ams() {
    omits_deprecated_models_from("xiaomi-token-plan-ams");
}

#[test]
fn omits_deprecated_models_from_xiaomi_token_plan_sgp() {
    omits_deprecated_models_from("xiaomi-token-plan-sgp");
}

#[test]
fn keeps_replacement_models_on_xiaomi() {
    keeps_replacement_models_on("xiaomi");
}

#[test]
fn keeps_replacement_models_on_xiaomi_token_plan_cn() {
    keeps_replacement_models_on("xiaomi-token-plan-cn");
}

#[test]
fn keeps_replacement_models_on_xiaomi_token_plan_ams() {
    keeps_replacement_models_on("xiaomi-token-plan-ams");
}

#[test]
fn keeps_replacement_models_on_xiaomi_token_plan_sgp() {
    keeps_replacement_models_on("xiaomi-token-plan-sgp");
}
