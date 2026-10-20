use super::{normalize_id_part, supports_explicit_cache_breakpoints};
use crate::types::Model;

#[test]
fn normalize_id_part_sanitizes_truncates_and_trims() {
    assert_eq!(normalize_id_part("call/1+x"), "call_1_x");
    assert_eq!(normalize_id_part("abc___"), "abc");
    let long = "a".repeat(70);
    assert_eq!(normalize_id_part(&long).len(), 64);
}

/// The oracle: the id rule that decided the explicit prompt-cache controls
/// before the quirks rulebook held the fact (GPT-5.6 and every later GPT-5
/// minor version, every GPT-6 model).
fn id_rule(model_id: &str) -> bool {
    if let Some(rest) = model_id.strip_prefix("gpt-6") {
        return rest.is_empty() || rest.starts_with(['-', '.']);
    }
    let Some(rest) = model_id.strip_prefix("gpt-5.") else {
        return false;
    };
    let minor_end = rest
        .find(|c: char| !c.is_ascii_digit())
        .unwrap_or(rest.len());
    let (minor, suffix) = rest.split_at(minor_end);
    (suffix.is_empty() || suffix.starts_with('-'))
        && minor.parse::<u32>().is_ok_and(|minor| minor >= 6)
}

/// Every compiled catalog model, and the catalog's first `OpenAI` Responses
/// model renamed to each id of the old rule's edge cases.
fn models() -> Vec<Model> {
    let catalog: Vec<Model> = crate::models_generated::MODELS
        .values()
        .flat_map(|models| models.values())
        .cloned()
        .collect();
    let template = catalog
        .iter()
        .find(|model| model.api == "openai-responses")
        .cloned()
        .unwrap();
    let crafted = [
        "gpt-5.6",
        "gpt-5.6-sol",
        "gpt-5.06",
        "gpt-5.06-x",
        "gpt-5.7",
        "gpt-5.10",
        "gpt-5.10-mini",
        "gpt-6",
        "gpt-6-",
        "gpt-6-astra",
        "gpt-6-astra-x",
        "gpt-6-asteroid",
        "gpt-6.1-sol",
        "gpt-5.5",
        "gpt-5",
        "gpt-5.6sol",
        "gpt-60",
        "gpt-4o",
        "my-gpt-6",
    ]
    .map(|id| Model {
        id: id.to_owned(),
        name: id.to_owned(),
        ..template.clone()
    });
    catalog.into_iter().chain(crafted).collect()
}

#[test]
fn explicit_cache_breakpoints_are_the_rulebook_answer_of_the_old_id_rule() {
    let differences: Vec<String> = models()
        .iter()
        .filter(|model| id_rule(&model.id) != supports_explicit_cache_breakpoints(model))
        .map(|model| format!("{}/{}", model.provider, model.id))
        .collect();
    assert_eq!(differences, Vec::<String>::new());
}
