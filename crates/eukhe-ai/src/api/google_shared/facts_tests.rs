//! Oracles for the Google thinking facts that moved into the quirks
//! rulebook: the old id rules live only here, and each test compares them
//! with the rulebook answers over the compiled catalog and crafted ids.

use eukhe_types::pi_ai::{Model, ThinkingBudgets};
use regex::Regex;

use super::{google_thinking_budget, uses_google_thinking_level, ResolvedGoogleThinkingLevel};

const LEVELS: [ResolvedGoogleThinkingLevel; 4] = [
    ResolvedGoogleThinkingLevel::Minimal,
    ResolvedGoogleThinkingLevel::Low,
    ResolvedGoogleThinkingLevel::Medium,
    ResolvedGoogleThinkingLevel::High,
];

/// The old format rule: Gemini 3 Pro/Flash ids, the two `-latest` aliases
/// and Gemma 4 take `thinkingLevel`.
fn old_uses_level(model: &Model) -> bool {
    let id = model.id.to_lowercase();
    Regex::new(r"gemini-3(?:\.\d+)?-(?:pro|flash)")
        .unwrap()
        .is_match(&id)
        || id == "gemini-flash-latest"
        || id == "gemini-flash-lite-latest"
        || Regex::new(r"gemma-?4").unwrap().is_match(&id)
}

/// The old `[minimal, low, medium, high]` table entry of `level`.
const fn entry(budgets: [i64; 4], level: ResolvedGoogleThinkingLevel) -> i64 {
    match level {
        ResolvedGoogleThinkingLevel::Minimal => budgets[0],
        ResolvedGoogleThinkingLevel::Low => budgets[1],
        ResolvedGoogleThinkingLevel::Medium => budgets[2],
        ResolvedGoogleThinkingLevel::High => budgets[3],
    }
}

/// The old Gemini API budget rule (no custom budgets).
fn old_generative_ai_budget(model: &Model, level: ResolvedGoogleThinkingLevel) -> i64 {
    let budgets: [i64; 4] = if model.id.contains("2.5-pro") {
        [128, 2048, 8192, 32768]
    } else if model.id.contains("2.5-flash-lite") {
        [512, 2048, 8192, 24576]
    } else if model.id.contains("2.5-flash") {
        [128, 2048, 8192, 24576]
    } else {
        return -1;
    };
    entry(budgets, level)
}

/// The old Vertex budget rule (no custom budgets): no flash-lite table.
fn old_vertex_budget(model: &Model, level: ResolvedGoogleThinkingLevel) -> i64 {
    let budgets: [i64; 4] = if model.id.contains("2.5-pro") {
        [128, 2048, 8192, 32768]
    } else if model.id.contains("2.5-flash") {
        [128, 2048, 8192, 24576]
    } else {
        return -1;
    };
    entry(budgets, level)
}

fn catalog() -> Vec<Model> {
    crate::models_generated::MODELS
        .values()
        .flat_map(|models| models.values())
        .filter(|model| model.api.starts_with("google"))
        .cloned()
        .collect()
}

fn renamed(template: &Model, ids: &[&str]) -> Vec<Model> {
    ids.iter()
        .map(|id| Model {
            id: (*id).to_owned(),
            name: (*id).to_owned(),
            ..template.clone()
        })
        .collect()
}

#[test]
fn the_thinking_format_is_the_rulebook_answer_of_the_old_rule_up_to_gemini_3() {
    let catalog = catalog();
    let crafted = renamed(
        &catalog[0],
        &[
            "gemini-3-pro",
            "gemini-3.5-flash-lite",
            "gemini-flash-latest",
            "gemini-flash-lite-latest",
            "gemma-4-27b-it",
            "gemma4-e4b",
            "gemini-2.5-pro",
            "gemini-2.0-flash",
            "gemini-4-pro",
            "gemini-4.1-flash",
            "gemini-3-nano",
        ],
    );
    let differences: Vec<(String, bool)> = catalog
        .iter()
        .chain(&crafted)
        .filter(|model| old_uses_level(model) != uses_google_thinking_level(model))
        .map(|model| (model.id.clone(), uses_google_thinking_level(model)))
        .collect();
    // Gemini 4 and every Gemini 3 model take `thinkingLevel` now; the old
    // regex stopped at major 3 Pro/Flash.
    assert_eq!(
        differences,
        vec![
            ("gemini-4-pro".to_owned(), true),
            ("gemini-4.1-flash".to_owned(), true),
            ("gemini-3-nano".to_owned(), true),
        ]
    );
}

#[test]
fn the_budgets_are_the_rulebook_answer_of_the_gemini_api_table() {
    let catalog = catalog();
    let crafted = renamed(
        &catalog[0],
        &[
            "gemini-2.5-pro",
            "gemini-2.5-flash",
            "gemini-2.5-flash-lite",
            "gemini-2.5-flash-lite-preview-09-2025",
            "gemini-live-2.5-flash",
            "gemini-2.0-flash",
            "gemini-3-pro",
        ],
    );
    let differences: Vec<String> = catalog
        .iter()
        .chain(&crafted)
        .flat_map(|model| LEVELS.map(|level| (model, level)))
        .filter(|(model, level)| {
            old_generative_ai_budget(model, *level) != google_thinking_budget(model, *level, None)
        })
        .map(|(model, level)| format!("{}/{} {level:?}", model.provider, model.id))
        .collect();
    assert_eq!(differences, Vec::<String>::new());
}

#[test]
fn vertex_flash_lite_takes_the_flash_lite_minimum() {
    let catalog = catalog();
    let crafted = renamed(
        &catalog[0],
        &[
            "gemini-2.5-pro",
            "gemini-2.5-flash",
            "gemini-2.5-flash-lite",
        ],
    );
    let differences: Vec<(String, i64, i64)> = catalog
        .iter()
        .chain(&crafted)
        .flat_map(|model| LEVELS.map(|level| (model, level)))
        .filter(|(model, level)| {
            old_vertex_budget(model, *level) != google_thinking_budget(model, *level, None)
        })
        .map(|(model, level)| {
            (
                model.id.clone(),
                old_vertex_budget(model, level),
                google_thinking_budget(model, level, None),
            )
        })
        .collect();
    // The old Vertex copy had no flash-lite table: flash-lite took the
    // flash minimum (128) where the model accepts 512 at least.
    let lite: Vec<(String, i64, i64)> = catalog
        .iter()
        .chain(&crafted)
        .filter(|model| model.id.contains("2.5-flash-lite"))
        .map(|model| (model.id.clone(), 128, 512))
        .collect();
    assert_eq!(differences, lite);
}

#[test]
fn a_custom_budget_stays_inside_the_range_of_the_model() {
    let template = &catalog()[0];
    let lite = renamed(template, &["gemini-2.5-flash-lite"]).remove(0);
    let other = renamed(template, &["gemini-2.0-flash"]).remove(0);
    let custom = ThinkingBudgets {
        minimal: Some(64),
        low: Some(4096),
        medium: None,
        high: Some(100_000),
    };
    let budgets =
        |model: &Model| LEVELS.map(|level| google_thinking_budget(model, level, Some(&custom)));
    assert_eq!(
        (budgets(&lite), budgets(&other)),
        ([512, 4096, 8192, 24576], [64, 4096, -1, 100_000])
    );
}
