//! Oracles for the Bedrock facts that moved into data: the old id lists
//! live only here, and each test compares them with the new answers over
//! the compiled catalog and crafted ids.

use eukhe_types::pi_ai::{Model, ModelThinkingLevel, ProviderEnv, ThinkingBudgets, ThinkingLevel};

use super::{map_thinking_level_to_effort, supports_prompt_caching};
use crate::api::simple_options::{clamp_reasoning, thinking_budget_for_level};
use crate::models::{adaptive_thinking, thinking_level_map};
use crate::quirks::{match_candidates, Quirks};

const LEVELS: [ThinkingLevel; 6] = [
    ThinkingLevel::Minimal,
    ThinkingLevel::Low,
    ThinkingLevel::Medium,
    ThinkingLevel::High,
    ThinkingLevel::Xhigh,
    ThinkingLevel::Max,
];

fn any_candidate(model: &Model, needles: &[&str]) -> bool {
    match_candidates(&model.id, &model.name)
        .iter()
        .any(|candidate| needles.iter().any(|needle| candidate.contains(needle)))
}

/// The old id list of native `xhigh` effort and of block binding.
const NATIVE_XHIGH: [&str; 6] = [
    "opus-4-7", "opus-4-8", "opus-5", "sonnet-5", "haiku-5", "fable-5",
];

/// The old effort rule: the id list before the thinking-level map.
fn old_effort(model: &Model, level: ThinkingLevel) -> String {
    if level == ThinkingLevel::Xhigh && any_candidate(model, &NATIVE_XHIGH) {
        return "xhigh".to_owned();
    }
    let mapped = thinking_level_map(model)
        .and_then(|map| map.get(&ModelThinkingLevel::from(level)))
        .and_then(Option::as_ref);
    if let Some(mapped) = mapped {
        return mapped.clone();
    }
    match level {
        ThinkingLevel::Minimal | ThinkingLevel::Low => "low",
        ThinkingLevel::Medium => "medium",
        ThinkingLevel::High | ThinkingLevel::Xhigh | ThinkingLevel::Max => "high",
    }
    .to_owned()
}

/// The old adaptive-thinking pattern of the rulebook (one family).
fn old_adaptive(model: &Model) -> bool {
    any_candidate(
        model,
        &[
            "opus-4-6",
            "opus-4-7",
            "opus-4-8",
            "opus-5",
            "sonnet-4-6",
            "sonnet-5",
            "haiku-5",
            "fable-5",
        ],
    )
}

/// The old prompt-caching rule.
fn old_prompt_caching(model: &Model, env: Option<&ProviderEnv>) -> bool {
    if !any_candidate(model, &["claude"]) {
        return crate::utils::provider_env::get_provider_env_value("AWS_BEDROCK_FORCE_CACHE", env)
            .as_deref()
            == Some("1");
    }
    any_candidate(
        model,
        &[
            "fable-5",
            "opus-5",
            "sonnet-5",
            "haiku-5",
            "-4-",
            "claude-3-7-sonnet",
            "claude-3-5-haiku",
        ],
    )
}

/// The old budget table of budget-based Claude.
fn old_budget(level: ThinkingLevel, budgets: Option<&ThinkingBudgets>) -> u64 {
    let default_budget: u64 = match level {
        ThinkingLevel::Minimal => 1024,
        ThinkingLevel::Low => 2048,
        ThinkingLevel::Medium => 8192,
        ThinkingLevel::High | ThinkingLevel::Xhigh | ThinkingLevel::Max => 16384,
    };
    let custom = budgets.and_then(|budgets| match clamp_reasoning(Some(level)) {
        Some(ThinkingLevel::Minimal) => budgets.minimal,
        Some(ThinkingLevel::Low) => budgets.low,
        Some(ThinkingLevel::Medium) => budgets.medium,
        Some(ThinkingLevel::High | ThinkingLevel::Xhigh | ThinkingLevel::Max) | None => {
            budgets.high
        }
    });
    custom.unwrap_or(default_budget)
}

fn catalog() -> Vec<Model> {
    crate::models_generated::MODELS
        .values()
        .flat_map(|models| models.values())
        .cloned()
        .collect()
}

fn bedrock() -> Vec<Model> {
    catalog()
        .into_iter()
        .filter(|model| model.api == "bedrock-converse-stream")
        .collect()
}

fn renamed(template: &Model, ids: &[&str]) -> Vec<Model> {
    ids.iter()
        .map(|id| Model {
            id: (*id).to_owned(),
            name: String::new(),
            ..template.clone()
        })
        .collect()
}

#[test]
fn the_effort_is_the_thinking_level_map_answer_of_the_old_id_list() {
    let differences: Vec<String> = bedrock()
        .iter()
        .flat_map(|model| LEVELS.map(|level| (model, level)))
        .filter(|(model, level)| {
            old_effort(model, *level) != map_thinking_level_to_effort(model, *level)
        })
        .map(|(model, level)| format!("{} {level:?}", model.id))
        .collect();
    assert_eq!(differences, Vec::<String>::new());
}

#[test]
fn a_row_without_native_xhigh_in_its_map_is_sent_high() {
    let template = bedrock()
        .into_iter()
        .find(|model| model.id == "anthropic.claude-opus-4-7")
        .unwrap();
    let mut map = template.thinking_level_map.clone().unwrap();
    map.insert(ModelThinkingLevel::Xhigh, None);
    let model = Model {
        thinking_level_map: Some(map),
        ..template
    };
    assert_eq!(
        (
            old_effort(&model, ThinkingLevel::Xhigh),
            map_thinking_level_to_effort(&model, ThinkingLevel::Xhigh)
        ),
        ("xhigh".to_owned(), "high".to_owned())
    );
}

#[test]
fn block_binding_and_adaptive_thinking_are_the_rulebook_answers_of_the_old_lists() {
    let models: Vec<Model> = bedrock()
        .into_iter()
        .chain(
            catalog()
                .into_iter()
                .filter(|model| model.api == "anthropic-messages"),
        )
        .collect();
    let differences: Vec<String> = models
        .iter()
        .filter(|model| {
            let old_adaptive = if model.api == "anthropic-messages" {
                model
                    .compat
                    .as_ref()
                    .and_then(|compat| compat.as_anthropic_messages())
                    .and_then(|compat| compat.force_adaptive_thinking)
                    == Some(true)
            } else {
                old_adaptive(model)
            };
            let old_binding = old_adaptive && any_candidate(model, &NATIVE_XHIGH);
            let binding = adaptive_thinking(model)
                && Quirks::of(*model).thinking_block_binding() == Some(true);
            (old_adaptive, old_binding) != (adaptive_thinking(model), binding)
        })
        .map(|model| format!("{}/{}", model.provider, model.id))
        .collect();
    assert_eq!(differences, Vec::<String>::new());
}

#[test]
fn prompt_caching_is_the_rulebook_answer_of_the_old_id_list() {
    let forced = ProviderEnv::from([("AWS_BEDROCK_FORCE_CACHE".to_owned(), "1".to_owned())]);
    let models: Vec<Model> = bedrock();
    let crafted = renamed(
        &models[0],
        &[
            "anthropic.claude-3-7-sonnet-20250219-v1:0",
            "anthropic.claude-3-5-haiku-20241022-v1:0",
            "anthropic.claude-3-haiku-20240307-v1:0",
            "anthropic.claude-sonnet-4-20250514-v1:0",
            "us.anthropic.claude-opus-4-1-20250805-v1:0",
            "anthropic.claude-opus-4-6-v1",
            "anthropic.claude-sonnet-5",
            "amazon.nova-pro-v1:0",
            "meta.llama4-maverick-17b-instruct-v1:0",
        ],
    );
    let differences: Vec<String> = models
        .iter()
        .chain(&crafted)
        .flat_map(|model| [(model, None), (model, Some(&forced))])
        .filter(|(model, env)| {
            old_prompt_caching(model, *env) != supports_prompt_caching(model, *env)
        })
        .map(|(model, env)| format!("{} {}", model.id, env.is_some()))
        .collect();
    assert_eq!(differences, Vec::<String>::new());
}

#[test]
fn the_budget_is_the_one_budget_table() {
    let customs = [
        None,
        Some(ThinkingBudgets::default()),
        Some(ThinkingBudgets {
            minimal: Some(10),
            low: None,
            medium: Some(30),
            high: Some(40),
        }),
    ];
    let differences: Vec<String> = LEVELS
        .iter()
        .flat_map(|level| customs.iter().map(move |custom| (*level, custom.as_ref())))
        .filter(|(level, custom)| {
            old_budget(*level, *custom) != thinking_budget_for_level(*level, *custom)
        })
        .map(|(level, custom)| format!("{level:?} {custom:?}"))
        .collect();
    assert_eq!(differences, Vec::<String>::new());
}
