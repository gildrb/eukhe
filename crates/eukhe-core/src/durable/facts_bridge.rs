//! The bridge between the model and provider facts that live in data
//! (docs/inference.md S6.10) and their Bend model (`bend/facts.bend`; the
//! laws are `laws/model_facts.bend`, which `PROOF.bend` proves): both run
//! the same scenarios and must print the same transcript, byte for byte
//! (`bend/bridge_facts.bend` documents the format).
//!
//! - Decisions: the scenario lists the rules of the shipped rulebook
//!   (`quirks/rulebook.json`, read as data) for the five decision
//!   directives, then every model of the compiled catalog (and crafted ones:
//!   a flipped compat flag, ids past the catalog) with its rulebook query.
//!   The Rust side prints what the wire APIs decide ([`adaptive_thinking`],
//!   the block binding, [`supports_prompt_caching`] without and with
//!   `AWS_BEDROCK_FORCE_CACHE=1`, [`supports_explicit_cache_breakpoints`],
//!   [`uses_google_thinking_level`]); the Bend side looks the same query up
//!   in the table. A decision from anything but the table (a model id test)
//!   makes the two differ.
//! - Budgets: [`google_thinking_budget`] against the rule of the model's
//!   family in the table, [`adjust_max_tokens_for_thinking`],
//!   [`clamp_thinking_budget_to_answer_room`], the compactor's
//!   [`thinking_output_cap`], the Bedrock effort
//!   ([`map_thinking_level_to_effort`]) against the model's thinking-level
//!   map, and the shipped default budgets against the old Bedrock table.
//! - Prices: [`service_tier_multiplier`] for every model of the `OpenAI` wire
//!   APIs and every tier against the `service_tier_prices` rows of its
//!   provider and API (read as data), and the 1h cache write rate of
//!   [`calculate_cost`] against the model's `cache_write_1h_prices` row.
//!
//! [`compare`] runs them (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::collections::HashMap;
use std::fmt::Write as _;

use eukhe_ai::api::bedrock_converse_stream::{
    map_thinking_level_to_effort, supports_prompt_caching,
};
use eukhe_ai::api::google_shared::{
    google_thinking_budget, uses_google_thinking_level, ResolvedGoogleThinkingLevel,
};
use eukhe_ai::api::openai_responses_shared::supports_explicit_cache_breakpoints;
use eukhe_ai::api::simple_options::{
    adjust_max_tokens_for_thinking, clamp_thinking_budget_to_answer_room, MIN_ANSWER_TOKENS,
};
use eukhe_ai::models::{adaptive_thinking, calculate_cost, thinking_level_map};
use eukhe_ai::quirks::{
    cache_write_1h_multiplier, service_tier_multiplier, Directive, Layer, LevelBudgets, Quirks,
    Rulebook,
};
use eukhe_durable::testing::bridge::{compare, Rng, Scenario};
use eukhe_types::pi_ai::{
    Model, ModelThinkingLevel, ProviderEnv, ThinkingBudgets, ThinkingLevel, Usage,
};
use serde_json::{json, Value};

use crate::memory::thinking_output_cap;

/// The shipped rulebook, read as data.
const RULEBOOK: &str = include_str!("../../../eukhe-ai/src/quirks/rulebook.json");

/// The decision directives, in the order of the `i` line.
const DECISIONS: [&str; 5] = [
    "adaptive_thinking",
    "thinking_block_binding",
    "prompt_caching",
    "explicit_cache_breakpoints",
    "google_thinking_level",
];

/// A target that no rule names (a query's family or host when there is
/// none).
const NO_TARGET: usize = 999_999;

fn bit(flag: bool) -> u8 {
    u8::from(flag)
}

fn rulebook() -> Value {
    serde_json::from_str(RULEBOOK).unwrap()
}

/// The ids of the entries of `section`, in order: their index is their
/// target number.
fn ids(book: &Value, section: &str) -> Vec<String> {
    book[section]
        .as_array()
        .unwrap()
        .iter()
        .map(|entry| entry["id"].as_str().unwrap().to_owned())
        .collect()
}

fn index(ids: &[String], id: Option<&str>) -> usize {
    id.and_then(|id| ids.iter().position(|known| known == id))
        .unwrap_or(NO_TARGET)
}

fn directive_id(name: &str) -> usize {
    let directive = Directive::parse(name).unwrap();
    Directive::ALL
        .iter()
        .position(|known| *known == directive)
        .unwrap()
}

fn catalog() -> Vec<Model> {
    eukhe_ai::models_generated::MODELS
        .values()
        .flat_map(|models| models.values())
        .cloned()
        .collect()
}

fn renamed(template: &Model, id: &str) -> Model {
    Model {
        id: id.to_owned(),
        name: id.to_owned(),
        ..template.clone()
    }
}

/// `model` with the compat flag `forceAdaptiveThinking` set to `flag`.
fn with_compat(model: &Model, flag: bool) -> Model {
    let mut value = serde_json::to_value(model).unwrap();
    value["compat"]["forceAdaptiveThinking"] = json!(flag);
    serde_json::from_value(value).unwrap()
}

fn decision_scenario() -> Scenario {
    let book = rulebook();
    let families = ids(&book, "families");
    let hosts = ids(&book, "hosts");
    let mut models_by_id: HashMap<String, usize> = HashMap::new();
    let mut events = String::new();
    for rule in book["rules"].as_array().unwrap() {
        let target = rule["target"].as_str().unwrap();
        let (layer, number) = match serde_json::from_value(rule["layer"].clone()).unwrap() {
            Layer::Family => (0, index(&families, Some(target))),
            Layer::Model => {
                let next = 1_000_000 + models_by_id.len();
                (1, *models_by_id.entry(target.to_owned()).or_insert(next))
            }
            Layer::Host => (2, index(&hosts, Some(target))),
        };
        for (name, value) in rule["set"].as_object().unwrap() {
            if DECISIONS.contains(&name.as_str()) {
                let value = bit(value.as_bool().unwrap());
                writeln!(events, "r {layer} {number} {} {value}", directive_id(name)).unwrap();
            }
        }
    }
    let ids: Vec<String> = DECISIONS
        .iter()
        .map(|name| directive_id(name).to_string())
        .collect();
    writeln!(events, "i {}", ids.join(" ")).unwrap();
    let catalog = catalog();
    let mut rng = Rng(0xfac7_0001);
    let mut models = catalog.clone();
    for _ in 0..40 {
        let model = rng.pick(&catalog.iter().collect::<Vec<_>>()).unwrap();
        models.push(with_compat(model, rng.chance(50)));
    }
    let template = catalog
        .iter()
        .find(|model| model.api == "bedrock-converse-stream")
        .unwrap();
    for id in [
        "anthropic.claude-opus-5-5-v2",
        "anthropic.claude-sonnet-6",
        "anthropic.claude-3-haiku-20240307-v1:0",
        "gpt-5.10",
        "gpt-6.2-nova",
        "gemini-4-pro",
        "gemma4-e2b",
        "my-model",
    ] {
        models.push(renamed(template, id));
    }
    let forced = ProviderEnv::from([("AWS_BEDROCK_FORCE_CACHE".to_owned(), "1".to_owned())]);
    let mut transcript = String::new();
    for (at, model) in models.iter().enumerate() {
        let query = Quirks::of(model).query();
        let compat = model
            .compat
            .as_ref()
            .and_then(|compat| compat.as_anthropic_messages())
            .and_then(|compat| compat.force_adaptive_thinking)
            .map_or(2, u8::from);
        let model_target = models_by_id
            .get(query.model)
            .copied()
            .unwrap_or(2_000_000 + at);
        writeln!(
            events,
            "m {} {model_target} {} {compat}",
            index(&families, query.family),
            index(&hosts, query.host)
        )
        .unwrap();
        writeln!(
            transcript,
            "m {} {} {} {} {} {}",
            bit(adaptive_thinking(model)),
            bit(Quirks::of(model).thinking_block_binding().unwrap_or(false)),
            bit(supports_prompt_caching(model, None)),
            bit(supports_prompt_caching(model, Some(&forced))),
            bit(supports_explicit_cache_breakpoints(model)),
            bit(uses_google_thinking_level(model)),
        )
        .unwrap();
    }
    Scenario {
        name: "decisions".to_owned(),
        events,
        transcript,
    }
}

/// The Google budget rule of the family of `model` in the table.
fn google_rule(book: &Value, model: &Model) -> Option<LevelBudgets> {
    let family = Rulebook::shipped()
        .family(&model.id, &model.name)
        .unwrap()?;
    book["rules"]
        .as_array()
        .unwrap()
        .iter()
        .find(|rule| rule["layer"] == "family" && rule["target"] == family)
        .and_then(|rule| rule["set"].get("thinking_budgets"))
        .map(|budgets| serde_json::from_value(budgets.clone()).unwrap())
}

const GOOGLE_LEVELS: [ResolvedGoogleThinkingLevel; 4] = [
    ResolvedGoogleThinkingLevel::Minimal,
    ResolvedGoogleThinkingLevel::Low,
    ResolvedGoogleThinkingLevel::Medium,
    ResolvedGoogleThinkingLevel::High,
];

/// The user's budgets: `custom` at `level`, none elsewhere.
fn customs(level: ResolvedGoogleThinkingLevel, custom: Option<u64>) -> ThinkingBudgets {
    let mut budgets = ThinkingBudgets::default();
    match level {
        ResolvedGoogleThinkingLevel::Minimal => budgets.minimal = custom,
        ResolvedGoogleThinkingLevel::Low => budgets.low = custom,
        ResolvedGoogleThinkingLevel::Medium => budgets.medium = custom,
        ResolvedGoogleThinkingLevel::High => budgets.high = custom,
    }
    budgets
}

fn opt(value: Option<u64>) -> String {
    value.map_or_else(|| "-".to_owned(), |value| value.to_string())
}

/// The wire efforts the model numbers 1 to 6 (`bend/facts.bend` section
/// 3); any other wire string is 9.
const EFFORT_WIRES: [&str; 6] = ["minimal", "low", "medium", "high", "xhigh", "max"];

fn effort_code(wire: &str) -> usize {
    EFFORT_WIRES
        .iter()
        .position(|known| *known == wire)
        .map_or(9, |at| at + 1)
}

const EFFORT_LEVELS: [ThinkingLevel; 6] = [
    ThinkingLevel::Minimal,
    ThinkingLevel::Low,
    ThinkingLevel::Medium,
    ThinkingLevel::High,
    ThinkingLevel::Xhigh,
    ThinkingLevel::Max,
];

#[allow(clippy::too_many_lines)] // one scenario: each problem is a short loop
fn budget_scenario() -> Scenario {
    let book = rulebook();
    let defaults: LevelBudgets =
        serde_json::from_value(book["thinking_defaults"]["budgets"].clone()).unwrap();
    let mut events = format!(
        "d {} {} {} {} {MIN_ANSWER_TOKENS}\n",
        defaults.minimal, defaults.low, defaults.medium, defaults.high
    );
    let mut transcript = String::new();
    let mut rng = Rng(0xfac7_0002);
    // Google budgets.
    let catalog = catalog();
    let google: Vec<Model> = catalog
        .iter()
        .filter(|model| model.api.starts_with("google"))
        .cloned()
        .collect();
    let mut google_models = google.clone();
    for id in [
        "gemini-2.5-flash-lite",
        "gemini-2.5-flash",
        "gemini-2.5-pro",
        "gemini-2.0-flash",
    ] {
        google_models.push(renamed(&google[0], id));
    }
    for model in &google_models {
        let rule = google_rule(&book, model);
        let (
            has,
            LevelBudgets {
                minimal,
                low,
                medium,
                high,
            },
        ) = rule.map_or((0, LevelBudgets::default()), |rule| (1, rule));
        for (at, level) in GOOGLE_LEVELS.into_iter().enumerate() {
            let custom = rng.chance(50).then(|| rng.below(40_000));
            writeln!(
                events,
                "g {has} {minimal} {low} {medium} {high} {at} {}",
                opt(custom)
            )
            .unwrap();
            let budgets = customs(level, custom);
            writeln!(
                transcript,
                "g {}",
                google_thinking_budget(model, level, Some(&budgets))
            )
            .unwrap();
        }
    }
    // The fit under the response ceiling, with each level (xhigh and max
    // take the high budget).
    for _ in 0..300 {
        let base = rng.chance(50).then(|| rng.below(40_000));
        let model_max = rng.range(1, 140_000);
        let level = EFFORT_LEVELS[usize::try_from(rng.below(6)).unwrap()];
        let budget_level = match level {
            ThinkingLevel::Minimal => ResolvedGoogleThinkingLevel::Minimal,
            ThinkingLevel::Low => ResolvedGoogleThinkingLevel::Low,
            ThinkingLevel::Medium => ResolvedGoogleThinkingLevel::Medium,
            ThinkingLevel::High | ThinkingLevel::Xhigh | ThinkingLevel::Max => {
                ResolvedGoogleThinkingLevel::High
            }
        };
        let at = GOOGLE_LEVELS
            .iter()
            .position(|known| *known == budget_level)
            .unwrap();
        let custom = rng.chance(50).then(|| rng.below(60_000));
        writeln!(events, "f {} {model_max} {at} {}", opt(base), opt(custom)).unwrap();
        let fit = adjust_max_tokens_for_thinking(
            base,
            model_max,
            level,
            Some(&customs(budget_level, custom)),
        );
        writeln!(transcript, "f {} {}", fit.max_tokens, fit.thinking_budget).unwrap();
    }
    // The edges of the fit: a ceiling equal to the budget, one above it,
    // one below it.
    for (model_max, custom) in [
        (16_384, None),
        (16_385, None),
        (16_383, None),
        (5_000, Some(5_000)),
    ] {
        writeln!(events, "f - {model_max} 3 {}", opt(custom)).unwrap();
        let budgets = customs(ResolvedGoogleThinkingLevel::High, custom);
        let fit =
            adjust_max_tokens_for_thinking(None, model_max, ThinkingLevel::High, Some(&budgets));
        writeln!(transcript, "f {} {}", fit.max_tokens, fit.thinking_budget).unwrap();
    }
    // The answer room and the auxiliary cap.
    for _ in 0..100 {
        let (budget, ceiling) = (rng.below(40_000), rng.below(40_000));
        writeln!(events, "o {budget} {ceiling}").unwrap();
        writeln!(
            transcript,
            "o {}",
            clamp_thinking_budget_to_answer_room(budget, ceiling)
        )
        .unwrap();
        writeln!(events, "x {budget}").unwrap();
        writeln!(
            transcript,
            "x {}",
            thinking_output_cap(budget, MIN_ANSWER_TOKENS)
        )
        .unwrap();
    }
    // The Bedrock effort from the thinking-level map.
    let bedrock: Vec<Model> = catalog
        .iter()
        .filter(|model| model.api == "bedrock-converse-stream")
        .cloned()
        .collect();
    let mut no_xhigh = bedrock
        .iter()
        .find(|model| model.id == "anthropic.claude-opus-4-7")
        .unwrap()
        .clone();
    if let Some(map) = no_xhigh.thinking_level_map.as_mut() {
        map.insert(ModelThinkingLevel::Xhigh, None);
    }
    let mut efforts = bedrock;
    efforts.push(no_xhigh);
    for model in &efforts {
        let map = thinking_level_map(model);
        let entries: Vec<String> = EFFORT_LEVELS
            .iter()
            .map(
                |level| match map.and_then(|map| map.get(&ModelThinkingLevel::from(*level))) {
                    None => "-".to_owned(),
                    Some(None) => "n".to_owned(),
                    Some(Some(wire)) => effort_code(wire).to_string(),
                },
            )
            .collect();
        for (at, level) in EFFORT_LEVELS.into_iter().enumerate() {
            writeln!(events, "e {at} {}", entries.join(" ")).unwrap();
            writeln!(
                transcript,
                "e {}",
                effort_code(&map_thinking_level_to_effort(model, level))
            )
            .unwrap();
        }
    }
    // The default budgets are the old Bedrock table (1024, 2048, 8192,
    // 16384).
    events.push_str("s\n");
    let shipped = Rulebook::shipped().thinking_defaults().budgets;
    writeln!(
        transcript,
        "s {}",
        bit(shipped
            == LevelBudgets {
                minimal: 1024,
                low: 2048,
                medium: 8192,
                high: 16384,
            })
    )
    .unwrap();
    Scenario {
        name: "budgets".to_owned(),
        events,
        transcript,
    }
}

/// The tiers the price scenario asks, numbered from 1 in this order.
const TIERS: [&str; 7] = [
    "flex", "priority", "fast", "auto", "scale", "default", "unknown",
];

/// `price` in units of `1 / scale`, rounded.
#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)] // small, non-negative prices
fn scaled(price: f64, scale: f64) -> u64 {
    (price * scale).round() as u64
}

/// A multiplier in hundredths (every shipped multiplier is a whole number
/// of them).
fn hundredths(multiplier: f64) -> u64 {
    scaled(multiplier, 100.0)
}

/// A rate in ten-thousandths of a dollar per million tokens.
fn rate(rate: f64) -> u64 {
    scaled(rate, 10_000.0)
}

fn price_scenario() -> Scenario {
    let book = rulebook();
    let rows = book["service_tier_prices"].as_array().unwrap();
    let catalog = catalog();
    let mut events = String::new();
    let mut transcript = String::new();
    let mut groups: Vec<(String, String)> = catalog
        .iter()
        .filter(|model| model.api.starts_with("openai") || model.api.starts_with("azure"))
        .map(|model| (model.provider.clone(), model.api.clone()))
        .collect();
    groups.sort();
    groups.dedup();
    for (provider, api) in groups {
        let group: Vec<&Model> = catalog
            .iter()
            .filter(|model| model.provider == provider && model.api == api)
            .collect();
        let mut numbers: HashMap<String, usize> = HashMap::new();
        events.push_str("q\n");
        for row in rows
            .iter()
            .filter(|row| row["provider"] == provider.as_str() && row["api"] == api.as_str())
        {
            let model = row["model"].as_str().map_or_else(
                || "-".to_owned(),
                |id| {
                    let next = numbers.len();
                    numbers.entry(id.to_owned()).or_insert(next).to_string()
                },
            );
            let multiplier = hundredths(row["multiplier"].as_f64().unwrap());
            for tier in row["tiers"].as_array().unwrap() {
                let tier = TIERS
                    .iter()
                    .position(|known| *known == tier.as_str().unwrap())
                    .unwrap()
                    + 1;
                writeln!(events, "w {model} {tier} {multiplier}").unwrap();
            }
        }
        for (at, model) in group.iter().enumerate() {
            let number = numbers.get(&model.id).copied().unwrap_or(1000 + at);
            for (tier_at, tier) in TIERS.iter().enumerate() {
                writeln!(events, "t {number} {}", tier_at + 1).unwrap();
                writeln!(
                    transcript,
                    "t {}",
                    opt(service_tier_multiplier((*model).into(), tier).map(hundredths))
                )
                .unwrap();
            }
        }
    }
    // The 1h cache write rate of each model without request-wide tiers
    // whose rates are whole ten-thousandths.
    let whole = |price: f64| (price * 10_000.0).fract() == 0.0;
    for model in catalog
        .iter()
        .filter(|model| model.cost.tiers.is_none())
        .filter(|model| whole(model.cost.input) && whole(model.cost.cache_write))
    {
        let row = cache_write_1h_multiplier(&model.id).map(hundredths);
        writeln!(
            events,
            "h {} {} {}",
            opt(row),
            rate(model.cost.input),
            rate(model.cost.cache_write)
        )
        .unwrap();
        let mut usage = Usage {
            cache_write: 1_000_000,
            cache_write_1h: Some(1_000_000),
            ..Usage::default()
        };
        writeln!(
            transcript,
            "h {}",
            rate(calculate_cost(model, &mut usage).cache_write)
        )
        .unwrap();
    }
    Scenario {
        name: "prices".to_owned(),
        events,
        transcript,
    }
}

#[test]
fn the_rust_model_facts_equal_the_bend_model() {
    compare(
        "bend/bridge_facts.bend",
        [decision_scenario(), budget_scenario(), price_scenario()],
    );
}
