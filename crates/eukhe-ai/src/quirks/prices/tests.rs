use std::collections::BTreeMap;

use crate::models::{apply_service_tier_pricing, calculate_cost, CatalogModel};
use crate::quirks::{QuirksError, Rulebook};
use crate::types::{Model, ModelCostRates, Usage, UsageCost};

/// Every model of the compiled catalog.
fn catalog() -> impl Iterator<Item = &'static Model> {
    crate::models_generated::MODELS
        .values()
        .flat_map(|models| models.values())
}

/// The service tiers that the oracle prices: no tier, each tier of
/// [`eukhe_types::ai::ServiceTier`], `fast` (a response value of the `OpenAI`
/// Responses API) and a tier that no API knows.
const TIERS: [Option<&str>; 8] = [
    None,
    Some("auto"),
    Some("default"),
    Some("flex"),
    Some("scale"),
    Some("priority"),
    Some("fast"),
    Some("unknown"),
];

/// The multiplier of the `openai-responses` copy that the
/// `service_tier_prices` table replaced (`openai_responses.rs`), kept here
/// only as an oracle.
fn former_responses_multiplier(model_id: &str, service_tier: Option<&str>) -> f64 {
    match service_tier {
        Some("flex") => 0.5,
        Some("priority" | "fast") => {
            if model_id == "gpt-5.5" {
                2.5
            } else {
                2.0
            }
        }
        _ => 1.0,
    }
}

/// The multiplier of the `openai-codex-responses` copy that the table
/// replaced (`openai_codex_responses/request.rs`), kept here only as an
/// oracle.
fn former_codex_multiplier(model_id: &str, service_tier: Option<&str>) -> f64 {
    match service_tier {
        Some("flex") => 0.5,
        Some("priority") => {
            if model_id == "gpt-5.5" {
                2.5
            } else {
                2.0
            }
        }
        _ => 1.0,
    }
}

/// The cost that the former code gave `usage` (already priced by
/// [`calculate_cost`]) served at `service_tier`: the Responses copy for
/// every `openai-responses` model and for the `openai-completions` models of
/// the `openai` provider, the Codex copy for the `openai-codex-responses`
/// models, no tier price for any other model.
fn former_tier_cost(model: &Model, usage: &Usage, service_tier: Option<&str>) -> UsageCost {
    let multiplier = if model.api == "openai-responses"
        || (model.api == "openai-completions" && model.provider == "openai")
    {
        former_responses_multiplier(&model.id, service_tier)
    } else if model.api == "openai-codex-responses" {
        former_codex_multiplier(&model.id, service_tier)
    } else {
        1.0
    };
    let mut cost = usage.cost;
    // The former table is discrete; 1 was its no-op check.
    #[allow(clippy::float_cmp)]
    if multiplier == 1.0 {
        return cost;
    }
    cost.input *= multiplier;
    cost.output *= multiplier;
    cost.cache_read *= multiplier;
    cost.cache_write *= multiplier;
    cost.total = cost.input + cost.output + cost.cache_read + cost.cache_write;
    cost
}

/// `model` with the provider `provider` and the wire API `api`.
fn served_as(model: &Model, provider: &str, api: &str) -> Model {
    Model {
        provider: provider.to_owned(),
        api: api.to_owned(),
        ..model.clone()
    }
}

/// Every model of the compiled catalog of a wire API that prices service
/// tiers (and Azure, which never did), the `openai` models served over
/// `openai-completions` (a custom model: the catalog has none) and one
/// gateway over `openai-completions`, at every tier of [`TIERS`]: the
/// table changes only the cost of the models of the providers other than
/// `openai` over `openai-responses`, at `flex`, `priority` and `fast`.
/// Those providers do not sell the `OpenAI` tier prices (the request gate
/// of the `service_tiers` table sends them no tier).
#[test]
fn the_tier_prices_change_only_the_providers_that_do_not_sell_them() {
    let apis = [
        "openai-responses",
        "openai-codex-responses",
        "openai-completions",
        "azure-openai-responses",
    ];
    let openai = |id: &str| {
        catalog()
            .find(|model| model.provider == "openai" && model.id == id)
            .unwrap_or_else(|| panic!("the catalog has openai {id}"))
    };
    let crafted = [
        served_as(openai("gpt-5.5"), "openai", "openai-completions"),
        served_as(openai("gpt-5.4"), "openai", "openai-completions"),
        served_as(openai("gpt-5.5"), "my-gateway", "openai-completions"),
    ];
    let mut models: Vec<&Model> = catalog()
        .filter(|model| apis.contains(&model.api.as_str()))
        .collect();
    models.extend(&crafted);
    let mut differences: BTreeMap<(String, String, &str), usize> = BTreeMap::new();
    for model in models {
        let mut base = Usage {
            input: 1_000_000,
            output: 500_000,
            cache_read: 200_000,
            cache_write: 100_000,
            ..Usage::default()
        };
        calculate_cost(model, &mut base);
        for tier in TIERS {
            let mut usage = base;
            if let Some(tier) = tier {
                apply_service_tier_pricing(model, &mut usage, tier);
            }
            if usage.cost != former_tier_cost(model, &base, tier) {
                *differences
                    .entry((
                        model.provider.clone(),
                        model.api.clone(),
                        tier.unwrap_or("none"),
                    ))
                    .or_default() += 1;
            }
        }
    }
    let changed = [
        ("cloudflare-ai-gateway", 25),
        ("github-copilot", 18),
        ("meta", 5),
        ("opencode", 29),
        ("opencode-go", 6),
        ("xai", 4),
    ];
    let expected: BTreeMap<(String, String, &str), usize> = changed
        .into_iter()
        .flat_map(|(provider, count)| {
            ["flex", "priority", "fast"].map(|tier| {
                (
                    (provider.to_owned(), "openai-responses".to_owned(), tier),
                    count,
                )
            })
        })
        .collect();
    assert_eq!(differences, expected);
}

/// The [`calculate_cost`] that the `cache_write_1h_prices` table replaced,
/// kept here only as an oracle, with the rate of a 1h cache write as
/// `long_write_rate` of the selected rates: the former code billed every
/// 1h cache write at 2x the input rate.
#[allow(clippy::cast_precision_loss)] // Token counts are JS numbers: far below 2^53.
fn former_calculate_cost(
    model: &Model,
    usage: &Usage,
    long_write_rate: fn(&ModelCostRates) -> f64,
) -> UsageCost {
    let cost = model.model_cost();
    let input_tokens = usage.input + usage.cache_read + usage.cache_write;
    let mut rates: ModelCostRates = cost.rates();
    let mut matched_threshold: Option<u64> = None;
    for tier in cost.tiers.iter().flatten() {
        if input_tokens > tier.input_tokens_above
            && matched_threshold.is_none_or(|matched| tier.input_tokens_above > matched)
        {
            rates = tier.rates();
            matched_threshold = Some(tier.input_tokens_above);
        }
    }
    let long_write = usage.cache_write_1h.unwrap_or(0) as f64;
    let short_write = usage.cache_write as f64 - long_write;
    let mut result = UsageCost {
        input: (rates.input / 1_000_000.0) * usage.input as f64,
        output: (rates.output / 1_000_000.0) * usage.output as f64,
        cache_read: (rates.cache_read / 1_000_000.0) * usage.cache_read as f64,
        cache_write: (rates.cache_write * short_write + long_write_rate(&rates) * long_write)
            / 1_000_000.0,
        total: 0.0,
    };
    result.total = result.input + result.output + result.cache_read + result.cache_write;
    result
}

/// Every model of the compiled catalog of a wire API that reports 1h
/// cache writes (`anthropic-messages`, `bedrock-converse-stream`), with
/// and without 1h writes: every Claude model (Anthropic's price, which
/// Bedrock and the gateways that resell Claude at Anthropic's list rates
/// charge too) keeps its cost; the other models that change bill their 1h
/// writes at their own cache write rate.
#[test]
fn only_claude_models_keep_the_1h_cache_write_price_of_anthropic() {
    let apis = ["anthropic-messages", "bedrock-converse-stream"];
    let mut claude_differences = Vec::new();
    let mut differences: BTreeMap<String, usize> = BTreeMap::new();
    for model in catalog().filter(|model| apis.contains(&model.api.as_str())) {
        for long_write in [None, Some(0), Some(400_000)] {
            let mut usage = Usage {
                input: 1_000,
                output: 2_000,
                cache_read: 3_000,
                cache_write: 1_000_000,
                cache_write_1h: long_write,
                ..Usage::default()
            };
            let former = former_calculate_cost(model, &usage, |rates| rates.input * 2.0);
            let cost = calculate_cost(model, &mut usage);
            if cost == former {
                continue;
            }
            if model.id.to_lowercase().contains("claude") {
                claude_differences.push((model.provider.clone(), model.id.clone()));
            }
            assert_eq!(
                cost,
                former_calculate_cost(model, &usage, |rates| rates.cache_write),
                "{} {}",
                model.provider,
                model.id
            );
            *differences.entry(model.provider.clone()).or_default() += 1;
        }
    }
    assert_eq!(claude_differences, Vec::new());
    let expected: BTreeMap<String, usize> = [
        ("amazon-bedrock", 111),
        ("fireworks", 14),
        ("kimi-coding", 3),
        ("minimax", 3),
        ("minimax-cn", 3),
        ("opencode", 3),
        ("opencode-go", 4),
        ("vercel-ai-gateway", 228),
    ]
    .into_iter()
    .map(|(provider, count)| (provider.to_owned(), count))
    .collect();
    assert_eq!(differences, expected);
}

/// A rulebook with only `section` beside the required tables.
fn rulebook_with(section: &str) -> Result<Rulebook, Vec<QuirksError>> {
    Rulebook::from_json(&format!(
        r#"{{ "families": [], "hosts": [], "rules": [], {section} }}"#
    ))
}

/// Two rows that price one tier of one provider, API and model, a
/// negative multiplier and a pattern that is not a regex: each table does
/// not load.
#[test]
fn a_price_table_that_is_not_one_price_per_key_does_not_load() {
    let errors: Vec<String> = [
        r#""service_tier_prices": [
            { "provider": "openai", "api": "openai-responses", "tiers": ["flex"], "multiplier": 0.5 },
            { "provider": "openai", "api": "openai-responses", "tiers": ["priority", "flex"], "multiplier": 2.0 }
        ]"#,
        r#""service_tier_prices": [
            { "provider": "openai", "api": "openai-responses", "tiers": ["flex"], "multiplier": -0.5 }
        ]"#,
        r#""cache_write_1h_prices": [{ "match": "claude(", "input_multiplier": 2.0 }]"#,
        r#""cache_write_1h_prices": [{ "match": "claude", "input_multiplier": -2.0 }]"#,
    ]
    .into_iter()
    .map(|section| match rulebook_with(section) {
        Ok(_) => "loads".to_owned(),
        Err(errors) => errors
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join("; "),
    })
    .collect();
    assert_eq!(
        errors,
        [
            "the rulebook is not valid: service_tier_prices: two rows price tier `flex` of \
             openai/openai-responses (model None) at line 4 column 11",
            "the rulebook is not valid: service_tier_prices: the multiplier -0.5 of \
             openai/openai-responses is not a price at line 3 column 11",
            "the rulebook is not valid: cache_write_1h_prices: regex parse error:\n    \
             claude(\n          ^\nerror: unclosed group at line 1 column 120",
            "the rulebook is not valid: cache_write_1h_prices: the multiplier -2 of `claude` \
             is not a price at line 1 column 120",
        ]
    );
}
