//! Port of `api/simple-options.ts`: mapping `streamSimple` options onto the
//! shared stream options and thinking-budget arithmetic.

use eukhe_types::pi_ai::{
    Model, ModelThinkingLevel, SamplingParams, ThinkingBudgets, ThinkingLevel, TranscriptContext,
};

use crate::models::clamp_thinking_level;
use crate::types::{SimpleStreamOptions, StreamOptions};
use crate::utils::estimate::estimate_context_tokens;

const CONTEXT_SAFETY_TOKENS: i128 = 4096;
const MIN_MAX_TOKENS: u64 = 1;

/// Cap `max_tokens` to what fits in the context window after the estimated
/// prompt and a safety margin (never below 1).
#[must_use]
pub fn clamp_max_tokens_to_context(
    model: &Model,
    context: &TranscriptContext,
    max_tokens: u64,
) -> u64 {
    if model.context_window == 0 {
        return max_tokens.max(MIN_MAX_TOKENS);
    }
    let available = i128::from(model.context_window)
        - i128::from(estimate_context_tokens(context.messages()).tokens)
        - CONTEXT_SAFETY_TOKENS;
    let available = u64::try_from(available.max(i128::from(MIN_MAX_TOKENS))).unwrap_or(u64::MAX);
    max_tokens.min(available)
}

/// Merge model, thinking-level, and request sampling params (later wins per
/// key); `None` when none of the three is present.
#[must_use]
pub fn resolve_sampling_params(
    model: &Model,
    thinking_level: ModelThinkingLevel,
    request_params: Option<&SamplingParams>,
) -> Option<SamplingParams> {
    let effective = clamp_thinking_level(model, thinking_level);
    let thinking_level_params = model
        .sampling_params_by_thinking_level
        .as_ref()
        .and_then(|by_level| by_level.get(&effective));
    let sources = [
        model.sampling_params.as_ref(),
        thinking_level_params,
        request_params,
    ];
    if sources.iter().all(Option::is_none) {
        return None;
    }
    let mut merged = SamplingParams::new();
    for source in sources.into_iter().flatten() {
        for (key, value) in source {
            merged.insert(key.clone(), value.clone());
        }
    }
    Some(merged)
}

/// TS `buildBaseOptions`: the shared stream options of a `streamSimple`
/// call, with resolved sampling params, context-clamped `max_tokens`, and
/// `api_key` taking precedence when non-empty.
///
/// Every other field is copied from `options.stream`; this includes the
/// eukhe addition `service_tier`.
#[must_use]
pub fn build_base_options(
    model: &Model,
    context: &TranscriptContext,
    options: Option<&SimpleStreamOptions>,
    api_key: Option<&str>,
) -> StreamOptions {
    let mut base = options
        .map(|options| options.stream.clone())
        .unwrap_or_default();
    let reasoning = options
        .and_then(|options| options.reasoning)
        .map_or(ModelThinkingLevel::Off, ModelThinkingLevel::from);
    base.sampling_params = resolve_sampling_params(model, reasoning, base.sampling_params.as_ref());
    base.max_tokens = Some(clamp_max_tokens_to_context(
        model,
        context,
        base.max_tokens.unwrap_or(model.max_tokens),
    ));
    if let Some(api_key) = api_key.filter(|key| !key.is_empty()) {
        base.request.api_key = Some(api_key.to_owned());
    }
    base
}

/// Tokens always left for the answer when a thinking budget shares the response ceiling.
pub const MIN_ANSWER_TOKENS: u64 = 1024;

/// TS `DEFAULT_THINKING_BUDGETS`.
pub const DEFAULT_THINKING_BUDGETS: ThinkingBudgets = ThinkingBudgets {
    minimal: Some(1024),
    low: Some(2048),
    medium: Some(8192),
    high: Some(16384),
};

/// Map `xhigh`/`max` to `high`; other levels unchanged.
#[must_use]
pub fn clamp_reasoning(effort: Option<ThinkingLevel>) -> Option<ThinkingLevel> {
    match effort {
        Some(ThinkingLevel::Xhigh | ThinkingLevel::Max) => Some(ThinkingLevel::High),
        other => other,
    }
}

/// Token budget of a thinking level, custom budgets over the defaults.
#[must_use]
pub fn thinking_budget_for_level(
    reasoning_level: ThinkingLevel,
    custom_budgets: Option<&ThinkingBudgets>,
) -> u64 {
    let custom = custom_budgets.cloned().unwrap_or_default();
    let defaults = DEFAULT_THINKING_BUDGETS;
    let (custom_value, default_value) = match clamp_reasoning(Some(reasoning_level)) {
        Some(ThinkingLevel::Minimal) => (custom.minimal, defaults.minimal),
        Some(ThinkingLevel::Low) => (custom.low, defaults.low),
        Some(ThinkingLevel::Medium) => (custom.medium, defaults.medium),
        Some(ThinkingLevel::High | ThinkingLevel::Xhigh | ThinkingLevel::Max) | None => {
            (custom.high, defaults.high)
        }
    };
    custom_value.or(default_value).unwrap_or_default()
}

/// Cap a thinking budget so at least [`MIN_ANSWER_TOKENS`] remain under a shared response ceiling.
#[must_use]
pub fn clamp_thinking_budget_to_answer_room(thinking_budget: u64, ceiling: u64) -> u64 {
    thinking_budget.min(ceiling.saturating_sub(MIN_ANSWER_TOKENS))
}

/// Result of [`adjust_max_tokens_for_thinking`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ThinkingTokens {
    pub max_tokens: u64,
    pub thinking_budget: u64,
}

/// Fit a thinking budget inside the response ceiling. `base_max_tokens`
/// `None` means no explicit caller cap: use the model cap and fit thinking
/// inside it.
#[must_use]
pub fn adjust_max_tokens_for_thinking(
    base_max_tokens: Option<u64>,
    model_max_tokens: u64,
    reasoning_level: ThinkingLevel,
    custom_budgets: Option<&ThinkingBudgets>,
) -> ThinkingTokens {
    let mut thinking_budget = thinking_budget_for_level(reasoning_level, custom_budgets);
    let max_tokens = base_max_tokens.map_or(model_max_tokens, |base| {
        base.saturating_add(thinking_budget).min(model_max_tokens)
    });
    if max_tokens <= thinking_budget {
        thinking_budget = clamp_thinking_budget_to_answer_room(thinking_budget, max_tokens);
    }
    ThinkingTokens {
        max_tokens,
        thinking_budget,
    }
}
