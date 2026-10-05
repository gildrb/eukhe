//! Anthropic prompt-cache pricing helpers.
//! Ported from `packages/ai/src/cache-pricing.ts`.

use crate::types::Model;

pub const ANTHROPIC_FIVE_MINUTE_CACHE_WRITE_COST_MULTIPLIER: f64 = 1.25;
pub const ANTHROPIC_ONE_HOUR_CACHE_WRITE_COST_MULTIPLIER: f64 = 2.0;

/// Anthropic `cache_creation` usage block carried on the wire.
#[derive(Debug, Clone, Copy, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct AnthropicCacheCreationUsage {
    #[serde(rename = "ephemeral_5m_input_tokens", default)]
    pub ephemeral_5m_input_tokens: u64,
    #[serde(rename = "ephemeral_1h_input_tokens", default)]
    pub ephemeral_1h_input_tokens: u64,
}

#[must_use]
pub fn has_standard_anthropic_cache_pricing(model: &Model) -> bool {
    let model_id = model.id.to_lowercase();
    let is_anthropic_model = model.provider == "anthropic"
        || model_id.starts_with("anthropic/")
        || model_id.starts_with("claude-");
    if !is_anthropic_model {
        return false;
    }
    let expected_cache_write_cost =
        model.cost.input.as_f64() * ANTHROPIC_FIVE_MINUTE_CACHE_WRITE_COST_MULTIPLIER;
    let tolerance = f64::EPSILON
        * (1.0f64)
            .max(model.cost.cache_write.as_f64())
            .max(expected_cache_write_cost);
    (model.cost.cache_write.as_f64() - expected_cache_write_cost).abs() <= tolerance
}

/// The per-token cache-write cost. Requests write 5-minute entries only; a
/// reported `cache_creation` split still prices any 1-hour tokens at their
/// own rate.
#[must_use]
pub fn get_anthropic_cache_write_cost(
    input_cost: f64,
    cache_creation: Option<&AnthropicCacheCreationUsage>,
) -> f64 {
    let five_minute_cost = input_cost * ANTHROPIC_FIVE_MINUTE_CACHE_WRITE_COST_MULTIPLIER;
    let Some(creation) = cache_creation else {
        return five_minute_cost;
    };
    // Token counts sit far below f64's 2^53 exact-integer range; the cost math is f64 by design.
    #[allow(clippy::cast_precision_loss)]
    let five_minute_tokens = creation.ephemeral_5m_input_tokens as f64;
    #[allow(clippy::cast_precision_loss)]
    let one_hour_tokens = creation.ephemeral_1h_input_tokens as f64;
    let total_tokens = five_minute_tokens + one_hour_tokens;
    if total_tokens == 0.0 {
        return five_minute_cost;
    }
    input_cost
        * (five_minute_tokens * ANTHROPIC_FIVE_MINUTE_CACHE_WRITE_COST_MULTIPLIER
            + one_hour_tokens * ANTHROPIC_ONE_HOUR_CACHE_WRITE_COST_MULTIPLIER)
        / total_tokens
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blended_cache_write_cost() {
        let usage = AnthropicCacheCreationUsage {
            ephemeral_5m_input_tokens: 1000,
            ephemeral_1h_input_tokens: 3000,
        };
        // TS formula: inputCost * (5m*1.25 + 1h*2) / total = 10*(1250+6000)/4000 = 18.125.
        let cost = get_anthropic_cache_write_cost(10.0, Some(&usage));
        assert!((cost - 18.125).abs() < 1e-9);
    }
}
