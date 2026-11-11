//! The `thinking` / `output_config` forms of the shipped Anthropic Messages
//! models match what omp sends for the same model and level (omp
//! `packages/ai/src/providers/anthropic.ts` `buildParams`, its catalog's
//! thinking facts).

mod anthropic_support;

use anthropic_support::{builtin_model, capture_simple_payload};
use eukhe_ai::types::SimpleStreamOptions;
use eukhe_types::pi_ai::ThinkingLevel;
use serde_json::{json, Value as JsonValue};

/// The `thinking` and `output_config` fields `stream_simple` sends for the
/// built-in `provider`/`id` at `level` (`None`: thinking off).
async fn wire(provider: &str, id: &str, level: Option<ThinkingLevel>) -> [JsonValue; 2] {
    let options = SimpleStreamOptions {
        reasoning: level,
        ..SimpleStreamOptions::default()
    };
    let payload = capture_simple_payload(&builtin_model(provider, id, &json!({})), options).await;
    ["thinking", "output_config"].map(|key| payload.get(key).cloned().unwrap_or(JsonValue::Null))
}

/// omp sends `thinking.display` on adaptive thinking only where the model
/// accepts it, adaptive Claude 4.7 and later (its catalog's
/// `supportsDisplay`, `compat/resolve.ts` `defaultSupportsDisplay`;
/// `anthropic.ts` "Opus 4.6 / Sonnet 4.6+ reject it with a 400"). Budget
/// thinking keeps it.
#[tokio::test]
async fn adaptive_thinking_display_rides_on_claude_4_7_and_later_only() {
    let high = Some(ThinkingLevel::High);
    let adaptive = json!({ "type": "adaptive" });
    let summarized = json!({ "type": "adaptive", "display": "summarized" });
    assert_eq!(
        [
            wire("anthropic", "claude-opus-4-6", high).await,
            wire("github-copilot", "claude-sonnet-4.6", high).await,
            wire("vercel-ai-gateway", "anthropic/claude-opus-4.6", high).await,
            wire("kimi-coding", "k3", high).await,
            wire("opencode", "claude-opus-4-7", high).await,
            wire("anthropic", "claude-sonnet-4-5", high).await,
        ],
        [
            [adaptive.clone(), json!({ "effort": "high" })],
            [adaptive.clone(), json!({ "effort": "high" })],
            [adaptive.clone(), json!({ "effort": "high" })],
            [adaptive, json!({ "effort": "high" })],
            [summarized, json!({ "effort": "high" })],
            [
                json!({ "type": "enabled", "budget_tokens": 16384, "display": "summarized" }),
                JsonValue::Null
            ],
        ]
    );
}
