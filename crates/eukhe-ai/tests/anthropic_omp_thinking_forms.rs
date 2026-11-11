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

/// Thinking off on an adaptive-only Claude model (Opus/Sonnet 4.6 and
/// later) omits `thinking`, which the API reads as adaptive, and pins the
/// lowest effort (omp `anthropic.ts` `buildParams`, `isAdaptiveOnlyThinking`
/// branch). Haiku 5.5 takes an explicit `disabled` (omp
/// `compat.disabledThinking`), and a budget model keeps `disabled`.
#[tokio::test]
async fn thinking_off_on_adaptive_only_claude_pins_the_lowest_effort() {
    let low = [JsonValue::Null, json!({ "effort": "low" })];
    let disabled = [json!({ "type": "disabled" }), JsonValue::Null];
    assert_eq!(
        [
            wire("anthropic", "claude-opus-4-6", None).await,
            wire("github-copilot", "claude-opus-4.7", None).await,
            wire("cloudflare-ai-gateway", "claude-sonnet-5", None).await,
            wire("vercel-ai-gateway", "anthropic/claude-opus-4.8", None).await,
            wire("opencode", "claude-haiku-5-5", None).await,
            wire("github-copilot", "claude-haiku-5.5", None).await,
            wire("anthropic", "claude-sonnet-4-5", None).await,
        ],
        [
            low.clone(),
            low.clone(),
            low.clone(),
            low,
            disabled.clone(),
            disabled.clone(),
            disabled,
        ]
    );
}

/// Thinking off on Claude Sonnet 5.5, which rejects `disabled`, is its
/// lowest setting `between_tools`, with no effort pinned (omp
/// `anthropic.ts` `buildParams`, `compat.supportsBetweenToolsThinking`).
#[tokio::test]
async fn thinking_off_on_claude_sonnet_5_5_is_between_tools() {
    let between = [json!({ "type": "between_tools" }), JsonValue::Null];
    assert_eq!(
        [
            wire("github-copilot", "claude-sonnet-5.5", None).await,
            wire("opencode", "claude-sonnet-5-5", None).await,
            wire("vercel-ai-gateway", "anthropic/claude-sonnet-5.5", None).await,
        ],
        [between.clone(), between.clone(), between]
    );
}

/// Claude Opus 4.5 thinks on a budget and also takes the level as
/// `output_config.effort`, `minimal` as `low` (omp catalog
/// `classes/anthropic.kdl` `thinking-mode "anthropic-budget-effort"`,
/// `anthropic.ts` `buildParams`, `model-thinking.ts`
/// `mapEffortToAnthropicAdaptiveEffort`). Other budget models take none.
#[tokio::test]
async fn claude_opus_4_5_sends_its_budget_with_the_effort() {
    let budget = |tokens: u64| json!({ "type": "enabled", "budget_tokens": tokens, "display": "summarized" });
    assert_eq!(
        [
            wire("anthropic", "claude-opus-4-5", Some(ThinkingLevel::Minimal)).await,
            wire("opencode", "claude-opus-4-5", Some(ThinkingLevel::Medium)).await,
            wire(
                "vercel-ai-gateway",
                "anthropic/claude-opus-4.5",
                Some(ThinkingLevel::High)
            )
            .await,
            wire("anthropic", "claude-sonnet-4-5", Some(ThinkingLevel::Low)).await,
        ],
        [
            [budget(1024), json!({ "effort": "low" })],
            [budget(8192), json!({ "effort": "medium" })],
            [budget(16384), json!({ "effort": "high" })],
            [budget(2048), JsonValue::Null],
        ]
    );
}

/// `MiniMax` drives thinking with the `thinking.type: adaptive` tag alone:
/// no effort and no display, at every level (omp catalog `effortMap`
/// `"adaptive"`, `anthropic.ts` `usesAdaptiveThinkingTagOnly`); its
/// thinking off stays an explicit `disabled`.
#[tokio::test]
async fn minimax_thinks_by_the_adaptive_tag_alone() {
    let adaptive = [json!({ "type": "adaptive" }), JsonValue::Null];
    assert_eq!(
        [
            wire("minimax", "MiniMax-M2.7", Some(ThinkingLevel::Low)).await,
            wire("minimax-cn", "MiniMax-M3", Some(ThinkingLevel::High)).await,
            wire(
                "vercel-ai-gateway",
                "minimax/minimax-m2.5",
                Some(ThinkingLevel::Medium)
            )
            .await,
            wire("minimax", "MiniMax-M2.7", None).await,
        ],
        [
            adaptive.clone(),
            adaptive.clone(),
            adaptive,
            [json!({ "type": "disabled" }), JsonValue::Null],
        ]
    );
}
