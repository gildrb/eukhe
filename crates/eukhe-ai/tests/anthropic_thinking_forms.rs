//! The `thinking` / `output_config` forms of the shipped Anthropic Messages
//! models: what each model is sent at each thinking level, per the
//! catalog's thinking facts for that model.

mod anthropic_support;

use anthropic_support::{builtin_model, capture_simple_payload};
use eukhe_ai::models::{clamp_thinking_level, get_supported_thinking_levels};
use eukhe_ai::types::SimpleStreamOptions;
use eukhe_types::pi_ai::{ModelThinkingLevel, ThinkingLevel};
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

/// `thinking.display` goes out on adaptive thinking only where the model
/// accepts it, adaptive Claude 4.7 and later (Opus 4.6 and Sonnet 4.6+
/// reject it with a 400). Budget thinking keeps it.
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
/// lowest effort. Haiku 5.5 takes an explicit `disabled` (its compat
/// `disabledThinking`) except on `OpenCode` Go, and a budget model keeps
/// `disabled`.
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
            wire("opencode-go", "claude-haiku-5-5", None).await,
            wire("opencode", "claude-haiku-5-5", None).await,
            wire("github-copilot", "claude-haiku-5.5", None).await,
            wire("anthropic", "claude-sonnet-4-5", None).await,
        ],
        [
            low.clone(),
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

/// `OpenCode` Go's Claude Haiku 5.5 offers efforts up to `xhigh`: `max`
/// runs at `xhigh`.
#[test]
fn opencode_go_claude_haiku_5_5_tops_out_at_xhigh() {
    let model = builtin_model("opencode-go", "claude-haiku-5-5", &json!({}));
    assert_eq!(
        clamp_thinking_level(&model, ModelThinkingLevel::Max),
        ModelThinkingLevel::Xhigh
    );
}

/// Kimi For Coding `HighSpeed` does not think: it offers no level, so every
/// level runs as thinking off, an explicit `disabled`.
#[tokio::test]
async fn kimi_for_coding_highspeed_offers_no_thinking_level() {
    let id = "kimi-for-coding-highspeed";
    let model = builtin_model("kimi-coding", id, &json!({}));
    assert_eq!(
        get_supported_thinking_levels(&model),
        [ModelThinkingLevel::Off]
    );
    assert_eq!(
        wire("kimi-coding", id, None).await,
        [json!({ "type": "disabled" }), JsonValue::Null]
    );
}

/// Vercel AI Gateway's Qwen3 235B and Qwen3 Coder models think on a
/// budget; thinking off is an explicit `disabled`.
#[tokio::test]
async fn vercel_qwen3_235b_and_coder_think_on_a_budget() {
    let budget = json!({ "type": "enabled", "budget_tokens": 2048, "display": "summarized" });
    for id in [
        "alibaba/qwen-3-235b",
        "alibaba/qwen3-coder",
        "alibaba/qwen3-coder-30b-a3b",
        "alibaba/qwen3-coder-next",
    ] {
        assert_eq!(
            [
                wire("vercel-ai-gateway", id, Some(ThinkingLevel::Low)).await,
                wire("vercel-ai-gateway", id, None).await,
            ],
            [
                [budget.clone(), JsonValue::Null],
                [json!({ "type": "disabled" }), JsonValue::Null],
            ],
            "{id}"
        );
    }
}

/// Cloudflare AI Gateway's Claude Fable 5.1 takes per-message effort and
/// binds signed thinking to its prefix: a level sends
/// `thinking.block_binding`.
#[tokio::test]
async fn cloudflare_claude_fable_5_1_binds_thinking_to_its_prefix() {
    assert_eq!(
        wire(
            "cloudflare-ai-gateway",
            "claude-fable-5-1",
            Some(ThinkingLevel::High)
        )
        .await,
        [
            json!({
                "type": "adaptive",
                "display": "summarized",
                "block_binding": { "prefix_mismatch_behavior": "drop_block" },
            }),
            json!({ "effort": "high" }),
        ]
    );
}

/// Thinking off on Claude Sonnet 5.5, which rejects `disabled`, is its
/// lowest setting `between_tools`, with no effort pinned (its compat
/// `supportsBetweenToolsThinking`).
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
/// `output_config.effort`, `minimal` as `low` (its thinking mode
/// `anthropic-budget-effort`). Other budget models take none.
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
/// no effort and no display, at every level (its catalog `effortMap`
/// `"adaptive"`); its
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

/// `MiniMax-M3` answers in at most 128000 tokens on the `MiniMax` hosts: 512K
/// is its pricing-tier boundary, not its output ceiling.
#[tokio::test]
async fn minimax_m3_caps_its_answer_at_128k() {
    let mut caps = Vec::new();
    for provider in ["minimax", "minimax-cn"] {
        let model = builtin_model(provider, "MiniMax-M3", &json!({}));
        let payload = capture_simple_payload(&model, SimpleStreamOptions::default()).await;
        caps.push((model.max_tokens, payload["max_tokens"].clone()));
    }
    assert_eq!(caps, [(128_000, json!(128_000)), (128_000, json!(128_000))]);
}

/// Z.AI's GLM rides its Anthropic endpoint
/// (`https://api.z.ai/api/anthropic`), GLM-5.3-Flash and the high-speed
/// lanes its `OpenAI`-compatible coding endpoint. GLM 5.2 and later think on
/// a budget with the level as the effort; older GLM on a budget alone;
/// thinking off is `disabled`.
#[tokio::test]
async fn zai_glm_rides_the_anthropic_endpoint() {
    let route = |id: &str| {
        let model = eukhe_ai::providers::all::get_builtin_model("zai", id).expect("zai model");
        (model.api, model.base_url)
    };
    let anthropic = || {
        (
            "anthropic-messages".to_owned(),
            "https://api.z.ai/api/anthropic".to_owned(),
        )
    };
    let coding = || {
        (
            "openai-completions".to_owned(),
            "https://api.z.ai/api/coding/paas/v4".to_owned(),
        )
    };
    assert_eq!(
        [
            "glm-4.7",
            "glm-5-turbo",
            "glm-5.2",
            "glm-5.3",
            "glm-5.3-flash",
            "glm-5.2-highspeed",
            "glm-5.3-highspeed",
        ]
        .map(route),
        [
            anthropic(),
            anthropic(),
            anthropic(),
            anthropic(),
            coding(),
            coding(),
            coding(),
        ]
    );
    let budget = |tokens: u64| json!({ "type": "enabled", "budget_tokens": tokens, "display": "summarized" });
    assert_eq!(
        [
            wire("zai", "glm-4.7", Some(ThinkingLevel::High)).await,
            wire("zai", "glm-5.2", Some(ThinkingLevel::High)).await,
            wire("zai", "glm-5.3", Some(ThinkingLevel::Low)).await,
            wire("zai", "glm-5.2", None).await,
        ],
        [
            [budget(16384), JsonValue::Null],
            [budget(16384), json!({ "effort": "high" })],
            [budget(2048), json!({ "effort": "low" })],
            [json!({ "type": "disabled" }), JsonValue::Null],
        ]
    );
}
