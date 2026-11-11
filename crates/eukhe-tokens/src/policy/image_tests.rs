//! omp `packages/catalog/test/image-tokenization.test.ts` and
//! `packages/agent/test/image-tokens.test.ts`. omp's `getBundledModel(…)`
//! targets are spelled out as the bundled row's `{ provider, id, api }`.

use super::*;

const HIRES: ImageTokenization = anthropic(2576, 4784, true);
/// The Anthropic-wire fallback: the high-res numbers, unmeasured.
const HIRES_FALLBACK: ImageTokenization = anthropic(2576, 4784, false);
const STANDARD: ImageTokenization = CLAUDE_STANDARD;
const GPT_PATCH: ImageTokenization = GPT_5_5;
const DEEPSEEK_PATCH: ImageTokenization = DEEPSEEK_V4_1_FLASH;
const FIXED_1120: ImageTokenization = ImageTokenization::Fixed {
    tokens: 1120,
    verified: false,
};

fn resolve(provider: &str, id: &str, api: &str) -> Option<ImageTokenization> {
    resolve_image_tokenization(ModelRef { id, provider, api })
}

fn rule_for(provider: &str, id: &str) -> ImageTokenization {
    resolve(provider, id, "").unwrap_or_else(|| panic!("no image rule for {provider}/{id}"))
}

fn tokens(rule: &ImageTokenization, width: u32, height: u32, detail: Option<ImageDetail>) -> u64 {
    image_tokens(rule, ImageSize { width, height }, detail)
}

fn verified(rule: &ImageTokenization) -> bool {
    match *rule {
        ImageTokenization::OpenAiPatch { verified, .. }
        | ImageTokenization::AnthropicPatch { verified, .. }
        | ImageTokenization::DeepSeekPatch { verified, .. }
        | ImageTokenization::Fixed { verified, .. } => verified,
    }
}

fn is_gpt_patch_1_2(rule: &ImageTokenization) -> bool {
    matches!(rule, ImageTokenization::OpenAiPatch { multiplier, .. } if (multiplier - 1.2).abs() < f64::EPSILON)
}

#[test]
fn splits_claude_at_4_7() {
    for id in [
        "claude-opus-4-6",
        "claude-haiku-4-5",
        "claude-3-5-sonnet-20241022",
        "claude-sonnet-45",
    ] {
        assert_eq!(resolve("anthropic", id, ""), Some(STANDARD), "{id}");
    }
    for id in ["claude-sonnet-4-6", "claude-sonnet-46"] {
        assert_eq!(
            resolve("anthropic", id, ""),
            Some(CLAUDE_STANDARD_VERIFIED),
            "{id}"
        );
    }
    for id in [
        "claude-opus-4-7",
        "claude-opus-5-5",
        "claude-sonnet-5-5",
        "claude-fable-5-1",
        "claude-fable-latest",
        "claude-mythos-preview",
    ] {
        assert_eq!(resolve("anthropic", id, ""), Some(HIRES), "{id}");
    }
    // Separator-collapsed revisions parse as two digits: `claude-opus-45` is
    // Opus 4.5 (standard), `claude-opus-47` is Opus 4.7 (high-res).
    assert_eq!(resolve("anthropic", "claude-opus-45", ""), Some(STANDARD));
    assert_eq!(resolve("anthropic", "claude-opus-47", ""), Some(HIRES));
}

#[test]
fn prices_unversioned_claude_aliases_at_the_high_res_tier() {
    assert_eq!(resolve("anthropic", "claude-opus-latest", ""), Some(HIRES));
    assert_eq!(
        resolve("anthropic", "claude-sonnet-latest", ""),
        Some(HIRES)
    );
    for (provider, id, api) in [
        ("openrouter", "~anthropic/claude-opus-latest", "openrouter"),
        (
            "openrouter",
            "~anthropic/claude-sonnet-latest",
            "openrouter",
        ),
        (
            "kilo",
            "~anthropic/claude-opus-latest",
            "openai-completions",
        ),
        (
            "kilo",
            "~anthropic/claude-sonnet-latest",
            "openai-completions",
        ),
        (
            "nanogpt",
            "anthropic/claude-opus-latest",
            "openai-completions",
        ),
        (
            "nanogpt",
            "anthropic/claude-sonnet-latest",
            "openai-completions",
        ),
    ] {
        assert_eq!(resolve(provider, id, api), Some(HIRES), "{provider}/{id}");
    }
}

#[test]
fn follows_the_claude_lineage_through_gateways_and_cloud_hosts() {
    assert_eq!(
        resolve(
            "openrouter",
            "anthropic/claude-opus-4.7",
            "openai-completions"
        ),
        Some(HIRES)
    );
    assert_eq!(
        resolve(
            "openrouter",
            "anthropic/claude-sonnet-4.6",
            "openai-completions"
        ),
        Some(CLAUDE_STANDARD_VERIFIED)
    );
    assert_eq!(
        resolve(
            "amazon-bedrock",
            "us.anthropic.claude-opus-4-7-v1:0",
            "bedrock-converse-stream"
        ),
        Some(HIRES)
    );
    assert_eq!(
        resolve("google-vertex", "claude-fable-5@20250929", "google-vertex"),
        Some(HIRES)
    );
}

#[test]
fn prices_every_current_codex_model_with_32px_patches_times_1_2() {
    for id in [
        "gpt-6-astra",
        "gpt-6.1-sol",
        "gpt-5.6-luna",
        "gpt-5.5",
        "gpt-daybreak-blue-latest",
        "gpt-5.3-codex",
    ] {
        let rule = rule_for("openai-codex", id);
        assert!(is_gpt_patch_1_2(&rule), "{id}: {rule:?}");
        assert_eq!(
            tokens(&rule, 1568, 1562, Some(ImageDetail::Original)),
            2882,
            "{id}"
        );
    }
}

#[test]
fn marks_the_gpt_rules_measured_against_codex_billing_as_verified() {
    for id in [
        "gpt-6-astra",
        "gpt-6.1-sol",
        "gpt-5.6-luna",
        "gpt-5.5",
        "gpt-daybreak-blue-latest",
    ] {
        assert!(verified(&rule_for("openai-codex", id)), "{id}");
    }
    // gpt-5.4 and older follow the guide without a billing probe.
    assert!(!verified(&rule_for("openai", "gpt-5.4")));
    assert!(!verified(&rule_for("openai-codex", "gpt-5.3-codex")));
    // Lines after 6.1 size like gpt-5.6 but are not measured yet.
    for id in ["gpt-6.2-sol", "gpt-7-luna"] {
        let rule = rule_for("openai-codex", id);
        assert!(!verified(&rule), "{id}");
        assert_eq!(
            tokens(&rule, 1568, 1562, Some(ImageDetail::Original)),
            2882,
            "{id}"
        );
    }
}

#[test]
fn marks_the_gemini_sonnet_and_grok_rules_measured_on_antigravity_and_xai_as_verified() {
    // Cloud Code Assist bills every Gemini image 1,089 tokens; Google's own
    // API keeps the documented 1,120.
    for id in [
        "gemini-2.5-flash-lite",
        "gemini-3.1-flash-lite",
        "gemini-3.8-flash",
    ] {
        assert_eq!(
            rule_for("google-antigravity", id),
            ImageTokenization::Fixed {
                tokens: 1089,
                verified: true
            },
            "{id}"
        );
    }
    assert_eq!(rule_for("google", "gemini-3.8-flash"), FIXED_1120);
    // Sonnet's standard tier is verified on every host; Opus 4.6 is not measured.
    assert_eq!(
        rule_for("google-antigravity", "claude-sonnet-4-6"),
        CLAUDE_STANDARD_VERIFIED
    );
    assert!(verified(&rule_for("anthropic", "claude-sonnet-4-6")));
    assert!(!verified(&rule_for(
        "google-antigravity",
        "claude-opus-4-6"
    )));
    // Grok 4.6 through 4.20 bill 32px patches resized past 2,401, plus a few
    // tokens per image.
    for (provider, id) in [
        ("xai-oauth", "grok-4.6"),
        ("xai-oauth", "grok-4.7"),
        ("xai-oauth", "grok-4.20-0309-non-reasoning"),
        ("xai", "grok-4.20-0309-reasoning"),
    ] {
        let rule = rule_for(provider, id);
        assert!(verified(&rule), "{provider}/{id}");
        assert_eq!(tokens(&rule, 1568, 1562, Some(ImageDetail::Original)), 2442);
        assert_eq!(tokens(&rule, 2048, 2048, Some(ImageDetail::Original)), 2442);
    }
    // Older Grok lines keep the wire's unverified GPT pricing.
    assert_eq!(
        resolve("xai-oauth", "grok-4.5", "openai-responses"),
        Some(GPT_PATCH)
    );
}

#[test]
fn sizes_each_detail_level_the_way_the_guide_lists_for_that_model() {
    let astra = rule_for("openai", "gpt-6-astra");
    // Guide example: astra `high` keeps a 4096×512 image (65,535px limit).
    assert_eq!(tokens(&astra, 4096, 512, Some(ImageDetail::High)), 2458);
    // Astra `original` has no resizing budget; gpt-5.5 caps at 10,000 patches.
    assert_eq!(
        tokens(&astra, 4096, 4096, Some(ImageDetail::Original)),
        19_661
    );
    assert_eq!(
        tokens(
            &rule_for("openai", "gpt-5.5"),
            4096,
            4096,
            Some(ImageDetail::Original)
        ),
        12_000
    );
    // gpt-5.6 `high` fits 2048px first.
    assert_eq!(
        tokens(
            &rule_for("openai", "gpt-5.6-sol"),
            4096,
            512,
            Some(ImageDetail::High)
        ),
        615
    );
    // gpt-5.4 sizes `auto` like `high` (2,500 patches).
    let gpt54 = rule_for("openai", "gpt-5.4-mini");
    assert_eq!(tokens(&gpt54, 1932, 1920, None), 2940);
    assert_eq!(
        tokens(&gpt54, 1932, 1920, Some(ImageDetail::Original)),
        4392
    );
}

#[test]
fn bills_gemini_3_a_fixed_budget_and_leaves_unruled_lines_without_a_wire_to_the_caller() {
    assert_eq!(resolve("google", "gemini-3.5-flash", ""), Some(FIXED_1120));
    assert_eq!(resolve("google", "gemini-2.5-pro", ""), None);
    assert_eq!(resolve("openrouter", "moonshotai/kimi-k2.6", ""), None);
    for id in [
        "gpt-5.1-codex-max",
        "gpt-5.1",
        "gpt-5-mini",
        "gpt-4.1",
        "gpt-4o",
        "o3",
    ] {
        assert_eq!(resolve("openai", id, ""), None, "{id}");
    }
}

#[test]
fn falls_back_to_the_wire_apis_rule_when_the_lineage_has_none() {
    for api in OPENAI_WIRES {
        assert_eq!(resolve("", "", api), Some(GPT_PATCH), "{api}");
        assert_eq!(
            resolve("openrouter", "moonshotai/kimi-k2.6", api),
            Some(GPT_PATCH),
            "{api}"
        );
    }
    for api in ["google-generative-ai", "google-gemini-cli", "google-vertex"] {
        assert_eq!(
            resolve("google", "gemini-2.5-pro", api),
            Some(FIXED_1120),
            "{api}"
        );
    }
    for api in [
        "anthropic-messages",
        "bedrock-converse-stream",
        "openrouter",
        "ollama-chat",
    ] {
        assert_eq!(
            resolve("", "qwen/qwen3-vl", api),
            Some(HIRES_FALLBACK),
            "{api}"
        );
    }
    // Grok has no lineage rule: xAI's OpenAI-compatible wire prices it as GPT.
    assert_eq!(
        resolve("xai", "grok-4", "openai-responses"),
        Some(GPT_PATCH)
    );
    // The lineage rule wins over the wire carrying it.
    assert_eq!(
        resolve(
            "openrouter",
            "anthropic/claude-opus-4.6",
            "openai-completions"
        ),
        Some(STANDARD)
    );
    assert_eq!(
        resolve("", "gemini-3.5-flash", "anthropic-messages"),
        Some(FIXED_1120)
    );
    // An unregistered API carries no rule.
    assert_eq!(resolve("", "qwen/qwen3-vl", "some-future-api"), None);
}

#[test]
fn keeps_separator_collapsed_gpt_revisions_off_the_gpt_5_6_sizing() {
    for id in [
        "openai-gpt-52-codex",
        "openai-gpt-53-codex",
        "openai-gpt-54",
        "openai-gpt-55",
    ] {
        assert_eq!(
            resolve("venice", id, "openai-completions"),
            Some(GPT_PATCH),
            "{id}"
        );
    }
}

#[test]
fn uses_the_models_identity() {
    // omp's second case swaps a built model's `identity`; a `ModelRef` is
    // always classified from its id.
    assert_eq!(
        resolve("anthropic", "claude-opus-4-6", "anthropic-messages"),
        Some(STANDARD)
    );
}

#[test]
fn prices_deepseek_v4_1_flash_by_its_own_vision_config_on_every_host() {
    for (provider, id, api) in [
        (
            "openrouter",
            "deepseek/deepseek-v4.1-flash-1017",
            "openrouter",
        ),
        ("openrouter", "deepseek/deepseek-v4.1-flash", "openrouter"),
        ("deepseek", "deepseek-flash", "openai-completions"),
        // DeepSeek's API serves the retired preview id with the current Flash.
        (
            "deepseek",
            "deepseek-v4-flash-vision-exp",
            "openai-completions",
        ),
        ("fireworks", "deepseek-v4.1-flash", "openai-completions"),
        (
            "together",
            "deepseek-ai/DeepSeek-V4.1-Flash",
            "openai-completions",
        ),
    ] {
        assert_eq!(
            resolve(provider, id, api),
            Some(DEEPSEEK_PATCH),
            "{provider}/{id}"
        );
    }
    // Hosts still running the V4.0 vision preview keep their wire fallback.
    assert_eq!(
        resolve(
            "openrouter",
            "deepseek/deepseek-v4-flash-vision-exp",
            "openrouter"
        ),
        Some(HIRES_FALLBACK)
    );
    assert_eq!(
        resolve(
            "fireworks",
            "deepseek-v4-flash-vision-exp",
            "openai-completions"
        ),
        Some(GPT_PATCH)
    );
    // An unmeasured later Flash release is not priced by V4.1's rule.
    assert_eq!(
        resolve("fireworks", "deepseek-v4.2-flash", "openai-completions"),
        Some(GPT_PATCH)
    );
}

#[test]
fn matches_the_per_frame_input_token_deltas_measured_on_live_requests() {
    assert_eq!(
        tokens(&GPT_PATCH, 1568, 1562, Some(ImageDetail::Original)),
        2882
    );
    assert_eq!(
        tokens(&GPT_PATCH, 1932, 1920, Some(ImageDetail::Original)),
        4392
    );
    assert_eq!(
        tokens(&GPT_PATCH, 1932, 1920, Some(ImageDetail::Auto)),
        4392
    );
    // `high` resizes to a 2,500-patch budget; `low` fits 512px.
    assert_eq!(
        tokens(&GPT_PATCH, 1932, 1920, Some(ImageDetail::High)),
        2940
    );
    assert_eq!(tokens(&GPT_PATCH, 1932, 1920, Some(ImageDetail::Low)), 308);
    assert_eq!(tokens(&HIRES, 1932, 1920, None), 4761);
    // The standard tier shrinks to the largest size under its 1,568-token cap.
    assert_eq!(tokens(&STANDARD, 1932, 1920, None), 40 * 39);
    assert_eq!(tokens(&STANDARD, 1568, 1568, None), 39 * 39);
}

#[test]
fn follows_openais_documented_patch_examples() {
    assert_eq!(
        tokens(&GPT_PATCH, 1024, 1024, Some(ImageDetail::High)),
        1229
    );
    assert_eq!(
        tokens(&GPT_PATCH, 2048, 2048, Some(ImageDetail::High)),
        3000
    );
    assert_eq!(
        tokens(&GPT_PATCH, 4096, 512, Some(ImageDetail::Original)),
        2458
    );
}

#[test]
fn resizes_anthropic_images_like_the_reference_implementation() {
    assert_eq!(tokens(&HIRES, 200, 100, None), 8 * 4);
    assert_eq!(tokens(&HIRES, 4000, 4000, None), 69 * 69);
    // Guide examples on the standard tier: A4 scan 1075×1520 → 924×1307,
    // 1920×1080 screenshot → 1456×819.
    assert_eq!(tokens(&STANDARD, 1075, 1520, None), 33 * 47);
    assert_eq!(tokens(&STANDARD, 1920, 1080, None), 52 * 30);
    // Near-square: the short edge follows the original aspect, so 3000×2999
    // lands at 1092×1092 (39²), not 40·39.
    assert_eq!(tokens(&STANDARD, 3000, 2999, None), 39 * 39);
    assert_eq!(tokens(&STANDARD, 2999, 3000, None), 39 * 39);
    assert_eq!(tokens(&FIXED_1120, 2048, 2048, None), 1120);
}

#[test]
fn matches_deepseek_v4_1_flash_billing_measured_through_openrouter() {
    // Input-token delta over a text-only request, identical on Fireworks and
    // DeepInfra: upscaled to the 544² floor, then 42px cells up to the cap.
    for (width, height, expected) in [
        (256, 256, 184),
        (512, 512, 184),
        (784, 784, 382),
        (1024, 1024, 652),
        (1280, 1280, 994),
        (1568, 1562, 994),
        (1568, 784, 743),
        (784, 1568, 762),
        (2576, 1716, 977),
        (3000, 1000, 992),
        (4000, 4000, 994),
    ] {
        assert_eq!(
            tokens(&DEEPSEEK_PATCH, width, height, None),
            expected,
            "{width}x{height}"
        );
    }
}

#[test]
fn resizes_deepseek_images_like_the_reference_processor_at_extreme_aspect_ratios() {
    // Values from `plan_image_grid` in DeepSeek's `inference/image_processor.py`.
    assert_eq!(tokens(&DEEPSEEK_PATCH, 1, 8192, None), 1024);
    assert_eq!(tokens(&DEEPSEEK_PATCH, 8192, 1, None), 1024);
    assert_eq!(tokens(&DEEPSEEK_PATCH, 64, 8192, None), 590);
    assert_eq!(tokens(&DEEPSEEK_PATCH, 8192, 64, None), 396);
    assert_eq!(tokens(&DEEPSEEK_PATCH, 100, 2000, None), 234);
    assert_eq!(tokens(&DEEPSEEK_PATCH, 2000, 100, None), 179);
}

// omp packages/agent/test/image-tokens.test.ts
#[test]
fn billed_tokens_match_openais_documented_patch_examples() {
    let size = |width, height| Some(ImageSize { width, height });
    assert_eq!(
        billed_image_tokens(size(1024, 1024), Some(ImageDetail::High), None),
        1229
    );
    // 4096x4096 patches exceed the 2,500 budget and shrink to 50x50 patches.
    assert_eq!(
        billed_image_tokens(size(2048, 2048), Some(ImageDetail::High), None),
        3000
    );
    assert_eq!(
        billed_image_tokens(size(4096, 512), Some(ImageDetail::Original), None),
        2458
    );
}

#[test]
fn unknown_dimensions_charge_the_detail_levels_full_budget() {
    assert_eq!(
        billed_image_tokens(None, Some(ImageDetail::High), None),
        3000
    );
    assert_eq!(
        billed_image_tokens(None, Some(ImageDetail::Original), None),
        12_000
    );
    assert_eq!(billed_image_tokens(None, None, None), 12_000);
    let empty = Some(ImageSize {
        width: 0,
        height: 768,
    });
    assert_eq!(billed_image_tokens(empty, None, None), 12_000);
    assert_eq!(billed_image_tokens(empty, None, Some(&FIXED_1120)), 1120);
}

#[test]
fn the_default_image_rule_is_the_openai_responses_wires() {
    assert_eq!(resolve("", "", "openai-responses"), Some(GPT_5_5));
}
