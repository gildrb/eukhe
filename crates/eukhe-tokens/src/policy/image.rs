//! Billed input tokens per image, by the catalog's `image-tokenization`
//! rules: a model line's lineage rule (`rules/classes/*.kdl`) applies on
//! every host, a host rule can refine it (`providers/google-antigravity.kdl`),
//! and readers without one fall back to the rule for the wire API carrying
//! the request (`providers/image-tokenization.kdl`, priority -1). Plus the
//! billed estimate for an image of known or unknown pixel size
//! ([`billed_image_tokens`]).
//!
//! The pixel math runs in `f64` exactly as the reference JavaScript does, so
//! every intermediate rounding matches.

use super::ModelRef;
use super::cascade::{ModelSelector, Selector, Target, resolve_axis};
use super::revision::RevisionTerm::{AtLeast, AtMost, Below, Equal};

/// An image's pixel size.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ImageSize {
    pub width: u32,
    pub height: u32,
}

/// `OpenAI` image `detail` levels; `None` where one is taken means the
/// provider default (`Auto`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ImageDetail {
    Auto,
    Low,
    High,
    Original,
}

/// One `OpenAI` `detail` level's sizing: a pixel-dimension limit, then an
/// optional patch budget.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PatchSizing {
    /// Longest side after the pixel-dimension fit.
    pub max_edge: u32,
    /// Resizing patch budget; `None` when the level keeps the image's size.
    pub patch_budget: Option<u32>,
}

/// The `detail` level `auto` (and an omitted `detail`) sizes like.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AutoLevel {
    High,
    Original,
}

/// One model line's image billing rule: the vendor formula and its
/// per-model numbers. `verified`: provider billing was measured to match
/// this rule (unset for docs-only rules and wire fallbacks).
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum ImageTokenization {
    /// `OpenAI` 32px patches × a per-model multiplier, sized per `detail`.
    OpenAiPatch {
        multiplier: f64,
        low: PatchSizing,
        high: PatchSizing,
        original: PatchSizing,
        auto: AutoLevel,
        verified: bool,
    },
    /// Anthropic 28px patches, resized to fit a padded-edge limit and a
    /// visual-token budget.
    AnthropicPatch {
        max_edge: u32,
        max_tokens: u32,
        verified: bool,
    },
    /// `DeepSeek` `ViT` patches merged `downsample`² into one token, plus a
    /// newline per row and two delimiters.
    DeepSeekPatch {
        /// `ViT` patch edge in pixels.
        patch_size: u32,
        /// Patches merged per token along each axis.
        downsample: u32,
        /// Token budget per image, layout tokens included.
        max_tokens: u32,
        /// Smaller images are upscaled to this pixel area.
        min_pixels: u32,
        verified: bool,
    },
    /// A fixed per-image budget regardless of pixels (Gemini 3
    /// `media_resolution`).
    Fixed { tokens: u32, verified: bool },
}

const fn sizing(max_edge: u32) -> PatchSizing {
    PatchSizing {
        max_edge,
        patch_budget: None,
    }
}

const fn budgeted(max_edge: u32, patch_budget: u32) -> PatchSizing {
    PatchSizing {
        max_edge,
        patch_budget: Some(patch_budget),
    }
}

const fn anthropic(max_edge: u32, max_tokens: u32, verified: bool) -> ImageTokenization {
    ImageTokenization::AnthropicPatch {
        max_edge,
        max_tokens,
        verified,
    }
}

/// Claude's standard tier: 1,568px edges, 1,568 visual tokens.
const CLAUDE_STANDARD: ImageTokenization = anthropic(1568, 1568, false);
const CLAUDE_STANDARD_VERIFIED: ImageTokenization = anthropic(1568, 1568, true);

/// GPT-5.5's sizing (`auto` sizes like `original`), unmeasured.
const GPT_5_5: ImageTokenization = ImageTokenization::OpenAiPatch {
    multiplier: 1.2,
    low: sizing(512),
    high: budgeted(2048, 2500),
    original: budgeted(6000, 10_000),
    auto: AutoLevel::Original,
    verified: false,
};

/// GPT-5.6 and later: `original` keeps the image's size.
const fn gpt_5_6(verified: bool) -> ImageTokenization {
    ImageTokenization::OpenAiPatch {
        multiplier: 1.2,
        low: sizing(512),
        high: budgeted(2048, 2500),
        original: sizing(65_535),
        auto: AutoLevel::Original,
        verified,
    }
}

const DEEPSEEK_V4_1_FLASH: ImageTokenization = ImageTokenization::DeepSeekPatch {
    patch_size: 14,
    downsample: 3,
    max_tokens: 1024,
    min_pixels: 295_936,
    verified: true,
};

const OPENAI_WIRES: &[&str] = &[
    "openai-completions",
    "openai-responses",
    "openai-codex-responses",
    "azure-openai-responses",
];

/// The `image-tokenization` rules at reference commit c28b3e3, in rule order.
static RULES: &[(Selector, ImageTokenization)] = &[
    // classes/anthropic.kdl:26 — every Claude line not narrowed below: the
    // 4.7+ high-res tier (2,576px edges, 4,784 visual tokens).
    (
        Selector {
            class: Some("anthropic"),
            ..Selector::ANY
        },
        anthropic(2576, 4784, true),
    ),
    // classes/anthropic.kdl:45 — Opus before 4.7.
    (
        Selector {
            class: Some("anthropic"),
            family: Some("opus"),
            revision: Some(&[Below([4, 7, 0])]),
            ..Selector::ANY
        },
        CLAUDE_STANDARD,
    ),
    // classes/anthropic.kdl:52 — separator-collapsed `opus-45` style ids.
    (
        Selector {
            class: Some("anthropic"),
            family: Some("opus"),
            revision: Some(&[AtLeast([10, 0, 0]), Below([47, 0, 0])]),
            ..Selector::ANY
        },
        CLAUDE_STANDARD,
    ),
    // classes/anthropic.kdl:63 — Sonnet before 4.6.
    (
        Selector {
            class: Some("anthropic"),
            family: Some("sonnet"),
            revision: Some(&[Below([4, 6, 0])]),
            ..Selector::ANY
        },
        CLAUDE_STANDARD,
    ),
    // classes/anthropic.kdl:70 — Sonnet 4.6, measured.
    (
        Selector {
            class: Some("anthropic"),
            family: Some("sonnet"),
            revision: Some(&[AtLeast([4, 6, 0]), Below([4, 7, 0])]),
            ..Selector::ANY
        },
        CLAUDE_STANDARD_VERIFIED,
    ),
    // classes/anthropic.kdl:78
    (
        Selector {
            class: Some("anthropic"),
            family: Some("sonnet"),
            revision: Some(&[AtLeast([10, 0, 0]), Below([46, 0, 0])]),
            ..Selector::ANY
        },
        CLAUDE_STANDARD,
    ),
    // classes/anthropic.kdl:85
    (
        Selector {
            class: Some("anthropic"),
            family: Some("sonnet"),
            revision: Some(&[AtLeast([46, 0, 0]), Below([47, 0, 0])]),
            ..Selector::ANY
        },
        CLAUDE_STANDARD_VERIFIED,
    ),
    // classes/anthropic.kdl:95 — Haiku before 4.7.
    (
        Selector {
            class: Some("anthropic"),
            family: Some("haiku"),
            revision: Some(&[Below([4, 7, 0])]),
            ..Selector::ANY
        },
        CLAUDE_STANDARD,
    ),
    // classes/anthropic.kdl:102
    (
        Selector {
            class: Some("anthropic"),
            family: Some("haiku"),
            revision: Some(&[AtLeast([10, 0, 0]), Below([47, 0, 0])]),
            ..Selector::ANY
        },
        CLAUDE_STANDARD,
    ),
    // classes/deepseek.kdl:121 — V4.1 Flash's own vision config.
    (
        Selector {
            class: Some("deepseek"),
            family: Some("flash"),
            revision: Some(&[AtLeast([4, 1, 0]), Below([4, 2, 0])]),
            ..Selector::ANY
        },
        DEEPSEEK_V4_1_FLASH,
    ),
    // classes/deepseek.kdl:136 — DeepSeek's API serves the retired preview
    // id with the current Flash.
    (
        Selector {
            class: Some("deepseek"),
            providers: Some(&["deepseek"]),
            models: Some(&[ModelSelector::Exact("deepseek-v4-flash-vision-exp")]),
            ..Selector::ANY
        },
        DEEPSEEK_V4_1_FLASH,
    ),
    // classes/gemini.kdl:170 — Gemini 3 `media_resolution` budget.
    (
        Selector {
            class: Some("gemini"),
            revision: Some(&[AtLeast([3, 0, 0])]),
            ..Selector::ANY
        },
        ImageTokenization::Fixed {
            tokens: 1120,
            verified: false,
        },
    ),
    // classes/openai.kdl:107 — GPT-5.6 through 6.1, measured against billed
    // usage.
    (
        Selector {
            class: Some("openai"),
            revision: Some(&[AtLeast([5, 6, 0]), Below([6, 2, 0])]),
            ..Selector::ANY
        },
        gpt_5_6(true),
    ),
    // classes/openai.kdl:127 — later lines size like GPT-5.6, unmeasured.
    (
        Selector {
            class: Some("openai"),
            revision: Some(&[AtLeast([6, 2, 0]), Below([10, 0, 0])]),
            ..Selector::ANY
        },
        gpt_5_6(false),
    ),
    // classes/openai.kdl:145 — GPT-5.5, measured.
    (
        Selector {
            class: Some("openai"),
            revision: Some(&[Equal([5, 5, 0])]),
            ..Selector::ANY
        },
        ImageTokenization::OpenAiPatch {
            multiplier: 1.2,
            low: sizing(512),
            high: budgeted(2048, 2500),
            original: budgeted(6000, 10_000),
            auto: AutoLevel::Original,
            verified: true,
        },
    ),
    // classes/openai.kdl:165 — GPT-5.4: `auto` sizes like `high`.
    (
        Selector {
            class: Some("openai"),
            revision: Some(&[Equal([5, 4, 0])]),
            ..Selector::ANY
        },
        ImageTokenization::OpenAiPatch {
            multiplier: 1.2,
            low: budgeted(2048, 6144),
            high: budgeted(2048, 2500),
            original: budgeted(6000, 10_000),
            auto: AutoLevel::High,
            verified: false,
        },
    ),
    // classes/openai.kdl:185 — GPT-5.2 and 5.3.
    (
        Selector {
            class: Some("openai"),
            revision: Some(&[AtLeast([5, 2, 0]), Below([5, 4, 0])]),
            ..Selector::ANY
        },
        ImageTokenization::OpenAiPatch {
            multiplier: 1.2,
            low: budgeted(2048, 6144),
            high: budgeted(2048, 6144),
            original: budgeted(2048, 6144),
            auto: AutoLevel::High,
            verified: false,
        },
    ),
    // classes/openai.kdl:206 — GPT-6 Astra keeps `high` images at 65,535px.
    (
        Selector {
            class: Some("openai"),
            models: Some(&[ModelSelector::Glob("*gpt-6-astra*")]),
            ..Selector::ANY
        },
        ImageTokenization::OpenAiPatch {
            multiplier: 1.2,
            low: sizing(512),
            high: budgeted(65_535, 2500),
            original: sizing(65_535),
            auto: AutoLevel::Original,
            verified: true,
        },
    ),
    // classes/xai.kdl:67 — Grok 4.6 through 4.20: 32px patches resized past
    // 2,401, plus a few tokens per image.
    (
        Selector {
            class: Some("xai"),
            family: Some("grok"),
            revision: Some(&[AtLeast([4, 6, 0]), AtMost([4, 20, 0])]),
            ..Selector::ANY
        },
        ImageTokenization::OpenAiPatch {
            multiplier: 1.017,
            low: budgeted(65_535, 2401),
            high: budgeted(65_535, 2401),
            original: budgeted(65_535, 2401),
            auto: AutoLevel::Original,
            verified: true,
        },
    ),
    // providers/google-antigravity.kdl:99 — Cloud Code Assist bills every
    // Gemini image 1,089 tokens.
    (
        Selector {
            class: Some("gemini"),
            providers: Some(&["google-antigravity"]),
            priority: 1,
            ..Selector::ANY
        },
        ImageTokenization::Fixed {
            tokens: 1089,
            verified: true,
        },
    ),
    // providers/image-tokenization.kdl:8 — the OpenAI wires.
    (
        Selector {
            apis: Some(OPENAI_WIRES),
            priority: -1,
            ..Selector::ANY
        },
        GPT_5_5,
    ),
    // providers/image-tokenization.kdl:28 — the Google wires.
    (
        Selector {
            apis: Some(&["google-generative-ai", "google-gemini-cli", "google-vertex"]),
            priority: -1,
            ..Selector::ANY
        },
        ImageTokenization::Fixed {
            tokens: 1120,
            verified: false,
        },
    ),
    // providers/image-tokenization.kdl:37 — the Anthropic-patch wires: the
    // high-res numbers, unmeasured for the readers they price.
    (
        Selector {
            apis: Some(&[
                "anthropic-messages",
                "bedrock-converse-stream",
                "openrouter",
                "ollama-chat",
                "cursor-agent",
                "factory-droid-agent",
                "gitlab-duo-agent",
                "devin-agent",
                "apple-foundation-models",
            ]),
            priority: -1,
            ..Selector::ANY
        },
        anthropic(2576, 4784, false),
    ),
];

/// The reader's image billing rule: its lineage rule, else its wire API's
/// fallback; `None` when neither covers it (an unclassified model on an
/// unregistered API). An empty `id` resolves by wire API alone.
#[must_use]
pub fn resolve_image_tokenization(model: ModelRef<'_>) -> Option<ImageTokenization> {
    resolve_axis(RULES, &Target::new(model)).copied()
}

/// Scale `(width, height)` down (never up) so its longest side is at most
/// `max_edge`.
fn fit_long_edge(width: f64, height: f64, max_edge: f64) -> (f64, f64) {
    let longest = width.max(height);
    if longest <= max_edge {
        return (width, height);
    }
    let scale = max_edge / longest;
    (
        (width * scale).round().max(1.0),
        (height * scale).round().max(1.0),
    )
}

const OPENAI_PATCH_PX: f64 = 32.0;

/// <https://developers.openai.com/api/docs/guides/images-vision#patch-based-image-tokenization>
fn openai_patches(size: ImageSize, level: PatchSizing) -> f64 {
    let (width, height) = fit_long_edge(
        f64::from(size.width),
        f64::from(size.height),
        f64::from(level.max_edge),
    );
    let patches = (width / OPENAI_PATCH_PX).ceil() * (height / OPENAI_PATCH_PX).ceil();
    let Some(budget) = level.patch_budget.map(f64::from) else {
        return patches;
    };
    if patches <= budget {
        return patches;
    }
    let shrink = ((OPENAI_PATCH_PX * OPENAI_PATCH_PX * budget) / (width * height)).sqrt();
    let scaled_w = (width * shrink) / OPENAI_PATCH_PX;
    let scaled_h = (height * shrink) / OPENAI_PATCH_PX;
    let adjusted = shrink * (scaled_w.floor() / scaled_w).min(scaled_h.floor() / scaled_h);
    let resized_w = (width * adjusted).floor();
    let resized_h = (height * adjusted).floor();
    if resized_w <= 0.0 || resized_h <= 0.0 {
        return budget;
    }
    budget.min((resized_w / OPENAI_PATCH_PX).ceil() * (resized_h / OPENAI_PATCH_PX).ceil())
}

const ANTHROPIC_PATCH_PX: f64 = 28.0;

/// Round half to even, like the API's resize (and Python's `round`).
/// `f64::round` is `Math.round` for the non-negative values here.
#[allow(clippy::float_cmp)] // detects an exact `.5` fraction, as the reference does
fn round_ties_to_even(value: f64) -> f64 {
    let floor = value.floor();
    if value - floor != 0.5 {
        return value.round();
    }
    if floor % 2.0 == 0.0 {
        floor
    } else {
        floor + 1.0
    }
}

/// Anthropic visual tokens after the API's resize: the largest
/// aspect-preserving size whose 28px-padded edges fit `max_edge` and whose
/// patch count fits `max_tokens`, found by bisecting the long edge. Port of
/// the reference implementation:
/// <https://platform.claude.com/docs/en/build-with-claude/vision-coordinates#resize-your-image-before-uploading>
fn anthropic_tokens(size: ImageSize, max_edge: u32, max_tokens: u32) -> f64 {
    let (max_edge, max_tokens) = (f64::from(max_edge), f64::from(max_tokens));
    let long = f64::from(size.width.max(size.height));
    let short_side = f64::from(size.width.min(size.height));
    let aspect = long / short_side;
    let patches =
        |l: f64, s: f64| (l / ANTHROPIC_PATCH_PX).ceil() * (s / ANTHROPIC_PATCH_PX).ceil();
    let fits = |l: f64, s: f64| {
        (l / ANTHROPIC_PATCH_PX).ceil() * ANTHROPIC_PATCH_PX <= max_edge
            && (s / ANTHROPIC_PATCH_PX).ceil() * ANTHROPIC_PATCH_PX <= max_edge
            && patches(l, s) <= max_tokens
    };
    let short = |l: f64| round_ties_to_even(l / aspect).max(1.0);
    if fits(long, short_side) {
        return patches(long, short_side);
    }
    let mut lo = 1.0; // always fits
    let mut hi = long; // never fits
    while lo + 1.0 < hi {
        let mid = f64::midpoint(lo, hi).floor();
        if fits(mid, short(mid)) {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    patches(lo, short(lo))
}

/// `DeepSeek` visual tokens: the image is upscaled to `min_pixels`, padded
/// to whole patches, and when its token grid busts `max_tokens` shrunk to
/// the largest aspect-preserving grid that fits. Port of `plan_image_grid`
/// in the reference processor (`max_wh_ratio` is unset in the V4.1 config):
/// <https://huggingface.co/deepseek-ai/DeepSeek-V4.1-Flash/blob/main/inference/image_processor.py>
fn deepseek_tokens(
    size: ImageSize,
    patch_size: u32,
    downsample: u32,
    max_tokens: u32,
    min_pixels: u32,
) -> f64 {
    let patch_size = f64::from(patch_size);
    let downsample = f64::from(downsample);
    let max_tokens = f64::from(max_tokens);
    let min_pixels = f64::from(min_pixels);
    let cell = patch_size * downsample;
    let span_tokens = |height: f64, width: f64| {
        let rows = ((height / patch_size).floor() / downsample).ceil();
        let cols = ((width / patch_size).floor() / downsample).ceil();
        rows * (cols + 1.0) + 2.0
    };
    let mut width = f64::from(size.width);
    let mut height = f64::from(size.height);
    if width * height < min_pixels {
        let scale = (min_pixels / (width * height)).sqrt();
        width = (width * scale).trunc();
        height = (height * scale).trunc();
    }
    let tokens = span_tokens(
        (height / patch_size).ceil() * patch_size,
        (width / patch_size).ceil() * patch_size,
    );
    if tokens <= max_tokens {
        return tokens;
    }
    let aspect = height / width;
    let max_cols = ((max_tokens - 2.0) / aspect + 0.25).sqrt() - 0.5;
    let max_rows = max_cols * aspect;
    if max_cols < 1.0 {
        return span_tokens(((max_tokens - 2.0) / 2.0).floor() * cell, cell);
    }
    if max_rows < 1.0 {
        return span_tokens(cell, (max_tokens - 3.0) * cell);
    }
    let beta = ((max_cols.floor() * cell) / width).min((max_rows.floor() * cell) / height);
    span_tokens(
        ((height * beta) / patch_size).floor() * patch_size,
        ((width * beta) / patch_size).floor() * patch_size,
    )
}

/// Billed input tokens for one image of `size` under `rule`; only
/// [`ImageTokenization::OpenAiPatch`] reads `detail`.
#[must_use]
#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)] // whole, non-negative token counts far below 2^53
pub fn image_tokens(rule: &ImageTokenization, size: ImageSize, detail: Option<ImageDetail>) -> u64 {
    let tokens = match *rule {
        ImageTokenization::Fixed { tokens, .. } => f64::from(tokens),
        ImageTokenization::OpenAiPatch {
            multiplier,
            low,
            high,
            original,
            auto,
            ..
        } => {
            let level = match (detail, auto) {
                (Some(ImageDetail::Low), _) => low,
                (Some(ImageDetail::High), _)
                | (Some(ImageDetail::Auto) | None, AutoLevel::High) => high,
                (Some(ImageDetail::Original), _)
                | (Some(ImageDetail::Auto) | None, AutoLevel::Original) => original,
            };
            (openai_patches(size, level) * multiplier).ceil()
        }
        ImageTokenization::AnthropicPatch {
            max_edge,
            max_tokens,
            ..
        } => anthropic_tokens(size, max_edge, max_tokens),
        ImageTokenization::DeepSeekPatch {
            patch_size,
            downsample,
            max_tokens,
            min_pixels,
            ..
        } => deepseek_tokens(size, patch_size, downsample, max_tokens, min_pixels),
    };
    tokens as u64
}

/// Larger than every detail level's pixel limit, so an unknown size charges
/// the level's full patch budget.
const UNKNOWN_SIZE: ImageSize = ImageSize {
    width: 65_535,
    height: 65_535,
};

/// Input tokens one image is billed under `rule` (the provider's image
/// pricing), the `OpenAI` Responses wire's rule when `None` (what
/// `resolve_image_tokenization` gives a bare `openai-responses` target).
/// An unknown or empty size (undecodable data, remote URLs, provider file
/// ids) charges the rule's most expensive size.
#[must_use]
pub fn billed_image_tokens(
    size: Option<ImageSize>,
    detail: Option<ImageDetail>,
    rule: Option<&ImageTokenization>,
) -> u64 {
    let size = size
        .filter(|size| size.width > 0 && size.height > 0)
        .unwrap_or(UNKNOWN_SIZE);
    image_tokens(rule.unwrap_or(&GPT_5_5), size, detail)
}

#[cfg(test)]
#[path = "image_tests.rs"]
mod tests;
