//! The screenshot a model takes: none for a model without vision or while
//! the user blocks images, else one scaled into the frame the model's
//! provider keeps at its own size (its image tokenization rule in
//! `eukhe_tokens`, then the model's own resize limits), so a pixel the
//! model names is a pixel of the frame the desktop stored.

use std::num::NonZeroU32;

use eukhe_desktop::ImageCaps;
use eukhe_tokens::{resolve_image_tokenization, AutoLevel, ImageTokenization, ModelRef};
use eukhe_types::pi_ai::{Modality, Model};

/// The longest side of any screenshot: the `read` tool's image limit, so
/// one screenshot costs what one attached image does.
const CEILING: u32 = 1568;

/// Pixels per visual token of each patch tokenizer.
const ANTHROPIC_PATCH_PIXELS: u64 = 28 * 28;
const OPENAI_PATCH_PIXELS: u64 = 32 * 32;

/// Whether and how large a screenshot the model gets.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Vision {
    /// Scaled into `caps`; a PNG whose base64 is longer than `max_base64`
    /// is not attached.
    Sees {
        caps: ImageCaps,
        max_base64: Option<u64>,
    },
    Blind(Blind),
}

/// Why the model gets no screenshot.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Blind {
    /// The model does not take images (or is unknown).
    TextOnly,
    /// `images.blockImages` is on.
    Blocked,
}

impl Blind {
    pub(super) fn note(self) -> &'static str {
        match self {
            Self::TextOnly => "No screenshot: this model cannot see images; the tree is the view.",
            Self::Blocked => "No screenshot: the user blocks images (`images.blockImages`).",
        }
    }
}

/// Whether images reach the model at all.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Images {
    Allowed,
    Blocked,
}

/// What `model` sees of a window.
pub(super) fn vision(model: Option<&Model>, images: Images) -> Vision {
    match (model, images) {
        (_, Images::Blocked) => Vision::Blind(Blind::Blocked),
        (Some(model), Images::Allowed) if model.input.contains(&Modality::Image) => Vision::Sees {
            caps: caps(model),
            max_base64: model
                .input_limits
                .as_ref()
                .and_then(|limits| limits.images.as_ref())
                .and_then(|images| images.resize.as_ref())
                .and_then(|resize| resize.max_bytes),
        },
        (Some(_) | None, Images::Allowed) => Vision::Blind(Blind::TextOnly),
    }
}

/// The base64 length of `bytes` bytes.
pub(super) fn base64_len(bytes: usize) -> u64 {
    u64::try_from(bytes.div_ceil(3)).map_or(u64::MAX, |groups| groups.saturating_mul(4))
}

/// The longest edge and the pixel area the model's provider keeps as is.
fn native(model: &Model) -> (u32, Option<u64>) {
    let rule = resolve_image_tokenization(ModelRef {
        id: &model.id,
        provider: model.provider.as_str(),
        api: model.api.as_str(),
    });
    match rule {
        Some(ImageTokenization::AnthropicPatch {
            max_edge,
            max_tokens,
            ..
        }) => (
            max_edge,
            Some(u64::from(max_tokens) * ANTHROPIC_PATCH_PIXELS),
        ),
        Some(ImageTokenization::OpenAiPatch {
            high,
            original,
            auto,
            ..
        }) => {
            // No `detail` is sent: the provider sizes like `auto`.
            let level = match auto {
                AutoLevel::High => high,
                AutoLevel::Original => original,
            };
            (
                level.max_edge,
                level
                    .patch_budget
                    .map(|patches| u64::from(patches) * OPENAI_PATCH_PIXELS),
            )
        }
        Some(ImageTokenization::DeepSeekPatch {
            patch_size,
            downsample,
            max_tokens,
            ..
        }) => {
            let token = u64::from(patch_size) * u64::from(downsample);
            (CEILING, Some(u64::from(max_tokens) * token * token))
        }
        Some(ImageTokenization::Fixed { .. }) | None => (CEILING, None),
    }
}

/// The 16:10 box of `area` pixels: any image that fits it has at most
/// that area.
fn area_box(area: u64) -> (u64, u64) {
    ((area * 16 / 10).isqrt(), (area * 10 / 16).isqrt())
}

fn nonzero(pixels: u64) -> NonZeroU32 {
    u32::try_from(pixels)
        .ok()
        .and_then(NonZeroU32::new)
        .unwrap_or(NonZeroU32::MIN)
}

/// The screenshot frame of `model`: its provider's native edge and area,
/// at most [`CEILING`], within the model's resize limits.
fn caps(model: &Model) -> ImageCaps {
    let (edge, area) = native(model);
    let edge = u64::from(edge.min(CEILING));
    let (width, height) = area.map_or((edge, edge), area_box);
    let resize = model
        .input_limits
        .as_ref()
        .and_then(|limits| limits.images.as_ref())
        .and_then(|images| images.resize.as_ref());
    let limit = |side: u64, max: Option<u64>| max.map_or(side, |max| side.min(max));
    ImageCaps {
        max_width: nonzero(limit(
            width.min(edge),
            resize.and_then(|resize| resize.max_width),
        )),
        max_height: nonzero(limit(
            height.min(edge),
            resize.and_then(|resize| resize.max_height),
        )),
    }
}

#[cfg(test)]
mod tests {
    use eukhe_types::pi_ai::{
        Api, ModelCost, ModelImageInputLimits, ModelImageResizeOptions, ModelInputLimits,
        ProviderId,
    };

    use super::*;

    fn model(api: &str, id: &str, vision: bool, resize: Option<ModelImageResizeOptions>) -> Model {
        Model {
            id: id.to_owned(),
            name: id.to_owned(),
            api: Api::parse(api),
            provider: ProviderId::parse("p"),
            base_url: String::new(),
            input: if vision {
                vec![Modality::Text, Modality::Image]
            } else {
                vec![Modality::Text]
            },
            input_limits: resize.map(|resize| ModelInputLimits {
                max_request_bytes: None,
                images: Some(ModelImageInputLimits {
                    resize: Some(resize),
                    max_per_message: None,
                    max_per_request: None,
                }),
            }),
            cost: ModelCost::default(),
            headers: None,
            model_type: None,
            reasoning: false,
            thinking_level_map: None,
            prompt_cache: None,
            context_window: 100_000,
            max_tokens: 4_096,
            sampling_params: None,
            sampling_params_by_thinking_level: None,
            compat: None,
            featured: None,
        }
    }

    fn sees(width: u32, height: u32, max_base64: Option<u64>) -> Vision {
        Vision::Sees {
            caps: ImageCaps {
                max_width: nonzero(width.into()),
                max_height: nonzero(height.into()),
            },
            max_base64,
        }
    }

    /// A Claude screenshot fits the area Claude keeps unscaled (1,568
    /// tokens of 28px patches); an unknown vision model gets the read
    /// ceiling; the model's own resize limits lower either; a model
    /// without vision, or blocked images, gets none.
    #[test]
    fn the_screenshot_fits_what_the_provider_keeps() {
        let claude = model("anthropic-messages", "claude-sonnet-4-5", true, None);
        let unknown = model("custom", "", true, None);
        let small = model(
            "custom",
            "",
            true,
            Some(ModelImageResizeOptions {
                max_width: Some(1000),
                max_height: Some(700),
                max_bytes: Some(400_000),
                jpeg_quality: None,
            }),
        );
        let text = model("anthropic-messages", "claude-sonnet-4-5", false, None);
        assert_eq!(
            [
                vision(Some(&claude), Images::Allowed),
                vision(Some(&unknown), Images::Allowed),
                vision(Some(&small), Images::Allowed),
                vision(Some(&text), Images::Allowed),
                vision(None, Images::Allowed),
                vision(Some(&claude), Images::Blocked),
            ],
            [
                sees(1402, 876, None),
                sees(1568, 1568, None),
                sees(1000, 700, Some(400_000)),
                Vision::Blind(Blind::TextOnly),
                Vision::Blind(Blind::TextOnly),
                Vision::Blind(Blind::Blocked),
            ]
        );
    }

    #[test]
    fn base64_length_rounds_up_to_whole_groups() {
        assert_eq!(
            [base64_len(0), base64_len(1), base64_len(3), base64_len(4)],
            [0, 4, 4, 8]
        );
    }
}
