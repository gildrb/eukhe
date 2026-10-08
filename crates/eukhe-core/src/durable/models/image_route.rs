//! Image-model routing for dispatched durable turns (the old engine's
//! `settings.imageModel` behavior, TS `resolveImageModelOverride`): a
//! request whose context attaches image blocks, served on a model without
//! image input, routes to the configured image-capable model instead. An
//! unusable or missing reference fails the turn with the actionable refusal
//! naming the setting — nothing silently downgrades the images to
//! "(image omitted)" placeholders.
//!
//! The decision is pure and synchronous: it resolves against the
//! collection's last-known chat catalog (`Models::get_models`), so the
//! dispatcher (which owns the request pipeline) applies the swap itself.
//! Unlike the old engine's resolver, the durable decision carries no
//! thinking-level/tier clamps (the durable request builds those from the
//! routed model) and no auth probe (the routed model's provider resolves
//! auth per request, like every other served model).

use eukhe_pi_ai::models::Models;
use eukhe_types::pi_ai::{Modality, Model};

/// The image-routing decision for one dispatched request: serve on the
/// session model, serve on a routed image model, or fail the turn with the
/// user-visible refusal.
// The dispatcher's fixed shape: an owned routed model, not boxed (matching
// the repo's by-value unions of model payloads).
#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum ImageRoute {
    /// Serve on the session model as-is.
    None,
    /// Serve on this model instead.
    Route(Model),
    /// Fail the turn with this user-visible refusal.
    Refuse(String),
}

/// Whether the model takes image input (TS `model.input.includes("image")`).
fn takes_image_input(model: &Model) -> bool {
    model.input.contains(&Modality::Image)
}

/// TS `formatImageModelRequiredMessage`: the session model cannot serve the
/// attached images and no image model is configured. Name the model, the
/// setting, and the alternatives so the user can act immediately.
fn format_image_model_required_message(session_model_id: &str) -> String {
    format!(
        "This turn attaches images, but the selected model ({session_model_id}) does not accept image input.\n\nPick one:\n- Switch the session model to an image-capable one with /model, or\n- Set imageModel in settings.json to an image-capable model (\"provider/model-id\" or a bare id), e.g. \"anthropic/claude-sonnet-4-5\"\n\nThen resend the message. Without it the request would silently drop the images."
    )
}

/// TS `formatImageModelUnusableMessage`: the configured `imageModel` could
/// not be resolved to an available, image-capable model.
fn format_image_model_unusable_message(reference: &str) -> String {
    format!(
        "imageModel \"{reference}\" could not be resolved to an available, image-capable, authenticated model.\n\nFix the imageModel setting (settings.json) or authenticate the provider, then resend the message."
    )
}

/// Exact reference match against the catalog (the old engine's
/// `find_exact_model_reference_match` over pi-ai models): canonical
/// `provider/id`, the `provider/id` split, or an unambiguous bare id,
/// case-insensitively; an ambiguous or unmatched reference resolves to
/// nothing.
fn find_exact_model_reference_match<'a>(
    model_reference: &str,
    catalog: &'a [Model],
) -> Option<&'a Model> {
    let trimmed = model_reference.trim();
    if trimmed.is_empty() {
        return None;
    }
    let normalized = trimmed.to_lowercase();
    let canonical: Vec<&Model> = catalog
        .iter()
        .filter(|model| format!("{}/{}", model.provider, model.id).to_lowercase() == normalized)
        .collect();
    if canonical.len() == 1 {
        return Some(canonical[0]);
    }
    if canonical.len() > 1 {
        return None;
    }
    if let Some(slash) = trimmed.find('/') {
        let provider = trimmed[..slash].trim();
        let model_id = trimmed[slash + 1..].trim();
        if !provider.is_empty() && !model_id.is_empty() {
            let provider_matches: Vec<&Model> = catalog
                .iter()
                .filter(|model| {
                    model.provider.to_lowercase() == provider.to_lowercase()
                        && model.id.to_lowercase() == model_id.to_lowercase()
                })
                .collect();
            if provider_matches.len() == 1 {
                return Some(provider_matches[0]);
            }
            if provider_matches.len() > 1 {
                return None;
            }
        }
    }
    let id_matches: Vec<&Model> = catalog
        .iter()
        .filter(|model| model.id.to_lowercase() == normalized)
        .collect();
    if id_matches.len() == 1 {
        Some(id_matches[0])
    } else {
        None
    }
}

/// Resolve the routing decision for one dispatched request: the configured
/// `imageModel` (a bare model id or `provider/model-id`) when the serving
/// model has no image input and the request's context attaches image
/// blocks; [`ImageRoute::None`] when the serving model accepts images or
/// the request carries none; the actionable refusal when the turn cannot be
/// served honestly (a text-only serving model would otherwise downgrade the
/// images to an "(image omitted)" placeholder). A blank `image_model`
/// reference (empty or whitespace) behaves as unset, like the settings
/// read.
pub(crate) fn resolve(
    context_has_images: bool,
    model: &Model,
    image_model: Option<&str>,
    models: &Models,
) -> ImageRoute {
    if !context_has_images || takes_image_input(model) {
        return ImageRoute::None;
    }
    let Some(reference) = image_model
        .map(str::trim)
        .filter(|reference| !reference.is_empty())
    else {
        return ImageRoute::Refuse(format_image_model_required_message(&format!(
            "{}/{}",
            model.provider, model.id
        )));
    };
    let catalog = models.get_models(None);
    let Some(routed) = find_exact_model_reference_match(reference, &catalog) else {
        return ImageRoute::Refuse(format_image_model_unusable_message(reference));
    };
    if !takes_image_input(routed) {
        return ImageRoute::Refuse(format_image_model_unusable_message(reference));
    }
    ImageRoute::Route(routed.clone())
}

#[cfg(test)]
mod tests {
    use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
    use eukhe_pi_ai::providers::faux::{
        faux_provider, FauxModelDefinition, RegisterFauxProviderOptions,
    };
    use eukhe_types::pi_ai::Modality;

    use super::*;

    /// A collection with one faux provider: a text-only session model and
    /// an image-capable model.
    fn models() -> (Models, Model, Model) {
        let faux = faux_provider(RegisterFauxProviderOptions {
            models: Some(vec![
                FauxModelDefinition {
                    input: Some(vec![Modality::Text]),
                    ..FauxModelDefinition::new("text-only")
                },
                FauxModelDefinition {
                    input: Some(vec![Modality::Text, Modality::Image]),
                    ..FauxModelDefinition::new("vision")
                },
            ]),
            ..RegisterFauxProviderOptions::default()
        });
        let models = create_models(CreateModelsOptions::default());
        models.set_provider(faux.provider.clone());
        let text = faux.get_model_by_id("text-only").unwrap();
        let vision = faux.get_model_by_id("vision").unwrap();
        (models, text, vision)
    }

    // The old table (eukhe-core models/image_model_routing.rs tests, TS
    // test/image-model-override.test.ts): routes image turns to imageModel;
    // a vision session model serves image turns natively; refusals name the
    // setting.
    #[test]
    fn routes_image_turns_to_image_model() {
        let (models, text, vision) = models();
        assert_eq!(
            resolve(true, &text, Some("vision"), &models),
            ImageRoute::Route(vision)
        );
        // Canonical provider/id reference and a bare id resolve alike.
        assert!(matches!(
            resolve(true, &text, Some("faux/vision"), &models),
            ImageRoute::Route(_)
        ));
    }

    #[test]
    fn vision_session_model_serves_image_turns() {
        let (models, _text, vision) = models();
        assert_eq!(
            resolve(true, &vision, Some("vision"), &models),
            ImageRoute::None
        );
    }

    #[test]
    fn no_routing_without_images() {
        let (models, text, _vision) = models();
        assert_eq!(
            resolve(false, &text, Some("vision"), &models),
            ImageRoute::None
        );
    }

    #[test]
    fn refuses_without_image_model() {
        let (models, text, _vision) = models();
        let ImageRoute::Refuse(error) = resolve(true, &text, None, &models) else {
            panic!("expected refusal");
        };
        assert!(
            error.contains("This turn attaches images, but the selected model (faux/text-only) does not accept image input."),
            "{error}"
        );
        assert!(error.contains("Set imageModel in settings.json"), "{error}");
        // A blank reference behaves as unset, like the settings read.
        let ImageRoute::Refuse(blank) = resolve(true, &text, Some("   "), &models) else {
            panic!("expected refusal");
        };
        assert_eq!(blank, error);
    }

    #[test]
    fn refuses_unusable_reference() {
        let (models, text, _vision) = models();
        let ImageRoute::Refuse(error) = resolve(true, &text, Some("openai/gpt-5.4"), &models)
        else {
            panic!("expected refusal");
        };
        assert!(
            error.contains("could not be resolved to an available, image-capable"),
            "{error}"
        );
    }

    #[test]
    fn refuses_text_only_image_model() {
        let (models, text, _vision) = models();
        let ImageRoute::Refuse(error) = resolve(true, &text, Some("faux/text-only"), &models)
        else {
            panic!("expected refusal");
        };
        assert!(
            error.contains("could not be resolved to an available, image-capable"),
            "{error}"
        );
    }
}
