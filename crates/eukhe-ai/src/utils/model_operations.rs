//! Model-type narrowing and error results for image/classifier models.

use eukhe_types::pi_ai::{
    AnyModel, AssistantImages, ClassifierContext, ClassifierModel, ClassifierResult,
    ClassifierStopReason, ImageModel, ImagesStopReason, IndexMap, Modality, Model, ModelType,
};

use super::diagnostics::Thrown;
use super::models_error::{ModelsError, ModelsErrorCode};
use super::now_ms;

/// The type of a model. Models without `type` are chat models.
#[must_use]
pub const fn get_model_type(model: &AnyModel) -> ModelType {
    model.model_type()
}

/// Runtime-checked model type test, including legacy chat models without `type`.
#[must_use]
pub fn is_model_type(model: &AnyModel, model_type: ModelType) -> bool {
    get_model_type(model) == model_type
}

/// Narrow to a chat model.
///
/// # Errors
///
/// `provider` [`ModelsError`] when the model is not a chat model.
pub fn assert_chat_model(model: &AnyModel) -> Result<&Model, ModelsError> {
    match model {
        AnyModel::Chat(chat) => Ok(chat),
        AnyModel::Image(_) | AnyModel::Classifier(_) => Err(not_a(model, "a chat")),
    }
}

/// Narrow to an image model.
///
/// # Errors
///
/// `provider` [`ModelsError`] when the model is not an image model.
pub fn assert_image_model(model: &AnyModel) -> Result<&ImageModel, ModelsError> {
    match model {
        AnyModel::Image(image) => Ok(image),
        AnyModel::Chat(_) | AnyModel::Classifier(_) => Err(not_a(model, "an image")),
    }
}

/// Narrow to a classifier model.
///
/// # Errors
///
/// `provider` [`ModelsError`] when the model is not a classifier model.
pub fn assert_classifier_model(model: &AnyModel) -> Result<&ClassifierModel, ModelsError> {
    match model {
        AnyModel::Classifier(classifier) => Ok(classifier),
        AnyModel::Chat(_) | AnyModel::Image(_) => Err(not_a(model, "a classifier")),
    }
}

/// Rejects classifier images for models whose catalog entry does not accept image input.
///
/// # Errors
///
/// `provider` [`ModelsError`] when `context` has images and the model's
/// `input` lacks `image`.
pub fn assert_classifier_input_supported(
    model: &ClassifierModel,
    context: &ClassifierContext,
) -> Result<(), ModelsError> {
    if context
        .images
        .as_ref()
        .is_some_and(|images| !images.is_empty())
        && !model.input.contains(&Modality::Image)
    {
        return Err(ModelsError::new(
            ModelsErrorCode::Provider,
            format!(
                "Model {}/{} does not accept image input",
                model.provider, model.id
            ),
        ));
    }
    Ok(())
}

/// `Model <provider>/<id> is not <kind> model`.
fn not_a(model: &AnyModel, kind: &str) -> ModelsError {
    ModelsError::new(
        ModelsErrorCode::Provider,
        format!(
            "Model {}/{} is not {kind} model",
            model.provider(),
            model.id()
        ),
    )
}

/// The failed result of an image-generation request.
#[must_use]
pub fn image_error_result(model: &ImageModel, error: &Thrown, aborted: bool) -> AssistantImages {
    AssistantImages {
        api: model.api.clone(),
        provider: model.provider.clone(),
        model: model.id.clone(),
        output: Vec::new(),
        response_id: None,
        usage: None,
        stop_reason: if aborted {
            ImagesStopReason::Aborted
        } else {
            ImagesStopReason::Error
        },
        error_message: Some(error.to_string()),
        timestamp: now_ms(),
    }
}

/// The failed result of a classifier request.
#[must_use]
pub fn classifier_error_result(
    model: &ClassifierModel,
    error: &Thrown,
    aborted: bool,
) -> ClassifierResult {
    ClassifierResult {
        api: model.api.clone(),
        provider: model.provider.clone(),
        model: model.id.clone(),
        answers: IndexMap::new(),
        usage: None,
        stop_reason: if aborted {
            ClassifierStopReason::Aborted
        } else {
            ClassifierStopReason::Error
        },
        error_message: Some(error.to_string()),
        timestamp: now_ms(),
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;
    use crate::utils::diagnostics::ErrorObject;

    fn any_model(value: serde_json::Value) -> AnyModel {
        serde_json::from_value(value).unwrap()
    }

    fn base(extra: serde_json::Value) -> serde_json::Value {
        let mut value = json!({
            "id": "m", "name": "M", "api": "x", "provider": "p", "baseUrl": "https://x",
            "input": ["text"], "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 }
        });
        if let (Some(target), serde_json::Value::Object(extra)) = (value.as_object_mut(), extra) {
            target.extend(extra);
        }
        value
    }

    #[test]
    fn narrows_model_types_including_legacy_chat_models() {
        let chat = any_model(base(
            json!({ "reasoning": false, "contextWindow": 1, "maxTokens": 1 }),
        ));
        let image = any_model(base(json!({ "type": "image", "output": ["image"] })));
        let classifier = any_model(base(json!({ "type": "classifier", "contextWindow": 10 })));
        assert_eq!(get_model_type(&chat), ModelType::Chat);
        assert!(is_model_type(&image, ModelType::Image));
        assert!(assert_chat_model(&chat).is_ok());
        assert!(assert_image_model(&image).is_ok());
        assert!(assert_classifier_model(&classifier).is_ok());
        let error = assert_chat_model(&image).unwrap_err();
        assert_eq!(error.code, ModelsErrorCode::Provider);
        assert_eq!(error.message, "Model p/m is not a chat model");
        assert_eq!(
            assert_image_model(&chat).unwrap_err().message,
            "Model p/m is not an image model"
        );
        assert_eq!(
            assert_classifier_model(&chat).unwrap_err().message,
            "Model p/m is not a classifier model"
        );
    }

    #[test]
    fn builds_error_results() {
        let AnyModel::Image(image) =
            any_model(base(json!({ "type": "image", "output": ["image"] })))
        else {
            panic!("image model")
        };
        let result = image_error_result(
            &image,
            &ErrorObject::new("boom").thrown(),
            /*aborted*/ true,
        );
        assert_eq!(result.stop_reason, ImagesStopReason::Aborted);
        assert_eq!(result.error_message.as_deref(), Some("boom"));
        assert!(result.output.is_empty());
        let AnyModel::Classifier(classifier) =
            any_model(base(json!({ "type": "classifier", "contextWindow": 10 })))
        else {
            panic!("classifier model")
        };
        let result = classifier_error_result(
            &classifier,
            &ErrorObject::new("bad").thrown(),
            /*aborted*/ false,
        );
        assert_eq!(result.stop_reason, ClassifierStopReason::Error);
        assert!(result.answers.is_empty());
        assert_eq!((result.api.as_str(), result.model.as_str()), ("x", "m"));
    }
}
