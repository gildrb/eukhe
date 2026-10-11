//! Generated catalog flattening. Port of `model-catalog.ts`.
//!
//! A provider's generated data file groups models by API, keyed
//! `"<type>:<id>"` (`{ "anthropic-messages": { "chat:claude-…": {…} } }`).
//! The flatten functions select one model type and key the result by model
//! id, in data order.

use eukhe_types::pi_ai::IndexMap;
use serde::de::DeserializeOwned;
use serde_json::{Map, Value};

use eukhe_types::pi_ai::{ClassifierModel, ImageModel, Model, ModelType};

/// Models grouped by API, then keyed `"<type>:<id>"`: TS `ModelGroups`.
pub type ModelGroups = Map<String, Value>;

/// Chat models of one provider keyed by id: TS `ChatModelCatalog`.
pub type ChatModelCatalog = IndexMap<String, Model>;

/// Image models of one provider keyed by id: TS `ImageModelCatalog`.
pub type ImageModelCatalog = IndexMap<String, ImageModel>;

/// Classifier models of one provider keyed by id: TS
/// `ClassifierModelCatalog`.
pub type ClassifierModelCatalog = IndexMap<String, ClassifierModel>;

/// Parses a generated provider data file.
///
/// # Panics
///
/// Panics when the embedded data is not a JSON object; the build embeds the
/// generated files verbatim, and the catalog tests parse every one.
#[must_use]
pub fn parse_model_groups(json: &str) -> ModelGroups {
    serde_json::from_str(json).expect("generated provider data is a JSON object")
}

fn model_type_name(model_type: ModelType) -> &'static str {
    match model_type {
        ModelType::Chat => "chat",
        ModelType::Image => "image",
        ModelType::Classifier => "classifier",
    }
}

fn flatten_model_catalog<T: DeserializeOwned>(
    groups: &ModelGroups,
    model_type: ModelType,
) -> IndexMap<String, T> {
    let wanted = model_type_name(model_type);
    let mut catalog = IndexMap::new();
    for model in groups
        .values()
        .filter_map(Value::as_object)
        .flat_map(Map::values)
        .filter(|model| model.get("type").and_then(Value::as_str) == Some(wanted))
    {
        let id = model
            .get("id")
            .and_then(Value::as_str)
            .expect("generated catalog models carry a string id")
            .to_owned();
        let parsed: T = serde_json::from_value(model.clone())
            .unwrap_or_else(|error| panic!("generated catalog model {id} is invalid: {error}"));
        catalog.insert(id, parsed);
    }
    catalog
}

/// Chat models of `groups` keyed by id.
///
/// # Panics
///
/// Panics when a generated chat entry does not match the chat model shape.
#[must_use]
pub fn flatten_chat_model_catalog(_provider: &str, groups: &ModelGroups) -> ChatModelCatalog {
    flatten_model_catalog(groups, ModelType::Chat)
}

/// Image models of `groups` keyed by id.
///
/// # Panics
///
/// Panics when a generated image entry does not match the image model shape.
#[must_use]
pub fn flatten_image_model_catalog(_provider: &str, groups: &ModelGroups) -> ImageModelCatalog {
    flatten_model_catalog(groups, ModelType::Image)
}

/// Classifier models of `groups` keyed by id.
///
/// # Panics
///
/// Panics when a generated classifier entry does not match the classifier
/// model shape.
#[must_use]
pub fn flatten_classifier_model_catalog(
    _provider: &str,
    groups: &ModelGroups,
) -> ClassifierModelCatalog {
    flatten_model_catalog(groups, ModelType::Classifier)
}
