//! Generated catalog flattening. Port of `model-catalog.ts`.
//!
//! A provider's generated data file groups models by API, keyed
//! `"<type>:<id>"` (`{ "anthropic-messages": { "chat:claude-…": {…} } }`).
//! The flatten functions select one model type and key the result by model
//! id, in data order.

use std::borrow::Cow;

use eukhe_types::pi_ai::IndexMap;
use serde::de::DeserializeOwned;
use serde::Deserialize;
use serde_json::value::RawValue;

use eukhe_types::pi_ai::{ClassifierModel, ImageModel, Model, ModelType};

/// Models grouped by API, then keyed `"<type>:<id>"`: TS `ModelGroups`.
/// Each model stays its JSON text in the embedded data file: a catalog
/// parses only the models of its type, and no parsed tree of the whole
/// file outlives the parse.
pub type ModelGroups = IndexMap<String, IndexMap<String, &'static RawValue>>;

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
/// Panics when the embedded data is not a JSON object of model objects; the
/// build embeds the generated files verbatim, and the catalog tests parse
/// every one.
#[must_use]
pub fn parse_model_groups(json: &'static str) -> ModelGroups {
    serde_json::from_str(json).expect("generated provider data is a JSON object of model groups")
}

/// The fields a catalog selects a model by.
#[derive(Deserialize)]
struct ModelHead<'a> {
    #[serde(rename = "type")]
    model_type: ModelType,
    #[serde(borrow)]
    id: Cow<'a, str>,
}

fn flatten_model_catalog<T: DeserializeOwned>(
    groups: &ModelGroups,
    model_type: ModelType,
) -> IndexMap<String, T> {
    groups
        .values()
        .flat_map(IndexMap::values)
        .filter_map(|model| {
            let head: ModelHead = serde_json::from_str(model.get())
                .expect("generated catalog models carry a model type and a string id");
            (head.model_type == model_type).then(|| {
                let parsed: T = serde_json::from_str(model.get()).unwrap_or_else(|error| {
                    panic!("generated catalog model {} is invalid: {error}", head.id)
                });
                (head.id.into_owned(), parsed)
            })
        })
        .collect()
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
