//! Generated catalog flattening. Port of `model-catalog.ts`.
//!
//! A provider's generated data file groups models by API, keyed
//! `"<type>:<id>"` (`{ "anthropic-messages": { "chat:claude-…": {…} } }`).
//! The flatten functions select one model type and key the result by model
//! id, in data order.
//!
//! Compatibility facts have two data layers: the provider's defaults per API
//! (`data/provider_compat.json`, what a host changes) and the row's own
//! `compat` (what is true of that model on that host). A row key wins over
//! the provider default of the same key.

use std::sync::LazyLock;

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

static PROVIDER_COMPAT: LazyLock<ModelGroups> =
    LazyLock::new(|| parse_model_groups(include_str!("providers/data/provider_compat.json")));

/// `row_compat` over the compat defaults of `provider` on `api`: the
/// model's effective compat object, `None` when neither layer has one.
#[must_use]
pub fn with_provider_compat_defaults(
    provider: &str,
    api: &str,
    row_compat: Option<&Map<String, Value>>,
) -> Option<Map<String, Value>> {
    let mut compat = PROVIDER_COMPAT
        .get(provider)
        .and_then(|apis| apis.get(api))
        .and_then(Value::as_object)
        .cloned();
    if let Some(row_compat) = row_compat {
        let compat = compat.get_or_insert_with(Map::new);
        for (key, value) in row_compat {
            compat.insert(key.clone(), value.clone());
        }
    }
    compat
}

fn model_type_name(model_type: ModelType) -> &'static str {
    match model_type {
        ModelType::Chat => "chat",
        ModelType::Image => "image",
        ModelType::Classifier => "classifier",
    }
}

fn flatten_model_catalog<T: DeserializeOwned>(
    provider: &str,
    groups: &ModelGroups,
    model_type: ModelType,
) -> IndexMap<String, T> {
    let wanted = model_type_name(model_type);
    let mut catalog = IndexMap::new();
    for (api, models) in groups
        .iter()
        .filter_map(|(api, models)| models.as_object().map(|models| (api, models)))
    {
        for model in models
            .values()
            .filter_map(Value::as_object)
            .filter(|model| model.get("type").and_then(Value::as_str) == Some(wanted))
        {
            let id = model
                .get("id")
                .and_then(Value::as_str)
                .expect("generated catalog models carry a string id")
                .to_owned();
            let mut model = model.clone();
            let row_compat = model.get("compat").and_then(Value::as_object);
            if let Some(compat) = with_provider_compat_defaults(provider, api, row_compat) {
                model.insert("compat".to_owned(), Value::Object(compat));
            }
            let parsed: T = serde_json::from_value(Value::Object(model))
                .unwrap_or_else(|error| panic!("generated catalog model {id} is invalid: {error}"));
            catalog.insert(id, parsed);
        }
    }
    catalog
}

/// Chat models of `groups` keyed by id.
///
/// # Panics
///
/// Panics when a generated chat entry does not match the chat model shape.
#[must_use]
pub fn flatten_chat_model_catalog(provider: &str, groups: &ModelGroups) -> ChatModelCatalog {
    flatten_model_catalog(provider, groups, ModelType::Chat)
}

/// Image models of `groups` keyed by id.
///
/// # Panics
///
/// Panics when a generated image entry does not match the image model shape.
#[must_use]
pub fn flatten_image_model_catalog(provider: &str, groups: &ModelGroups) -> ImageModelCatalog {
    flatten_model_catalog(provider, groups, ModelType::Image)
}

/// Classifier models of `groups` keyed by id.
///
/// # Panics
///
/// Panics when a generated classifier entry does not match the classifier
/// model shape.
#[must_use]
pub fn flatten_classifier_model_catalog(
    provider: &str,
    groups: &ModelGroups,
) -> ClassifierModelCatalog {
    flatten_model_catalog(provider, groups, ModelType::Classifier)
}

#[cfg(test)]
mod tests {
    use super::*;
    use eukhe_types::pi_ai::ModelCompat;

    #[test]
    fn every_provider_compat_default_is_typed_compat_of_its_api() {
        for (provider, apis) in PROVIDER_COMPAT.iter() {
            for (api, compat) in apis.as_object().expect("provider compat is keyed by api") {
                let typed = ModelCompat::from_json(api, compat.clone())
                    .unwrap_or_else(|error| panic!("{provider} {api}: {error}"));
                assert!(
                    !matches!(typed, ModelCompat::Other(_)),
                    "{provider} {api}: the api has no compat axes"
                );
                assert_eq!(
                    &serde_json::to_value(typed).expect("compat serializes"),
                    compat,
                    "{provider} {api}: every key is a declared compat axis"
                );
            }
        }
    }
}
