//! models.json, the one owner of the user's model configuration: the schema,
//! the comment-tolerant parse and validation (TS `stripJsonComments`,
//! `validateConfig`), the composition over a built-in model (provider
//! `baseUrl`/`compat`, TS `applyModelOverride`) and of the custom models (TS
//! `parseModels`), and the configured request auth (`apiKey`, `headers`,
//! `authHeader`). The registry (`ModelRegistry`) and the session collection
//! (`durable::models`) both read models.json through here, so the two
//! cannot disagree on it.
//!
//! Composition runs over the TS wire JSON of a model and lands on the
//! pi-ai [`Model`] (the request path's type and validation); the registry
//! takes its view of the result.

use std::collections::BTreeMap;
use std::path::Path;

use serde::{Deserialize, Serialize};
use serde_json::{json, Map, Value};

use eukhe_types::pi_ai::Model;

use crate::auth::resolve_config_value::resolve_config_value;

#[derive(Debug, Clone, Default, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub(crate) struct ModelCostConfig {
    pub input: Option<f64>,
    pub output: Option<f64>,
    pub cache_read: Option<f64>,
    pub cache_write: Option<f64>,
}

#[derive(Debug, Clone, Default, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub(crate) struct ModelDefinition {
    pub id: String,
    pub name: Option<String>,
    pub api: Option<String>,
    pub base_url: Option<String>,
    pub reasoning: Option<bool>,
    pub thinking_level_map: Option<BTreeMap<String, Option<String>>>,
    pub input: Option<Vec<String>>,
    pub cost: Option<ModelCostConfig>,
    pub context_window: Option<u64>,
    pub max_tokens: Option<u64>,
    pub headers: Option<BTreeMap<String, String>>,
    pub compat: Option<Value>,
}

#[derive(Debug, Clone, Default, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub(crate) struct ModelOverride {
    pub name: Option<String>,
    pub reasoning: Option<bool>,
    pub thinking_level_map: Option<BTreeMap<String, Option<String>>>,
    pub input: Option<Vec<String>>,
    pub cost: Option<ModelCostConfig>,
    pub context_window: Option<u64>,
    pub max_tokens: Option<u64>,
    pub headers: Option<BTreeMap<String, String>>,
    pub compat: Option<Value>,
}

#[derive(Debug, Clone, Default, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub(crate) struct ProviderConfig {
    pub name: Option<String>,
    pub base_url: Option<String>,
    pub api_key: Option<String>,
    pub api: Option<String>,
    pub headers: Option<BTreeMap<String, String>>,
    pub compat: Option<Value>,
    pub auth_header: Option<bool>,
    pub models: Option<Vec<ModelDefinition>>,
    pub model_overrides: Option<BTreeMap<String, ModelOverride>>,
}

/// The parsed and validated models.json document.
#[derive(Debug, Clone, Default, Deserialize)]
#[serde(default)]
pub(crate) struct ModelsConfig {
    pub providers: BTreeMap<String, ProviderConfig>,
}

/// `error` naming the models.json file, unless it already names it (TS
/// load failure format).
pub(crate) fn in_file(error: String, path: &Path) -> String {
    if error.contains("models.json") {
        error
    } else {
        format!("{error}\n\nFile: {}", path.display())
    }
}

impl ModelsConfig {
    /// Read, parse, and validate `path`; a missing file is the empty
    /// document. `is_built_in` answers whether a provider id has built-in
    /// models (those providers may add models without `baseUrl`/`apiKey`).
    ///
    /// # Errors
    ///
    /// The read, parse, or validation failure, naming the file.
    pub(crate) fn load(path: &Path, is_built_in: &dyn Fn(&str) -> bool) -> Result<Self, String> {
        let content = match std::fs::read_to_string(path) {
            Ok(content) => content,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                return Ok(Self::default())
            }
            Err(error) => {
                return Err(format!(
                    "Failed to load models.json: {error}\n\nFile: {}",
                    path.display()
                ))
            }
        };
        let config = Self::parse(&content)?;
        config
            .validate(is_built_in)
            .map_err(|error| in_file(error, path))?;
        Ok(config)
    }

    fn parse(content: &str) -> Result<Self, String> {
        serde_json::from_str(&strip_json_comments(content))
            .map_err(|error| format!("Invalid models.json: {error}"))
    }

    /// TS `validateConfig`: semantic checks beyond the schema.
    fn validate(&self, is_built_in: &dyn Fn(&str) -> bool) -> Result<(), String> {
        for (provider_name, provider_config) in &self.providers {
            let is_built_in = is_built_in(provider_name);
            let models = provider_config.models.as_deref().unwrap_or_default();
            let has_model_overrides = provider_config
                .model_overrides
                .as_ref()
                .is_some_and(|overrides| !overrides.is_empty());
            if models.is_empty() {
                if provider_config.base_url.is_none()
                    && provider_config.headers.is_none()
                    && provider_config.compat.is_none()
                    && !has_model_overrides
                {
                    return Err(format!(
                        "Provider {provider_name}: must specify \"baseUrl\", \"headers\", \"compat\", \"modelOverrides\", or \"models\"."
                    ));
                }
            } else if !is_built_in {
                if provider_config.base_url.is_none() {
                    return Err(format!(
                        "Provider {provider_name}: \"baseUrl\" is required when defining custom models."
                    ));
                }
                if provider_config.api_key.is_none() {
                    return Err(format!(
                        "Provider {provider_name}: \"apiKey\" is required when defining custom models."
                    ));
                }
            }
            for model in models {
                if provider_config.api.is_none() && model.api.is_none() && !is_built_in {
                    return Err(format!(
                        "Provider {provider_name}, model {}: no \"api\" specified. Set at provider or model level.",
                        model.id
                    ));
                }
                if model.id.is_empty() {
                    return Err(format!("Provider {provider_name}: model missing \"id\""));
                }
                if model.context_window == Some(0) {
                    return Err(format!(
                        "Provider {provider_name}, model {}: invalid contextWindow",
                        model.id
                    ));
                }
                if model.max_tokens == Some(0) {
                    return Err(format!(
                        "Provider {provider_name}, model {}: invalid maxTokens",
                        model.id
                    ));
                }
            }
        }
        Ok(())
    }
}

impl ProviderConfig {
    /// Whether [`Self::rewrite_built_in`] changes the built-in model
    /// `model_id`.
    pub(crate) fn rewrites(&self, model_id: &str) -> bool {
        self.base_url.is_some() || self.compat.is_some() || self.model_override(model_id).is_some()
    }

    fn model_override(&self, model_id: &str) -> Option<&ModelOverride> {
        self.model_overrides.as_ref()?.get(model_id)
    }

    /// Whether models.json configures `maxTokens` for `model_id` (a
    /// definition or an override): configuration, not catalog data.
    pub(crate) fn configures_max_tokens(&self, model_id: &str) -> bool {
        match self.definition(model_id) {
            Some(definition) => definition.max_tokens.is_some(),
            None => self
                .model_override(model_id)
                .is_some_and(|over| over.max_tokens.is_some()),
        }
    }

    /// The last definition of `model_id` (later definitions replace
    /// earlier ones).
    pub(crate) fn definition(&self, model_id: &str) -> Option<&ModelDefinition> {
        self.models
            .iter()
            .flatten()
            .rev()
            .find(|definition| definition.id == model_id)
    }

    /// A built-in model with this provider's `baseUrl` and `compat` and its
    /// `modelOverrides` entry deep-merged in.
    ///
    /// # Errors
    ///
    /// The rewritten model is not a valid model.
    pub(crate) fn rewrite_built_in(&self, model: &impl Serialize) -> Result<Model, String> {
        let Value::Object(mut object) = serde_json::to_value(model).map_err(|e| e.to_string())?
        else {
            return Err("a built-in model did not serialize to an object".to_owned());
        };
        if let Some(base_url) = &self.base_url {
            object.insert("baseUrl".to_owned(), json!(base_url));
        }
        if let Some(compat) = &self.compat {
            merge_compat(&mut object, compat);
        }
        let id = object.get("id").and_then(Value::as_str).unwrap_or_default();
        if let Some(over) = self.model_override(id) {
            over.apply(&mut object);
        }
        model_from(object)
    }

    /// The custom models this provider defines (later definitions of an id
    /// replace earlier ones). `defaults` is the provider's built-in
    /// `(api, baseUrl)`; a definition that resolves neither is skipped.
    ///
    /// # Errors
    ///
    /// A definition is not a valid model.
    pub(crate) fn custom_models(
        &self,
        provider_id: &str,
        defaults: Option<(&str, &str)>,
    ) -> Result<Vec<Model>, String> {
        let mut models: Vec<Model> = Vec::new();
        for definition in self.models.iter().flatten() {
            let api = (definition.api.as_deref())
                .or(self.api.as_deref())
                .or(defaults.map(|(api, _)| api));
            let base_url = (definition.base_url.as_deref())
                .or(self.base_url.as_deref())
                .or(defaults.map(|(_, base_url)| base_url));
            let (Some(api), Some(base_url)) = (api, base_url) else {
                continue;
            };
            let cost = definition.cost.clone().unwrap_or_default();
            let mut object = Map::new();
            object.insert("id".to_owned(), json!(definition.id));
            object.insert(
                "name".to_owned(),
                json!(definition.name.as_ref().unwrap_or(&definition.id)),
            );
            object.insert("api".to_owned(), json!(api));
            object.insert("provider".to_owned(), json!(provider_id));
            object.insert("baseUrl".to_owned(), json!(base_url));
            object.insert(
                "reasoning".to_owned(),
                json!(definition.reasoning.unwrap_or(false)),
            );
            if let Some(map) = &definition.thinking_level_map {
                object.insert("thinkingLevelMap".to_owned(), json!(map));
            }
            object.insert("input".to_owned(), inputs(definition.input.as_ref()));
            object.insert(
                "cost".to_owned(),
                json!({
                    "input": cost.input.unwrap_or(0.0),
                    "output": cost.output.unwrap_or(0.0),
                    "cacheRead": cost.cache_read.unwrap_or(0.0),
                    "cacheWrite": cost.cache_write.unwrap_or(0.0),
                }),
            );
            object.insert(
                "contextWindow".to_owned(),
                json!(definition.context_window.unwrap_or(128_000)),
            );
            object.insert(
                "maxTokens".to_owned(),
                json!(definition.max_tokens.unwrap_or(16_384)),
            );
            if let Some(headers) = definition.headers.as_ref().filter(|h| !h.is_empty()) {
                object.insert("headers".to_owned(), json!(headers));
            }
            if let Some(compat) = &self.compat {
                merge_compat(&mut object, compat);
            }
            let model = model_from(object)?;
            match models.iter().position(|entry| entry.id == model.id) {
                Some(index) => models[index] = model,
                None => models.push(model),
            }
        }
        Ok(models)
    }

    /// The configured `apiKey`, resolved (`!command`, environment variable
    /// name, or literal). Blocking: a command key runs the command.
    pub(crate) fn configured_api_key(&self) -> Option<String> {
        self.api_key.as_deref().and_then(resolve_config_value)
    }

    /// Whether the configured headers alone authenticate the provider:
    /// non-empty headers, and no `authHeader` (which needs a key).
    pub(crate) fn authenticates_with_headers(&self) -> bool {
        self.headers
            .as_ref()
            .is_some_and(|headers| !headers.is_empty())
            && !self.auth_header.unwrap_or(false)
    }

    /// The models.json request auth of the provider: the configured `apiKey`
    /// or the configured headers alone.
    pub(crate) fn has_request_auth(&self) -> bool {
        self.authenticates_with_headers() || self.configured_api_key().is_some()
    }

    /// Under `authHeader`, the `Authorization: Bearer <api_key>` header.
    ///
    /// # Errors
    ///
    /// `authHeader` is set and no API key resolved.
    pub(crate) fn bearer_header(
        &self,
        provider_id: &str,
        api_key: Option<&str>,
    ) -> Result<Option<(String, String)>, String> {
        if !self.auth_header.unwrap_or(false) {
            return Ok(None);
        }
        let Some(api_key) = api_key else {
            return Err(format!("No API key found for \"{provider_id}\""));
        };
        Ok(Some((
            "Authorization".to_owned(),
            format!("Bearer {api_key}"),
        )))
    }

    /// The model-level request headers models.json configures for
    /// `model_id`: its definition's, else its override's.
    pub(crate) fn model_headers(&self, model_id: &str) -> Option<&BTreeMap<String, String>> {
        match self.definition(model_id) {
            Some(definition) => definition.headers.as_ref(),
            None => self.model_override(model_id)?.headers.as_ref(),
        }
    }
}

impl ModelOverride {
    /// TS `applyModelOverride` over a model's wire JSON: scalar fields
    /// replace, the thinking-level map, cost, compat, and headers merge.
    fn apply(&self, object: &mut Map<String, Value>) {
        if let Some(name) = &self.name {
            object.insert("name".to_owned(), json!(name));
        }
        if let Some(reasoning) = self.reasoning {
            object.insert("reasoning".to_owned(), json!(reasoning));
        }
        if let Some(map) = &self.thinking_level_map {
            merge_at(object, "thinkingLevelMap", |merged| {
                merged.extend(
                    map.iter()
                        .map(|(level, value)| (level.clone(), json!(value))),
                );
            });
        }
        if let Some(input) = &self.input {
            object.insert("input".to_owned(), inputs(Some(input)));
        }
        if let Some(window) = self.context_window {
            object.insert("contextWindow".to_owned(), json!(window));
        }
        if let Some(max_tokens) = self.max_tokens {
            object.insert("maxTokens".to_owned(), json!(max_tokens));
        }
        if let (Some(cost), Some(Value::Object(base))) = (&self.cost, object.get_mut("cost")) {
            for (field, value) in [
                ("input", cost.input),
                ("output", cost.output),
                ("cacheRead", cost.cache_read),
                ("cacheWrite", cost.cache_write),
            ] {
                if let Some(value) = value {
                    base.insert(field.to_owned(), json!(value));
                }
            }
        }
        if let Some(compat) = &self.compat {
            merge_compat(object, compat);
        }
        if let Some(headers) = &self.headers {
            merge_at(object, "headers", |merged| {
                merged.extend(
                    headers
                        .iter()
                        .map(|(name, value)| (name.clone(), json!(value))),
                );
            });
        }
    }
}

/// `object[key]` merged by `merge`, a missing or non-object value starting
/// from `{}`.
fn merge_at(
    object: &mut Map<String, Value>,
    key: &str,
    merge: impl FnOnce(&mut Map<String, Value>),
) {
    let mut merged = if let Some(Value::Object(existing)) = object.remove(key) {
        existing
    } else {
        Map::new()
    };
    merge(&mut merged);
    object.insert(key.to_owned(), Value::Object(merged));
}

/// TS `mergeCompat`: override fields win and the routing sub-objects merge.
/// A non-object override changes nothing.
fn merge_compat(object: &mut Map<String, Value>, over: &Value) {
    let Value::Object(over) = over else {
        return;
    };
    merge_at(object, "compat", |compat| {
        for (key, value) in over {
            if matches!(key.as_str(), "openRouterRouting" | "vercelGatewayRouting") {
                if let (Some(Value::Object(existing)), Value::Object(incoming)) =
                    (compat.get_mut(key), value)
                {
                    existing.extend(incoming.clone());
                    continue;
                }
            }
            compat.insert(key.clone(), value.clone());
        }
    });
}

/// The input modalities: anything but "image" is text; unset is text only.
fn inputs(values: Option<&Vec<String>>) -> Value {
    values.map_or_else(
        || json!(["text"]),
        |items| {
            items
                .iter()
                .map(|item| json!(if item == "image" { "image" } else { "text" }))
                .collect()
        },
    )
}

fn model_from(object: Map<String, Value>) -> Result<Model, String> {
    let label = |key: &str| {
        object
            .get(key)
            .and_then(Value::as_str)
            .unwrap_or_default()
            .to_owned()
    };
    let (provider, id) = (label("provider"), label("id"));
    serde_json::from_value(Value::Object(object))
        .map_err(|error| format!("Provider {provider}, model {id}: {error}"))
}

/// Strip `//` line comments and trailing commas, leaving strings intact.
fn strip_json_comments(input: &str) -> String {
    let chars: Vec<char> = input.chars().collect();
    let uncommented = retain_outside_strings(&chars, |rest| {
        if rest.starts_with(&['/', '/']) {
            rest.iter().position(|&c| c == '\n').unwrap_or(rest.len())
        } else {
            0
        }
    });
    retain_outside_strings(&uncommented, |rest| {
        let closes = rest[1..]
            .iter()
            .find(|c| !c.is_whitespace())
            .is_some_and(|c| matches!(c, '}' | ']'));
        usize::from(rest[0] == ',' && closes)
    })
    .into_iter()
    .collect()
}

/// `chars` without the runs `skip` marks outside JSON string literals: at
/// each position outside a string, `skip(rest)` is how many chars to drop.
fn retain_outside_strings(chars: &[char], skip: impl Fn(&[char]) -> usize) -> Vec<char> {
    let mut out = Vec::with_capacity(chars.len());
    let (mut index, mut in_string, mut escaped) = (0, false, false);
    while let Some(&c) = chars.get(index) {
        if in_string {
            in_string = escaped || c != '"';
            escaped = !escaped && c == '\\';
        } else {
            let dropped = skip(&chars[index..]);
            if dropped > 0 {
                index += dropped;
                continue;
            }
            in_string = c == '"';
        }
        out.push(c);
        index += 1;
    }
    out
}

#[cfg(test)]
mod tests {
    use eukhe_types::pi_ai::ModelThinkingLevel;

    use super::*;

    fn provider(document: &str) -> ProviderConfig {
        let config = ModelsConfig::parse(document).unwrap();
        config.validate(&|_| false).unwrap();
        config.providers.into_values().next().unwrap()
    }

    #[test]
    fn strips_comments_and_trailing_commas() {
        let input = r#"{
            // a comment
            "providers": {
                "ollama": { "baseUrl": "http://localhost", "apiKey": "x // kept", }, // trailing
            },
        }"#;
        let parsed: Value = serde_json::from_str(&strip_json_comments(input)).unwrap();
        assert_eq!(parsed["providers"]["ollama"]["apiKey"], "x // kept");
    }

    #[test]
    fn validates_custom_provider_requirements() {
        let config = ModelsConfig::parse(
            r#"{ "providers": { "custom": { "baseUrl": "http://x", "models": [ { "id": "m" } ] } } }"#,
        )
        .unwrap();
        // Custom provider without apiKey fails.
        let error = config.validate(&|_| false).unwrap_err();
        assert!(error.contains("apiKey"));
        // Built-in providers are exempt.
        assert!(config.validate(&|p| p == "custom").is_ok());
    }

    #[test]
    fn parses_custom_models_with_defaults() {
        let config = provider(
            r#"{ "providers": { "ollama": {
                "baseUrl": "http://localhost:11434",
                "apiKey": "none",
                "api": "openai-completions",
                "models": [ { "id": "llama3", "name": "Llama 3" }, { "id": "bare" } ]
            } } }"#,
        );
        let models = config.custom_models("ollama", None).unwrap();
        assert_eq!(models[0].id, "llama3");
        assert_eq!(models[0].base_url, "http://localhost:11434");
        assert_eq!(models[0].context_window, 128_000);
        // A custom model that omits `maxTokens` defaults to 16384 and stays
        // catalog-like: only a configured value is explicit.
        assert_eq!(models[1].max_tokens, 16_384);
        assert!(!config.configures_max_tokens("bare"));
    }

    /// TS `thinkingLevelMap: modelDef.thinkingLevelMap`: a model
    /// definition's map is the model's, so a locally-defined route that
    /// declares addressable thinking levels keeps them.
    #[test]
    fn parses_a_custom_model_definition_thinking_level_map() {
        let config = provider(
            r#"{ "providers": { "battery": {
                "baseUrl": "http://127.0.0.1:9", "apiKey": "sk-local",
                "api": "openai-completions",
                "models": [ { "id": "chat-plus", "reasoning": false,
                              "thinkingLevelMap": { "off": null, "xhigh": "xhigh" } } ]
            } } }"#,
        );
        let models = config.custom_models("battery", None).unwrap();
        let map = models[0].thinking_level_map.as_ref().unwrap();
        assert_eq!(map.get(&ModelThinkingLevel::Off), Some(&None));
        assert_eq!(
            map.get(&ModelThinkingLevel::Xhigh),
            Some(&Some("xhigh".to_owned()))
        );
    }

    /// An unknown thinking level fails the model (both views reject it)
    /// instead of silently dropping the whole map.
    #[test]
    fn an_unknown_thinking_level_fails_the_model() {
        let config = provider(
            r#"{ "providers": { "battery": {
                "baseUrl": "http://127.0.0.1:9", "apiKey": "k", "api": "openai-completions",
                "models": [ { "id": "m", "thinkingLevelMap": { "ultra": "u" } } ]
            } } }"#,
        );
        let error = config.custom_models("battery", None).unwrap_err();
        assert!(error.starts_with("Provider battery, model m: "), "{error}");
    }

    /// TS `755-configured-max-tokens.test.ts`: a models.json `maxTokens`
    /// (a definition's or an override's) is configuration.
    #[test]
    fn a_configured_max_tokens_is_explicit() {
        let config = provider(
            r#"{ "providers": { "glm-h200": {
                "baseUrl": "http://vllm.example.test:8000/v1", "api": "openai-completions",
                "apiKey": "TEST_KEY",
                "models": [ { "id": "glm-5.2", "contextWindow": 393216, "maxTokens": 131072 } ],
                "modelOverrides": { "built-in": { "maxTokens": 200000 }, "renamed": { "name": "R" } }
            } } }"#,
        );
        assert_eq!(
            config.custom_models("glm-h200", None).unwrap()[0].max_tokens,
            131_072
        );
        assert!(config.configures_max_tokens("glm-5.2"));
        assert!(config.configures_max_tokens("built-in"));
        assert!(!config.configures_max_tokens("renamed"));
    }

    #[test]
    fn model_overrides_merge_into_the_built_in_model() {
        let config = provider(
            r#"{ "providers": { "p": { "modelOverrides": { "m": {
                "name": "Renamed", "contextWindow": 2000, "cost": { "output": 9 },
                "thinkingLevelMap": { "xhigh": "xhigh" }, "headers": { "X-Over": "1" }
            } } } } }"#,
        );
        let base = json!({
            "id": "m", "name": "M", "api": "openai-completions", "provider": "p",
            "baseUrl": "http://x", "reasoning": false, "input": ["text"],
            "cost": { "input": 1, "output": 2, "cacheRead": 0, "cacheWrite": 0 },
            "contextWindow": 1000, "maxTokens": 100,
            "compat": { "supportsStore": false }
        });
        let merged = config.rewrite_built_in(&base).unwrap();
        assert_eq!(merged.name, "Renamed");
        assert_eq!(merged.context_window, 2000);
        assert_eq!((merged.cost.input, merged.cost.output), (1.0, 9.0));
        // A map merges in even when the built-in model has none.
        assert_eq!(
            merged
                .thinking_level_map
                .unwrap()
                .get(&ModelThinkingLevel::Xhigh),
            Some(&Some("xhigh".to_owned()))
        );
        // An override without compat keeps the model's compat.
        assert_eq!(
            serde_json::to_value(merged.compat).unwrap(),
            json!({ "supportsStore": false })
        );
        assert_eq!(merged.headers.unwrap()["X-Over"], "1");
    }

    #[test]
    fn compat_routing_sub_objects_merge() {
        let mut object = Map::new();
        object.insert(
            "compat".to_owned(),
            json!({ "openRouterRouting": { "only": ["a"] }, "kept": 1 }),
        );
        merge_compat(
            &mut object,
            &json!({ "openRouterRouting": { "order": ["b"] }, "added": 2 }),
        );
        assert_eq!(
            object["compat"],
            json!({
                "openRouterRouting": { "only": ["a"], "order": ["b"] },
                "kept": 1, "added": 2
            })
        );
    }

    #[test]
    fn request_auth_from_the_provider_config() {
        let headers_only = provider(r#"{ "providers": { "p": { "headers": { "X-K": "v" } } } }"#);
        assert!(headers_only.has_request_auth());
        let bearer = provider(
            r#"{ "providers": { "p": { "headers": { "X-K": "v" }, "authHeader": true } } }"#,
        );
        // `authHeader` needs a key: headers alone do not authenticate.
        assert!(!bearer.has_request_auth());
        assert_eq!(
            bearer.bearer_header("p", None).unwrap_err(),
            "No API key found for \"p\""
        );
        assert_eq!(
            bearer.bearer_header("p", Some("k")).unwrap(),
            Some(("Authorization".to_owned(), "Bearer k".to_owned()))
        );
        assert_eq!(headers_only.bearer_header("p", None).unwrap(), None);
    }
}
