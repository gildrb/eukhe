//! Port of the `models.*` globals of code mode scripts
//! (`codemode/models.ts`): the catalog functions and the internal tools
//! behind `models.classify()` and `models.generateImages()`.

use std::future::Future;
use std::sync::Arc;

use eukhe_ai::auth::AuthOperationOptions;
use eukhe_ai::models::{Models, ModelsClassifierOptions, ModelsImagesOptions};
use eukhe_ai::typebox::Type;
use eukhe_chord::context::Context;
use eukhe_chord::json::{to_json, JsonValue};
use eukhe_types::pi_ai::{
    AnyModel, ClassifierContext, ClassifierModel, ImagesContext, JsonValue as PiJsonValue,
    ModelType, TextContent, Usage, UserContentBlock,
};
use futures::future::BoxFuture;
use serde::Serialize;

use crate::harness::define::define_tool;
use crate::harness::types::{ToolCaller, ToolExecutionApi, ToolExecutionResult, ToolRegistration};
use crate::session::{SessionError, SessionResult};

/// Why the embedding could not resolve the session's default classifier:
/// its own error, whose Display is the message the script gets.
pub type ClassifierResolveError = Box<dyn std::error::Error + Send + Sync + 'static>;

/// Resolves the classifier of a `models.classify()` call whose model is
/// `null` or `undefined`, from the session's model collection and the
/// calling conversation's chat model (`provider/id`; empty: none).
pub type ClassifierResolver = Arc<
    dyn Fn(Models, String) -> BoxFuture<'static, Result<ClassifierModel, ClassifierResolveError>>
        + Send
        + Sync,
>;

/// How `models.classify()` gets its model when the script names none.
#[derive(Clone)]
pub enum ClassifierDefault {
    /// No default: the script names a classifier model (the TS behavior).
    Unset,
    /// The embedding resolves one (eukhe: the `judge` role).
    Resolver(ClassifierResolver),
}

impl std::fmt::Debug for ClassifierDefault {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ClassifierDefault::Unset => formatter.write_str("Unset"),
            ClassifierDefault::Resolver(_) => formatter.write_str("Resolver(..)"),
        }
    }
}

/// Reserved names of code mode's internal tools; they are never listed to
/// scripts or the model.
pub const CODEMODE_INTERNAL_PREFIX: &str = "pi.codemode.";
/// The internal tool behind `models.classify()`.
pub(crate) const CLASSIFY_TOOL: &str = "pi.codemode.models.classify";
/// The internal tool behind `models.generateImages()`.
pub(crate) const GENERATE_IMAGES_TOOL: &str = "pi.codemode.models.generateImages";

/// `MODEL_CALLS`: the internal tool behind a script global
/// (`models.classify` → [`CLASSIFY_TOOL`], `models.generateImages` →
/// [`GENERATE_IMAGES_TOOL`]).
pub(crate) fn model_call_tool(global: &str) -> Option<&'static str> {
    match global {
        "models.classify" => Some(CLASSIFY_TOOL),
        "models.generateImages" => Some(GENERATE_IMAGES_TOOL),
        _ => None,
    }
}

/// The globals of `MODEL_CALLS`, in `Object.keys` order.
pub(crate) const MODEL_CALL_GLOBALS: [&str; 2] = ["models.classify", "models.generateImages"];

/// The catalog functions, host globals of the `models` namespace.
pub(crate) const CATALOG_GLOBALS: [&str; 3] = [
    "models.getModelsOfType",
    "models.getAvailableOfType",
    "models.getModelOfType",
];

/// `models.classify()` and `models.generateImages()` calls one script may
/// have in flight; the rest wait.
pub(crate) const MAX_CONCURRENT_MODEL_CALLS: usize = 4;

/// The `models` section of the code mode tool description.
pub(crate) const MODELS_DESCRIPTION: &str = concat!(
    "`models` (async):\n",
    "- `models.getModelsOfType(type, provider?)`, `models.getAvailableOfType(type, provider?)` (authed only), `models.getModelOfType(type, provider, id)`; `type`: \"chat\"|\"image\"|\"classifier\".\n",
    "- `models.classify(model, { state, images?: [image blocks], questions: { <id>: { type, instructions, criteria } } })` → `{ answers: { <id>: ... }, stopReason, errorMessage?, usage? }`; `type` \"choice\" (criteria `{ <label>: <meaning> }`), \"score\" (`[<lowest>, ..., <highest>]`) or \"bool\" (`{ true: <meaning>, false: <meaning> }`).\n",
    "- `models.generateImages(model, { input: [{ type: \"text\", text }, ...image blocks] })` → `{ output: [image blocks], stopReason, errorMessage?, usage? }`; show with `image(block)`.\n",
    "At most 4 classify/generateImages calls run at once.",
);

/// The line [`MODELS_DESCRIPTION`] gains with a
/// [`ClassifierDefault::Resolver`].
pub(crate) const CLASSIFIER_DEFAULT_DESCRIPTION: &str =
    "`models.classify(null, ...)` uses the session's default classifier.";

fn record(value: Option<&PiJsonValue>) -> Option<&serde_json::Map<String, PiJsonValue>> {
    value.and_then(PiJsonValue::as_object)
}

/// `JSON.stringify(value)`; `undefined` for an absent value.
fn stringify(value: Option<&PiJsonValue>) -> String {
    match value {
        None => "undefined".to_owned(),
        Some(value) => match to_json(value) {
            Ok(json) => json.to_string(),
            // Parsed JSON is always strict JSON; serde's text is the closest
            // rendering of anything else.
            Err(_) => value.to_string(),
        },
    }
}

/// A script value in an error message: `undefined`, `a string`, `an array`,
/// or its keys (`{ prompt }`).
fn describe_value(value: Option<&PiJsonValue>) -> String {
    match value {
        None => "undefined".to_owned(),
        Some(PiJsonValue::Null) => "null".to_owned(),
        Some(PiJsonValue::Array(items)) => {
            let described = if items.is_empty() {
                "an empty array"
            } else {
                "an array"
            };
            described.to_owned()
        }
        Some(PiJsonValue::Object(object)) => {
            if object.is_empty() {
                return "{}".to_owned();
            }
            let keys: Vec<&str> = object.keys().take(6).map(String::as_str).collect();
            let more = if object.len() > 6 { ", ..." } else { "" };
            format!("{{ {}{more} }}", keys.join(", "))
        }
        Some(PiJsonValue::String(_)) => "a string".to_owned(),
        Some(PiJsonValue::Number(_)) => "a number".to_owned(),
        Some(PiJsonValue::Bool(_)) => "a boolean".to_owned(),
    }
}

/// `an image`, `a classifier`.
fn with_article(word: &str) -> String {
    let article = if word.starts_with(['a', 'e', 'i', 'o', 'u']) {
        "an"
    } else {
        "a"
    };
    format!("{article} {word}")
}

/// `List the <type> models you can use with ...`: the hint of a model
/// argument that resolves to no model of the wanted type.
fn list_hint(model_type: ModelType) -> String {
    let type_name = model_type.as_str();
    format!(
        "List the {type_name} models you can use with models.getAvailableOfType(\"{type_name}\")."
    )
}

/// Why a `models.*` call of a script fails; its Display is the message of
/// the Error the script gets.
#[derive(Debug, thiserror::Error)]
pub(crate) enum ModelsCallError {
    /// `got` is the `JSON.stringify` of the type argument.
    #[error("Unknown model type {got}. Use \"chat\", \"image\", or \"classifier\".")]
    UnknownModelType { got: String },
    #[error("provider must be a string")]
    ProviderNotString,
    /// A catalog entry did not serialize.
    #[error("{source}")]
    ModelInfo {
        #[source]
        source: serde_json::Error,
    },
    /// A catalog entry or a call's result is not strict JSON.
    #[error("{source}")]
    NotStrictJson {
        #[source]
        source: eukhe_chord::json::JsonError,
    },
    /// The checked context did not read as the request context of `name()`.
    #[error("{name}() could not read its context: {source}")]
    ReadContext {
        name: String,
        #[source]
        source: serde_json::Error,
    },
    /// `name()` resolved a model of another type.
    #[error(
        "{name}() resolved {}, not the requested model type",
        with_article(.resolved.as_str())
    )]
    ResolvedWrongType { name: String, resolved: ModelType },
    /// Listing the models with configured auth failed (the thrown value).
    #[error("{source}")]
    Available {
        #[source]
        source: eukhe_chord::context::AbortReason,
    },
    /// `got` describes each argument.
    #[error("models.getModelOfType(type, provider, id) expects three strings, got ({got}). The provider and the id are separate arguments, for example models.getModelOfType(\"classifier\", \"typesafe\", \"jev-latest\").")]
    ModelOfTypeArguments { got: String },
    #[error("models.classify() {problem}. Expected context: {CLASSIFIER_CONTEXT_SHAPE}.")]
    ClassifierContext { problem: ContextProblem },
    #[error("models.generateImages() {problem}. Expected context: {{ input: [{{ type: \"text\", text: <prompt> }}, ...optional {{ type: \"image\", data: <base64>, mimeType }} references] }}.")]
    ImagesContext { problem: ContextProblem },
    /// The model argument of `name()` names no provider and id; `absent`:
    /// it is `null` or `undefined`.
    #[error(
        "{name}() expects {} model as its first argument, got {got}.{} {}",
        with_article(.wanted.as_str()),
        if *.absent { " models.getModelOfType() returns undefined for an unknown provider or id." } else { "" },
        list_hint(*.wanted)
    )]
    NotAModel {
        name: String,
        wanted: ModelType,
        got: String,
        absent: bool,
    },
    /// `provider/id` is a model of another type.
    #[error(
        "\"{provider}/{id}\" is {} model, not {} model. {}",
        with_article(.actual.as_str()),
        with_article(.wanted.as_str()),
        list_hint(*.wanted)
    )]
    WrongModelType {
        provider: String,
        id: String,
        actual: ModelType,
        wanted: ModelType,
    },
    #[error("Unknown {} model \"{provider}/{id}\". {}", .wanted.as_str(), list_hint(*.wanted))]
    UnknownModel {
        provider: String,
        id: String,
        wanted: ModelType,
    },
}

/// What is wrong with the context argument of `models.classify()` or
/// `models.generateImages()`; each `got` describes the script's value.
#[derive(Debug, thiserror::Error)]
pub(crate) enum ContextProblem {
    #[error("expects a context object as its second argument, got {got}")]
    NotAnObject { got: String },
    #[error("context.state must be an object, got {got}")]
    StateNotAnObject { got: String },
    #[error("context.images must be an array, got {got}")]
    ImagesNotAnArray { got: String },
    #[error("context.images[{index}] must be an image block, got {got}")]
    NotAnImageBlock { index: usize, got: String },
    #[error("context.questions must map question IDs to questions, got {got}")]
    NoQuestions { got: String },
    #[error("context.questions.{id} must be a question object, got {got}")]
    QuestionNotAnObject { id: String, got: String },
    #[error("context.questions.{id}.instructions must be a string")]
    NoInstructions { id: String },
    #[error(
        "context.questions.{id} is a \"choice\" question, so criteria must map each label to its meaning"
    )]
    ChoiceCriteria { id: String },
    #[error(
        "context.questions.{id} is a \"score\" question, so criteria must list the levels as strings, lowest first"
    )]
    ScoreCriteria { id: String },
    #[error(
        "context.questions.{id} is a \"bool\" question, so criteria must be {{ true: string, false: string }}"
    )]
    BoolCriteria { id: String },
    /// `got` is the `JSON.stringify` of the type.
    #[error("context.questions.{id}.type must be \"choice\", \"score\", or \"bool\", got {got}")]
    QuestionType { id: String, got: String },
    #[error("context.input must be a non-empty array of blocks, got {got}")]
    NoInput { got: String },
    #[error("context.input[{index}] must be a text or image block, got {got}")]
    NotAnInputBlock { index: usize, got: String },
}

fn to_model_type(value: Option<&PiJsonValue>) -> Result<ModelType, ModelsCallError> {
    value
        .and_then(PiJsonValue::as_str)
        .and_then(ModelType::parse)
        .ok_or_else(|| ModelsCallError::UnknownModelType {
            got: stringify(value),
        })
}

fn to_provider(value: Option<&PiJsonValue>) -> Result<Option<&str>, ModelsCallError> {
    match value {
        None | Some(PiJsonValue::Null) => Ok(None),
        Some(PiJsonValue::String(provider)) => Ok(Some(provider.as_str())),
        Some(_) => Err(ModelsCallError::ProviderNotString),
    }
}

/// Catalog entry for scripts. `headers` is dropped because configured
/// headers can carry credentials.
fn to_model_info(model: &AnyModel) -> Result<JsonValue, ModelsCallError> {
    let mut info =
        serde_json::to_value(model).map_err(|source| ModelsCallError::ModelInfo { source })?;
    if let Some(object) = info.as_object_mut() {
        object.remove("headers");
    }
    to_json(&info).map_err(|source| ModelsCallError::NotStrictJson { source })
}

fn model_infos(models: &[AnyModel]) -> Result<JsonValue, ModelsCallError> {
    let infos = models
        .iter()
        .map(to_model_info)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(JsonValue::from(infos))
}

/// `catalogCall`: what a script's call of catalog global `name` with its
/// spread argument list `args` (a JSON array after the JS round trip;
/// `None` = undefined) resolves to. `Ok(None)` = undefined. `Err` = the
/// thrown Error.
pub(crate) async fn catalog_call(
    name: &str,
    args: Option<&JsonValue>,
    models: &Models,
    cx: &Context,
) -> Result<Option<JsonValue>, ModelsCallError> {
    let list = match args.map(serde_json::Value::from) {
        Some(PiJsonValue::Array(items)) => items,
        Some(_) | None => Vec::new(),
    };
    let (type_arg, provider, id) = (list.first(), list.get(1), list.get(2));
    if name == "models.getModelsOfType" {
        let found = models.get_models_of_type(to_model_type(type_arg)?, to_provider(provider)?);
        return model_infos(&found).map(Some);
    }
    if name == "models.getAvailableOfType" {
        let model_type = to_model_type(type_arg)?;
        let available = models
            .get_available_of_type(
                model_type,
                to_provider(provider)?,
                AuthOperationOptions {
                    signal: cx.abort_signal(),
                },
            )
            .await
            .map_err(|source| ModelsCallError::Available { source })?;
        return model_infos(&available).map(Some);
    }
    let (Some(PiJsonValue::String(provider)), Some(PiJsonValue::String(id))) = (provider, id)
    else {
        let described: Vec<String> = list
            .iter()
            .map(|value| describe_value(Some(value)))
            .collect();
        return Err(ModelsCallError::ModelOfTypeArguments {
            got: described.join(", "),
        });
    };
    models
        .get_model_of_type(to_model_type(type_arg)?, provider, id)
        .as_ref()
        .map(to_model_info)
        .transpose()
}

const CLASSIFIER_CONTEXT_SHAPE: &str = "{ state: { ... }, images?: [{ type: \"image\", data: <base64>, mimeType }], questions: { <id>: { type: \"choice\", instructions, criteria: { <label>: <meaning> } } | { type: \"score\", instructions, criteria: [<lowest level>, ..., <highest level>] } | { type: \"bool\", instructions, criteria: { true: <meaning>, false: <meaning> } } } }";

fn is_image_block(value: &PiJsonValue) -> bool {
    value.as_object().is_some_and(|block| {
        block.get("type").and_then(PiJsonValue::as_str) == Some("image")
            && block.get("data").is_some_and(PiJsonValue::is_string)
            && block.get("mimeType").is_some_and(PiJsonValue::is_string)
    })
}

fn is_strings<'a>(mut values: impl ExactSizeIterator<Item = &'a PiJsonValue>) -> bool {
    values.len() > 0 && values.all(PiJsonValue::is_string)
}

/// Check a script's classifier context, so mistakes fail with the expected
/// shape instead of a provider error.
fn check_classifier_context(context: Option<&PiJsonValue>) -> Result<(), ModelsCallError> {
    let fail = |problem: ContextProblem| Err(ModelsCallError::ClassifierContext { problem });
    let Some(object) = record(context) else {
        return fail(ContextProblem::NotAnObject {
            got: describe_value(context),
        });
    };
    let state = object.get("state");
    if record(state).is_none() {
        return fail(ContextProblem::StateNotAnObject {
            got: describe_value(state),
        });
    }
    if let Some(images) = object.get("images") {
        let PiJsonValue::Array(images) = images else {
            return fail(ContextProblem::ImagesNotAnArray {
                got: describe_value(Some(images)),
            });
        };
        if let Some((index, image)) = images
            .iter()
            .enumerate()
            .find(|(_, image)| !is_image_block(image))
        {
            return fail(ContextProblem::NotAnImageBlock {
                index,
                got: describe_value(Some(image)),
            });
        }
    }
    let questions = object.get("questions");
    let Some(questions_map) = record(questions).filter(|map| !map.is_empty()) else {
        return fail(ContextProblem::NoQuestions {
            got: describe_value(questions),
        });
    };
    for (id, question) in questions_map {
        let Some(question) = question.as_object() else {
            return fail(ContextProblem::QuestionNotAnObject {
                id: id.clone(),
                got: describe_value(Some(question)),
            });
        };
        if !question
            .get("instructions")
            .is_some_and(PiJsonValue::is_string)
        {
            return fail(ContextProblem::NoInstructions { id: id.clone() });
        }
        let criteria = question.get("criteria");
        let question_type = question.get("type");
        match question_type.and_then(PiJsonValue::as_str) {
            Some("choice") => {
                if !record(criteria).is_some_and(|map| is_strings(map.values())) {
                    return fail(ContextProblem::ChoiceCriteria { id: id.clone() });
                }
            }
            Some("score") => {
                if !criteria
                    .and_then(PiJsonValue::as_array)
                    .is_some_and(|levels| is_strings(levels.iter()))
                {
                    return fail(ContextProblem::ScoreCriteria { id: id.clone() });
                }
            }
            Some("bool") => {
                if !record(criteria).is_some_and(|map| {
                    map.get("true").is_some_and(PiJsonValue::is_string)
                        && map.get("false").is_some_and(PiJsonValue::is_string)
                }) {
                    return fail(ContextProblem::BoolCriteria { id: id.clone() });
                }
            }
            Some(_) | None => {
                return fail(ContextProblem::QuestionType {
                    id: id.clone(),
                    got: stringify(question_type),
                });
            }
        }
    }
    Ok(())
}

/// Check a script's image context, so mistakes such as `{ prompt }` fail
/// with the expected shape.
fn check_images_context(context: Option<&PiJsonValue>) -> Result<(), ModelsCallError> {
    let fail = |problem: ContextProblem| Err(ModelsCallError::ImagesContext { problem });
    let Some(object) = record(context) else {
        return fail(ContextProblem::NotAnObject {
            got: describe_value(context),
        });
    };
    let input = object.get("input");
    let Some(blocks) = input
        .and_then(PiJsonValue::as_array)
        .filter(|blocks| !blocks.is_empty())
    else {
        return fail(ContextProblem::NoInput {
            got: describe_value(input),
        });
    };
    let is_text = |block: &PiJsonValue| {
        block.as_object().is_some_and(|block| {
            block.get("type").and_then(PiJsonValue::as_str) == Some("text")
                && block.get("text").is_some_and(PiJsonValue::is_string)
        })
    };
    match blocks
        .iter()
        .enumerate()
        .find(|(_, block)| !is_text(block) && !is_image_block(block))
    {
        Some((index, block)) => fail(ContextProblem::NotAnInputBlock {
            index,
            got: describe_value(Some(block)),
        }),
        None => Ok(()),
    }
}

/// Resolve the script's model by provider and id only, so a script-supplied
/// baseUrl or headers never receive the credentials, with errors that say
/// what to do.
fn resolve_model(
    name: &str,
    model_type: ModelType,
    model: Option<&PiJsonValue>,
    models: &Models,
) -> Result<AnyModel, ModelsCallError> {
    let fields = record(model).and_then(|object| {
        Some((
            object.get("provider")?.as_str()?,
            object.get("id")?.as_str()?,
        ))
    });
    let Some((provider, id)) = fields else {
        return Err(ModelsCallError::NotAModel {
            name: name.to_owned(),
            wanted: model_type,
            got: describe_value(model),
            absent: matches!(model, None | Some(PiJsonValue::Null)),
        });
    };
    if let Some(resolved) = models.get_model_of_type(model_type, provider, id) {
        return Ok(resolved);
    }
    let actual_type = ModelType::ALL.iter().copied().find(|&other| {
        other != model_type && models.get_model_of_type(other, provider, id).is_some()
    });
    let (provider, id) = (provider.to_owned(), id.to_owned());
    Err(match actual_type {
        Some(actual) => ModelsCallError::WrongModelType {
            provider,
            id,
            actual,
            wanted: model_type,
        },
        None => ModelsCallError::UnknownModel {
            provider,
            id,
            wanted: model_type,
        },
    })
}

/// The result of a model call as the tool returns it: the whole result for
/// the script, usage counted by the Harness.
fn model_result<T: Serialize>(
    label: &str,
    ok: bool,
    stop_reason: &str,
    error_message: Option<&str>,
    usage: Option<&Usage>,
    value: &T,
) -> SessionResult<ToolExecutionResult> {
    let text = if ok {
        format!("{label} done")
    } else {
        format!(
            "{label} {stop_reason}: {}",
            error_message.unwrap_or_default()
        )
    };
    let structured = to_json(value)
        .map_err(|source| SessionError::other(ModelsCallError::NotStrictJson { source }))?;
    Ok(ToolExecutionResult {
        output: Some(vec![UserContentBlock::Text(TextContent::new(text))]),
        structured_output: Some(structured),
        is_error: (!ok).then_some(true),
        usage: usage.copied(),
        ..ToolExecutionResult::default()
    })
}

/// Read the checked script context into a request context.
fn read_context<T: serde::de::DeserializeOwned>(
    name: &str,
    context: Option<&PiJsonValue>,
) -> SessionResult<T> {
    serde_json::from_value(context.cloned().unwrap_or(PiJsonValue::Null)).map_err(|source| {
        SessionError::other(ModelsCallError::ReadContext {
            name: name.to_owned(),
            source,
        })
    })
}

fn wrong_type(name: &str, model: &AnyModel) -> SessionError {
    SessionError::other(ModelsCallError::ResolvedWrongType {
        name: name.to_owned(),
        resolved: model.model_type(),
    })
}

async fn classify(
    args: PiJsonValue,
    api: Arc<dyn ToolExecutionApi>,
    cx: Context,
    default: ClassifierDefault,
) -> SessionResult<ToolExecutionResult> {
    const NAME: &str = "models.classify";
    let models = api.models();
    let model = match (args.get("model"), default) {
        (None | Some(PiJsonValue::Null), ClassifierDefault::Resolver(resolve)) => {
            let agent = api.agent(&cx).await?;
            let session_model = agent
                .model
                .as_ref()
                .map(|model| format!("{}/{}", model.provider, model.model_id))
                .unwrap_or_default();
            resolve(models.clone(), session_model)
                .await
                .map_err(|error| SessionError::Other(Arc::from(error)))?
        }
        (model, ClassifierDefault::Unset | ClassifierDefault::Resolver(_)) => {
            match resolve_model(NAME, ModelType::Classifier, model, &models)
                .map_err(SessionError::other)?
            {
                AnyModel::Classifier(model) => model,
                other @ (AnyModel::Chat(_) | AnyModel::Image(_)) => {
                    return Err(wrong_type(NAME, &other));
                }
            }
        }
    };
    let context = args.get("context");
    check_classifier_context(context).map_err(SessionError::other)?;
    let context: ClassifierContext = read_context(NAME, context)?;
    let mut options = ModelsClassifierOptions::default();
    options.options.request.signal = cx.abort_signal();
    let result = models.classify(&model, &context, options).await;
    let stop_reason = result.stop_reason.as_str();
    model_result(
        &format!("classify {}/{}", model.provider, model.id),
        stop_reason == "stop",
        stop_reason,
        result.error_message.as_deref(),
        result.usage.as_ref(),
        &result,
    )
}

async fn generate_images(
    args: PiJsonValue,
    api: Arc<dyn ToolExecutionApi>,
    cx: Context,
) -> SessionResult<ToolExecutionResult> {
    const NAME: &str = "models.generateImages";
    let models = api.models();
    let resolved = resolve_model(NAME, ModelType::Image, args.get("model"), &models)
        .map_err(SessionError::other)?;
    let model = match resolved {
        AnyModel::Image(model) => model,
        other @ (AnyModel::Chat(_) | AnyModel::Classifier(_)) => {
            return Err(wrong_type(NAME, &other));
        }
    };
    let context = args.get("context");
    check_images_context(context).map_err(SessionError::other)?;
    let context: ImagesContext = read_context(NAME, context)?;
    let mut options = ModelsImagesOptions::default();
    options.options.request.signal = cx.abort_signal();
    let result = models.generate_images(&model, &context, options).await;
    let stop_reason = result.stop_reason.as_str();
    model_result(
        &format!("generateImages {}/{}", model.provider, model.id),
        stop_reason == "stop",
        stop_reason,
        result.error_message.as_deref(),
        result.usage.as_ref(),
        &result,
    )
}

fn model_tool<F, Fut>(name: &str, description: &str, execute: F) -> Arc<ToolRegistration>
where
    F: Fn(PiJsonValue, Arc<dyn ToolExecutionApi>, Context) -> Fut + Send + Sync + 'static,
    Fut: Future<Output = SessionResult<ToolExecutionResult>> + Send + 'static,
{
    let parameters = Type::object([("model", Type::unknown()), ("context", Type::unknown())]);
    let mut tool = ToolRegistration::new(name, description, parameters, execute);
    tool.structured_output_schema = Some(Type::unknown().into());
    tool.callers = Some(vec![ToolCaller::Tools]);
    define_tool(tool)
}

/// The internal tools behind `models.classify()` (its model, when the
/// script names none, from `classifier`) and `models.generateImages()`:
/// callers [`ToolCaller::Tools`] only, an unknown structured output,
/// parameters `{ model: unknown, context: unknown }`.
pub fn create_model_tools(classifier: &ClassifierDefault) -> Vec<Arc<ToolRegistration>> {
    let classifier = classifier.clone();
    vec![
        model_tool(
            CLASSIFY_TOOL,
            "models.classify() of code mode scripts.",
            move |args, api, cx| classify(args, api, cx, classifier.clone()),
        ),
        model_tool(
            GENERATE_IMAGES_TOOL,
            "models.generateImages() of code mode scripts.",
            generate_images,
        ),
    ]
}

#[cfg(test)]
mod tests {
    use eukhe_ai::providers::faux::{faux_provider, RegisterFauxProviderOptions};
    use serde_json::json;

    use super::*;
    use eukhe_ai::models::{create_models, CreateModelsOptions};
    use eukhe_chord::context::BACKGROUND_CONTEXT;

    fn context() -> &'static Context {
        &BACKGROUND_CONTEXT
    }

    fn faux_models() -> Models {
        let models = create_models(CreateModelsOptions::default());
        models.set_provider(faux_provider(RegisterFauxProviderOptions::default()).provider);
        models
    }

    fn args(value: serde_json::Value) -> JsonValue {
        JsonValue::from(value)
    }

    fn ids(value: &JsonValue) -> Vec<String> {
        let value = serde_json::Value::from(value);
        value
            .as_array()
            .expect("a model list")
            .iter()
            .map(|model| model["id"].as_str().expect("an id").to_owned())
            .collect()
    }

    #[test]
    fn maps_globals_to_tools() {
        assert_eq!(
            MODEL_CALL_GLOBALS.map(model_call_tool),
            [Some(CLASSIFY_TOOL), Some(GENERATE_IMAGES_TOOL)]
        );
        assert_eq!(model_call_tool("models.getModelOfType"), None);
    }

    #[test]
    fn describes_values() {
        let values = [
            None,
            Some(json!(null)),
            Some(json!([])),
            Some(json!([1])),
            Some(json!({})),
            Some(json!({ "prompt": "x" })),
            Some(json!({ "a": 1, "b": 2, "c": 3, "d": 4, "e": 5, "f": 6, "g": 7 })),
            Some(json!("s")),
            Some(json!(1)),
            Some(json!(true)),
        ];
        let described: Vec<String> = values
            .iter()
            .map(|value| describe_value(value.as_ref()))
            .collect();
        assert_eq!(
            described,
            [
                "undefined",
                "null",
                "an empty array",
                "an array",
                "{}",
                "{ prompt }",
                "{ a, b, c, d, e, f, ... }",
                "a string",
                "a number",
                "a boolean",
            ]
        );
    }

    /// The script's message of a failed call.
    fn rendered<T>(result: Result<T, ModelsCallError>) -> Result<T, String> {
        result.map_err(|error| error.to_string())
    }

    #[test]
    fn rejects_unknown_model_types() {
        assert_eq!(
            rendered(to_model_type(Some(&json!("image")))),
            Ok(ModelType::Image)
        );
        assert_eq!(
            rendered(to_model_type(Some(&json!("text")))),
            Err(
                "Unknown model type \"text\". Use \"chat\", \"image\", or \"classifier\"."
                    .to_owned()
            )
        );
        assert_eq!(
            rendered(to_model_type(None)),
            Err(
                "Unknown model type undefined. Use \"chat\", \"image\", or \"classifier\"."
                    .to_owned()
            )
        );
        assert_eq!(
            rendered(to_provider(Some(&json!(3)))),
            Err("provider must be a string".to_owned())
        );
    }

    #[test]
    fn checks_classifier_contexts() {
        let fail = |problem: &str| {
            Err(format!(
                "models.classify() {problem}. Expected context: {CLASSIFIER_CONTEXT_SHAPE}."
            ))
        };
        let cases = [
            (None, "expects a context object as its second argument, got undefined"),
            (Some(json!({ "questions": {} })), "context.state must be an object, got undefined"),
            (
                Some(json!({ "state": {}, "images": {} })),
                "context.images must be an array, got {}",
            ),
            (
                Some(json!({ "state": {}, "images": [{ "type": "image", "data": "x" }] })),
                "context.images[0] must be an image block, got { type, data }",
            ),
            (
                Some(json!({ "state": {}, "questions": {} })),
                "context.questions must map question IDs to questions, got {}",
            ),
            (
                Some(json!({ "state": {}, "questions": { "q": "x" } })),
                "context.questions.q must be a question object, got a string",
            ),
            (
                Some(json!({ "state": {}, "questions": { "q": { "type": "bool" } } })),
                "context.questions.q.instructions must be a string",
            ),
            (
                Some(json!({ "state": {}, "questions": { "q": { "type": "choice", "instructions": "i", "criteria": {} } } })),
                "context.questions.q is a \"choice\" question, so criteria must map each label to its meaning",
            ),
            (
                Some(json!({ "state": {}, "questions": { "q": { "type": "score", "instructions": "i", "criteria": [1] } } })),
                "context.questions.q is a \"score\" question, so criteria must list the levels as strings, lowest first",
            ),
            (
                Some(json!({ "state": {}, "questions": { "q": { "type": "bool", "instructions": "i", "criteria": { "true": "y" } } } })),
                "context.questions.q is a \"bool\" question, so criteria must be { true: string, false: string }",
            ),
            (
                Some(json!({ "state": {}, "questions": { "q": { "type": "rank", "instructions": "i" } } })),
                "context.questions.q.type must be \"choice\", \"score\", or \"bool\", got \"rank\"",
            ),
        ];
        for (value, problem) in cases {
            assert_eq!(
                rendered(check_classifier_context(value.as_ref())),
                fail(problem),
                "{problem}"
            );
        }
        let valid = json!({
            "state": { "x": 1 },
            "questions": {
                "c": { "type": "choice", "instructions": "i", "criteria": { "a": "A" } },
                "s": { "type": "score", "instructions": "i", "criteria": ["low", "high"] },
                "b": { "type": "bool", "instructions": "i", "criteria": { "true": "y", "false": "n" } }
            }
        });
        assert_eq!(rendered(check_classifier_context(Some(&valid))), Ok(()));
        let read: SessionResult<ClassifierContext> = read_context("models.classify", Some(&valid));
        assert!(read.is_ok(), "{read:?}");
    }

    #[test]
    fn checks_images_contexts() {
        let fail = |problem: &str| {
            Err(format!("models.generateImages() {problem}. Expected context: {{ input: [{{ type: \"text\", text: <prompt> }}, ...optional {{ type: \"image\", data: <base64>, mimeType }} references] }}."))
        };
        assert_eq!(
            rendered(check_images_context(Some(&json!("draw")))),
            fail("expects a context object as its second argument, got a string")
        );
        assert_eq!(
            rendered(check_images_context(Some(&json!({ "prompt": "draw" })))),
            fail("context.input must be a non-empty array of blocks, got undefined")
        );
        assert_eq!(
            rendered(check_images_context(Some(&json!({ "input": [] })))),
            fail("context.input must be a non-empty array of blocks, got an empty array")
        );
        assert_eq!(
            rendered(check_images_context(Some(
                &json!({ "input": [{ "type": "text", "text": "t" }, { "text": "t" }] })
            ))),
            fail("context.input[1] must be a text or image block, got { text }")
        );
        assert_eq!(
            rendered(check_images_context(Some(
                &json!({ "input": [{ "type": "text", "text": "t" }, { "type": "image", "data": "d", "mimeType": "image/png" }] })
            ))),
            Ok(())
        );
    }

    #[test]
    fn resolves_models_by_provider_and_id() {
        let models = faux_models();
        let hint = "List the classifier models you can use with models.getAvailableOfType(\"classifier\").";
        assert_eq!(
            rendered(
                resolve_model(
                    "models.classify",
                    ModelType::Classifier,
                    Some(&json!({ "provider": "faux", "id": "faux-1" })),
                    &models
                )
                .map(|model| model.id().to_owned())
            ),
            Err(format!(
                "\"faux/faux-1\" is a chat model, not a classifier model. {hint}"
            ))
        );
        assert_eq!(
            rendered(
                resolve_model(
                    "models.classify",
                    ModelType::Classifier,
                    Some(&json!({ "provider": "faux", "id": "nope" })),
                    &models
                )
                .map(|model| model.id().to_owned())
            ),
            Err(format!("Unknown classifier model \"faux/nope\". {hint}"))
        );
        assert_eq!(
            rendered(resolve_model("models.classify", ModelType::Classifier, None, &models).map(|model| model.id().to_owned())),
            Err(format!("models.classify() expects a classifier model as its first argument, got undefined. models.getModelOfType() returns undefined for an unknown provider or id. {hint}"))
        );
        assert_eq!(
            rendered(resolve_model("models.generateImages", ModelType::Image, Some(&json!("faux-1")), &models).map(|model| model.id().to_owned())),
            Err("models.generateImages() expects an image model as its first argument, got a string. List the image models you can use with models.getAvailableOfType(\"image\").".to_owned())
        );
    }

    #[tokio::test]
    async fn lists_models_of_a_type_by_provider() {
        let models = faux_models();
        let listed = catalog_call(
            "models.getModelsOfType",
            Some(&args(json!(["chat", "faux"]))),
            &models,
            context(),
        )
        .await
        .expect("a list")
        .expect("defined");
        assert_eq!(ids(&listed), ["faux-1"]);
        let other = catalog_call(
            "models.getModelsOfType",
            Some(&args(json!(["chat", "other"]))),
            &models,
            context(),
        )
        .await
        .expect("a list")
        .expect("defined");
        assert_eq!(ids(&other), Vec::<String>::new());
        let images = catalog_call(
            "models.getModelsOfType",
            Some(&args(json!(["image", "faux"]))),
            &models,
            context(),
        )
        .await
        .expect("a list")
        .expect("defined");
        assert_eq!(ids(&images), Vec::<String>::new());
    }

    #[tokio::test]
    async fn gets_one_model_by_three_strings() {
        let models = faux_models();
        let found = catalog_call(
            "models.getModelOfType",
            Some(&args(json!(["chat", "faux", "faux-1"]))),
            &models,
            context(),
        )
        .await
        .expect("a model")
        .expect("defined");
        let found = serde_json::Value::from(&found);
        assert_eq!(
            (found["id"].clone(), found.get("headers")),
            (json!("faux-1"), None)
        );
        assert_eq!(
            rendered(
                catalog_call(
                    "models.getModelOfType",
                    Some(&args(json!(["classifier", "faux", "faux-1"]))),
                    &models,
                    context()
                )
                .await
            ),
            Ok(None)
        );
        assert_eq!(
            rendered(catalog_call("models.getModelOfType", Some(&args(json!(["classifier", "faux/faux-1"]))), &models, context()).await),
            Err("models.getModelOfType(type, provider, id) expects three strings, got (a string, a string). The provider and the id are separate arguments, for example models.getModelOfType(\"classifier\", \"typesafe\", \"jev-latest\").".to_owned())
        );
        assert_eq!(
            rendered(catalog_call("models.getModelsOfType", None, &models, context()).await),
            Err(
                "Unknown model type undefined. Use \"chat\", \"image\", or \"classifier\"."
                    .to_owned()
            )
        );
    }
}
