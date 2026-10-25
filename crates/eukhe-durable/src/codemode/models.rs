//! Port of the `models.*` globals of code mode scripts
//! (`codemode/models.ts`): the catalog functions and the internal tools
//! behind `models.classify()` and `models.generateImages()`.
//!
//! The rules run as the compiled Bend core
//! (`eukhe_bend::rules::codemode_models`; `bend/codemode_models.bend`,
//! `laws/codemode_models/`): every check of a script's contexts and
//! arguments, which error wins and its text, which model a call uses, what
//! a catalog call does with its arguments, which global runs which model
//! call, and the texts of a call's result. This module reads what the
//! checks read of a script's JSON values (kinds, keys, the strings a check
//! compares, serde's JSON text of a value an error prints), looks models up
//! in the catalog, and runs the calls.

use std::future::Future;
use std::sync::Arc;

use eukhe_ai::auth::AuthOperationOptions;
use eukhe_ai::models::{Models, ModelsClassifierOptions, ModelsImagesOptions};
use eukhe_ai::typebox::Type;
use eukhe_bend::rules::codemode_models::{
    self, Block, CatalogArgs, CatalogCall, Desc, Lookups, ModelArg, ModelCall, Outcome, Question,
    Resolved,
};
use eukhe_bend::{expect_core, Entry, WireError};
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

/// Resolves the classifier of a `models.classify()` call whose model is
/// `null` or `undefined`, from the session's model collection and the
/// calling conversation's chat model (`provider/id`; empty: none). `Err`
/// is the message the script gets.
pub type ClassifierResolver = Arc<
    dyn Fn(Models, String) -> BoxFuture<'static, Result<ClassifierModel, String>> + Send + Sync,
>;

/// How `models.classify()` gets its model when the script names none.
#[derive(Clone)]
pub enum ClassifierDefault {
    /// No default: the script names a classifier model (the TS behavior).
    Unset,
    /// The embedding resolves one (eukhe: the `judge` role,
    /// docs/inference.md S9).
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
    expect_core(Entry::CodemodeModels, codemode_models::tool(global)).map(|call| match call {
        ModelCall::Classify => CLASSIFY_TOOL,
        ModelCall::GenerateImages => GENERATE_IMAGES_TOOL,
    })
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
/// have in flight; the rest wait. The core holds the number
/// (`Mod.max_calls`), and the code mode tool's description names it.
pub(crate) fn max_concurrent_model_calls() -> usize {
    expect_core(Entry::CodemodeModels, codemode_models::max_calls())
}

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

/// What the checks read of a script value.
fn desc(value: Option<&PiJsonValue>) -> Desc<'_> {
    match value {
        None => Desc::Undefined,
        Some(PiJsonValue::Null) => Desc::Null,
        Some(PiJsonValue::Bool(_)) => Desc::Boolean,
        Some(PiJsonValue::Number(_)) => Desc::Number,
        Some(PiJsonValue::String(_)) => Desc::String,
        Some(PiJsonValue::Array(items)) => Desc::Array {
            empty: items.is_empty(),
        },
        Some(PiJsonValue::Object(object)) => {
            Desc::Object(object.keys().map(String::as_str).collect())
        }
    }
}

/// The field `key` of a value that is an object.
fn field<'a>(value: Option<&'a PiJsonValue>, key: &str) -> Option<&'a PiJsonValue> {
    record(value).and_then(|object| object.get(key))
}

fn text(value: Option<&PiJsonValue>) -> Option<&str> {
    value.and_then(PiJsonValue::as_str)
}

fn block(item: &PiJsonValue) -> Block<'_> {
    let at = |key| field(Some(item), key);
    Block {
        block: desc(Some(item)),
        kind: text(at("type")),
        text: desc(at("text")),
        data: desc(at("data")),
        mime_type: desc(at("mimeType")),
    }
}

fn blocks(value: Option<&PiJsonValue>) -> Vec<Block<'_>> {
    value
        .and_then(PiJsonValue::as_array)
        .map_or_else(Vec::new, |items| items.iter().map(block).collect())
}

fn question<'a>(id: &'a str, value: &'a PiJsonValue) -> Question<'a> {
    let at = |key| field(Some(value), key);
    let criteria = at("criteria");
    let values = match criteria {
        Some(PiJsonValue::Object(map)) => map.values().map(|item| desc(Some(item))).collect(),
        Some(PiJsonValue::Array(items)) => items.iter().map(|item| desc(Some(item))).collect(),
        Some(
            PiJsonValue::Null
            | PiJsonValue::Bool(_)
            | PiJsonValue::Number(_)
            | PiJsonValue::String(_),
        )
        | None => Vec::new(),
    };
    Question {
        id,
        question: desc(Some(value)),
        instructions: desc(at("instructions")),
        kind: text(at("type")),
        kind_json: stringify(at("type")),
        criteria: desc(criteria),
        values,
        yes: desc(field(criteria, "true")),
        no: desc(field(criteria, "false")),
    }
}

/// A core answer the caller's own facts contradict, or a request past the
/// wire's bounds (a script value too long), as the script's error.
fn core_error(error: &eukhe_bend::Error) -> SessionError {
    SessionError::error(format!("code mode models: {error}"))
}

/// Check a script's classifier context, so mistakes fail with the expected
/// shape instead of a provider error.
fn check_classifier_context(context: Option<&PiJsonValue>) -> SessionResult<()> {
    let questions = field(context, "questions");
    let facts = codemode_models::ClassifierContext {
        context: desc(context),
        state: desc(field(context, "state")),
        images: desc(field(context, "images")),
        image_items: blocks(field(context, "images")),
        questions: desc(questions),
        question_items: record(questions).map_or_else(Vec::new, |map| {
            map.iter().map(|(id, value)| question(id, value)).collect()
        }),
    };
    match codemode_models::classifier_problem(&facts).map_err(|error| core_error(&error))? {
        None => Ok(()),
        Some(problem) => Err(SessionError::error(problem)),
    }
}

/// Check a script's image context, so mistakes such as `{ prompt }` fail
/// with the expected shape.
fn check_images_context(context: Option<&PiJsonValue>) -> SessionResult<()> {
    let facts = codemode_models::ImagesContext {
        context: desc(context),
        input: desc(field(context, "input")),
        blocks: blocks(field(context, "input")),
    };
    match codemode_models::images_problem(&facts).map_err(|error| core_error(&error))? {
        None => Ok(()),
        Some(problem) => Err(SessionError::error(problem)),
    }
}

/// Catalog entry for scripts. `headers` is dropped because configured
/// headers can carry credentials.
fn to_model_info(model: &AnyModel) -> Result<JsonValue, String> {
    let mut info = serde_json::to_value(model).map_err(|error| error.to_string())?;
    if let Some(object) = info.as_object_mut() {
        object.remove("headers");
    }
    to_json(&info).map_err(|error| error.to_string())
}

fn model_infos(models: &[AnyModel]) -> Result<JsonValue, String> {
    let infos = models
        .iter()
        .map(to_model_info)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(JsonValue::from(infos))
}

/// `catalogCall`: what a script's call of catalog global `name` with its
/// spread argument list `args` (a JSON array after the JS round trip;
/// `None` = undefined) resolves to. `Ok(None)` = undefined. `Err(message)` =
/// the thrown Error's message.
pub(crate) async fn catalog_call(
    name: &str,
    args: Option<&JsonValue>,
    models: &Models,
    cx: &Context,
) -> Result<Option<JsonValue>, String> {
    let list = match args.map(serde_json::Value::from) {
        Some(PiJsonValue::Array(items)) => items,
        Some(_) | None => Vec::new(),
    };
    let facts = CatalogArgs {
        global: name,
        args: list.iter().map(|value| desc(Some(value))).collect(),
        kind: text(list.first()),
        kind_json: stringify(list.first()),
        provider: text(list.get(1)),
        id: text(list.get(2)),
    };
    match codemode_models::catalog(&facts).map_err(|error| error.to_string())? {
        CatalogCall::Failed(problem) => Err(problem),
        CatalogCall::Models {
            model_type,
            provider,
        } => model_infos(&models.get_models_of_type(model_type, provider)).map(Some),
        CatalogCall::Available {
            model_type,
            provider,
        } => {
            let available = models
                .get_available_of_type(
                    model_type,
                    provider,
                    AuthOperationOptions {
                        signal: cx.abort_signal(),
                    },
                )
                .await
                .map_err(|error| error.to_string())?;
            model_infos(&available).map(Some)
        }
        CatalogCall::One {
            model_type,
            provider,
            id,
        } => models
            .get_model_of_type(model_type, provider, id)
            .as_ref()
            .map(to_model_info)
            .transpose(),
    }
}

/// Resolve the script's model by provider and id only, so a script-supplied
/// baseUrl or headers never receive the credentials, with errors that say
/// what to do: the catalog's models of each type under the model's
/// provider and id, and the core's choice.
fn resolve_model(
    call: ModelCall,
    default_classifier: bool,
    model: Option<&PiJsonValue>,
    models: &Models,
) -> SessionResult<Resolved<AnyModel>> {
    let (provider, id) = (text(field(model, "provider")), text(field(model, "id")));
    let lookups = match (provider, id) {
        (Some(provider), Some(id)) => {
            let look = |model_type| {
                models
                    .get_model_of_type(model_type, provider, id)
                    .map(|found| (found.model_type(), found))
            };
            Lookups {
                chat: look(ModelType::Chat),
                image: look(ModelType::Image),
                classifier: look(ModelType::Classifier),
            }
        }
        (None, _) | (_, None) => Lookups {
            chat: None,
            image: None,
            classifier: None,
        },
    };
    let arg = ModelArg {
        call,
        default_classifier,
        model: desc(model),
        provider,
        id,
    };
    match codemode_models::resolve(&arg, lookups).map_err(|error| core_error(&error))? {
        Resolved::Failed(problem) => Err(SessionError::error(problem)),
        resolved @ (Resolved::Default | Resolved::Found(_)) => Ok(resolved),
    }
}

/// A model the core chose for a call, but of another kind than its lookup
/// said: an inconsistent build.
fn wrong_kind() -> SessionError {
    core_error(
        &WireError::Malformed {
            at: 0,
            expected: "a model of the call's type",
        }
        .into(),
    )
}

/// The result of a model call as the tool returns it: the whole result for
/// the script, usage counted by the Harness.
fn model_result<T: Serialize>(
    outcome: &Outcome<'_>,
    usage: Option<&Usage>,
    value: &T,
) -> SessionResult<ToolExecutionResult> {
    let report = codemode_models::report(outcome).map_err(|error| core_error(&error))?;
    let structured = to_json(value).map_err(|error| SessionError::error(error.to_string()))?;
    Ok(ToolExecutionResult {
        output: Some(vec![UserContentBlock::Text(TextContent::new(report.text))]),
        structured_output: Some(structured),
        is_error: (!report.ok).then_some(true),
        usage: usage.copied(),
        ..ToolExecutionResult::default()
    })
}

/// Read the checked script context into a request context.
fn read_context<T: serde::de::DeserializeOwned>(
    call: ModelCall,
    context: Option<&PiJsonValue>,
) -> SessionResult<T> {
    serde_json::from_value(context.cloned().unwrap_or(PiJsonValue::Null)).map_err(|error| {
        match codemode_models::unread(call, &error.to_string()) {
            Ok(text) => SessionError::error(text),
            Err(core) => core_error(&core),
        }
    })
}

async fn classify(
    args: PiJsonValue,
    api: Arc<dyn ToolExecutionApi>,
    cx: Context,
    default: ClassifierDefault,
) -> SessionResult<ToolExecutionResult> {
    let models = api.models();
    let default_classifier = match &default {
        ClassifierDefault::Unset => false,
        ClassifierDefault::Resolver(_) => true,
    };
    let resolved = resolve_model(
        ModelCall::Classify,
        default_classifier,
        args.get("model"),
        &models,
    )?;
    let model = match (resolved, default) {
        (Resolved::Default, ClassifierDefault::Resolver(resolve)) => {
            let agent = api.agent(&cx).await?;
            let session_model = agent
                .model
                .as_ref()
                .map(|model| format!("{}/{}", model.provider, model.model_id))
                .unwrap_or_default();
            resolve(models.clone(), session_model)
                .await
                .map_err(SessionError::error)?
        }
        (Resolved::Found(AnyModel::Classifier(model)), _) => model,
        (
            Resolved::Default | Resolved::Failed(_),
            ClassifierDefault::Unset | ClassifierDefault::Resolver(_),
        )
        | (Resolved::Found(AnyModel::Chat(_) | AnyModel::Image(_)), _) => {
            return Err(wrong_kind());
        }
    };
    let context = args.get("context");
    check_classifier_context(context)?;
    let context: ClassifierContext = read_context(ModelCall::Classify, context)?;
    let mut options = ModelsClassifierOptions::default();
    options.options.request.signal = cx.abort_signal();
    let result = models.classify(&model, &context, options).await;
    model_result(
        &Outcome {
            call: ModelCall::Classify,
            provider: &model.provider,
            id: &model.id,
            stop_reason: result.stop_reason.as_str(),
            error_message: result.error_message.as_deref(),
        },
        result.usage.as_ref(),
        &result,
    )
}

async fn generate_images(
    args: PiJsonValue,
    api: Arc<dyn ToolExecutionApi>,
    cx: Context,
) -> SessionResult<ToolExecutionResult> {
    let models = api.models();
    let model = match resolve_model(ModelCall::GenerateImages, false, args.get("model"), &models)? {
        Resolved::Found(AnyModel::Image(model)) => model,
        Resolved::Found(AnyModel::Chat(_) | AnyModel::Classifier(_))
        | Resolved::Default
        | Resolved::Failed(_) => return Err(wrong_kind()),
    };
    let context = args.get("context");
    check_images_context(context)?;
    let context: ImagesContext = read_context(ModelCall::GenerateImages, context)?;
    let mut options = ModelsImagesOptions::default();
    options.options.request.signal = cx.abort_signal();
    let result = models.generate_images(&model, &context, options).await;
    model_result(
        &Outcome {
            call: ModelCall::GenerateImages,
            provider: &model.provider,
            id: &model.id,
            stop_reason: result.stop_reason.as_str(),
            error_message: result.error_message.as_deref(),
        },
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

    const CLASSIFIER_CONTEXT_SHAPE: &str = "{ state: { ... }, images?: [{ type: \"image\", data: <base64>, mimeType }], questions: { <id>: { type: \"choice\", instructions, criteria: { <label>: <meaning> } } | { type: \"score\", instructions, criteria: [<lowest level>, ..., <highest level>] } | { type: \"bool\", instructions, criteria: { true: <meaning>, false: <meaning> } } } }";

    /// The facts each check reads of a script's JSON (`laws/codemode_models`
    /// pins the texts for given facts).
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
                check_classifier_context(value.as_ref()).map_err(|error| error.to_string()),
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
        assert!(check_classifier_context(Some(&valid)).is_ok());
        let read: SessionResult<ClassifierContext> =
            read_context(ModelCall::Classify, Some(&valid));
        assert!(read.is_ok(), "{read:?}");
        let unread: SessionResult<ClassifierContext> =
            read_context(ModelCall::Classify, Some(&json!({ "state": 1 })));
        assert!(unread.is_err_and(|error| error
            .to_string()
            .starts_with("models.classify() could not read its context: ")),);
    }

    #[test]
    fn checks_images_contexts() {
        let fail = |problem: &str| {
            Err(format!("models.generateImages() {problem}. Expected context: {{ input: [{{ type: \"text\", text: <prompt> }}, ...optional {{ type: \"image\", data: <base64>, mimeType }} references] }}."))
        };
        let check = |value: serde_json::Value| {
            check_images_context(Some(&value)).map_err(|error| error.to_string())
        };
        assert_eq!(
            check(json!("draw")),
            fail("expects a context object as its second argument, got a string")
        );
        assert_eq!(
            check(json!({ "prompt": "draw" })),
            fail("context.input must be a non-empty array of blocks, got undefined")
        );
        assert_eq!(
            check(json!({ "input": [] })),
            fail("context.input must be a non-empty array of blocks, got an empty array")
        );
        assert_eq!(
            check(json!({ "input": [{ "type": "text", "text": "t" }, { "text": "t" }] })),
            fail("context.input[1] must be a text or image block, got { text }")
        );
        assert_eq!(
            check(
                json!({ "input": [{ "type": "text", "text": "t" }, { "type": "image", "data": "d", "mimeType": "image/png" }] })
            ),
            Ok(())
        );
    }

    /// The catalog's lookups under each type and the core's choice.
    #[test]
    fn resolves_models_by_provider_and_id() {
        let models = faux_models();
        let resolve = |call, default, model: Option<serde_json::Value>| match resolve_model(
            call,
            default,
            model.as_ref(),
            &models,
        ) {
            Ok(Resolved::Found(model)) => Ok(Some(model.id().to_owned())),
            Ok(Resolved::Default) => Ok(None),
            Ok(Resolved::Failed(problem)) => Err(problem),
            Err(error) => Err(error.to_string()),
        };
        let hint = "List the classifier models you can use with models.getAvailableOfType(\"classifier\").";
        assert_eq!(
            resolve(
                ModelCall::Classify,
                false,
                Some(json!({ "provider": "faux", "id": "faux-1" }))
            ),
            Err(format!(
                "\"faux/faux-1\" is a chat model, not a classifier model. {hint}"
            ))
        );
        assert_eq!(
            resolve(
                ModelCall::Classify,
                false,
                Some(json!({ "provider": "faux", "id": "nope" }))
            ),
            Err(format!("Unknown classifier model \"faux/nope\". {hint}"))
        );
        assert_eq!(
            resolve(ModelCall::Classify, false, None),
            Err(format!("models.classify() expects a classifier model as its first argument, got undefined. models.getModelOfType() returns undefined for an unknown provider or id. {hint}"))
        );
        assert_eq!(resolve(ModelCall::Classify, true, None), Ok(None));
        assert_eq!(
            resolve(ModelCall::GenerateImages, false, Some(json!("faux-1"))),
            Err("models.generateImages() expects an image model as its first argument, got a string. List the image models you can use with models.getAvailableOfType(\"image\").".to_owned())
        );
    }

    #[test]
    fn caps_model_calls_as_the_description_says() {
        let description = crate::codemode::codemode_description(
            crate::codemode::CodemodeModels::Included,
            &ClassifierDefault::Unset,
        );
        assert!(description.contains(&format!(
            "At most {} classify/generateImages calls run at once",
            max_concurrent_model_calls()
        )));
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
            catalog_call(
                "models.getModelOfType",
                Some(&args(json!(["classifier", "faux", "faux-1"]))),
                &models,
                context()
            )
            .await,
            Ok(None)
        );
        assert_eq!(
            catalog_call("models.getModelOfType", Some(&args(json!(["classifier", "faux/faux-1"]))), &models, context()).await,
            Err("models.getModelOfType(type, provider, id) expects three strings, got (a string, a string). The provider and the id are separate arguments, for example models.getModelOfType(\"classifier\", \"typesafe\", \"jev-latest\").".to_owned())
        );
        assert_eq!(
            catalog_call("models.getModelsOfType", None, &models, context()).await,
            Err(
                "Unknown model type undefined. Use \"chat\", \"image\", or \"classifier\"."
                    .to_owned()
            )
        );
    }
}
