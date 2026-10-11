//! Shared utilities for Google Generative AI and Google Vertex providers.
//! Port of `api/google-shared.ts`.
//!
//! Gemini wire objects (`Content`, `Part`, `ThinkingConfig`, tool
//! declarations) are built as JSON values in the key order the TS object
//! literals produce; [`genai`] then sends them the way the `@google/genai`
//! SDK does.

pub(crate) mod genai;
mod messages;
mod options;
mod stream;
#[cfg(test)]
pub(crate) mod test_support;
#[cfg(test)]
mod tests;

use std::future::Future;
use std::sync::{Arc, LazyLock};

use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::{
    JsonObject, JsonValue, Model, ModelThinkingLevel, StopReason, ThinkingLevel, Tool,
};
use regex::Regex;
use serde_json::json;

use super::constrained_sampling::{
    get_json_schema_tool_parameters, resolve_json_schema_strict_sampling, StrictToolParameters,
};
use crate::models::clamp_thinking_level;
use crate::utils::diagnostics::{thrown, ErrorObject, Thrown};
use crate::utils::provider_retry::{retry_provider_request, ProviderRetryOptions};

pub use messages::convert_messages;
pub(crate) use options::{
    budget_for, custom_budget, pi_headers, simple_request_options, GoogleRequestOptions,
};
pub(crate) use stream::{run_google_stream, GoogleApiKind};

/// Thinking level for Gemini 3 models: mirrors Google's `ThinkingLevel`
/// enum values (TS `GoogleApiThinkingLevel`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum GoogleApiThinkingLevel {
    #[serde(rename = "THINKING_LEVEL_UNSPECIFIED")]
    ThinkingLevelUnspecified,
    #[serde(rename = "MINIMAL")]
    Minimal,
    #[serde(rename = "LOW")]
    Low,
    #[serde(rename = "MEDIUM")]
    Medium,
    #[serde(rename = "HIGH")]
    High,
}

impl GoogleApiThinkingLevel {
    /// The wire value.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ThinkingLevelUnspecified => "THINKING_LEVEL_UNSPECIFIED",
            Self::Minimal => "MINIMAL",
            Self::Low => "LOW",
            Self::Medium => "MEDIUM",
            Self::High => "HIGH",
        }
    }
}

/// TS `ResolvedGoogleThinkingLevel = Exclude<ThinkingLevel, "xhigh" | "max">`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResolvedGoogleThinkingLevel {
    Minimal,
    Low,
    Medium,
    High,
}

impl ResolvedGoogleThinkingLevel {
    /// The pi level name.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Minimal => "minimal",
            Self::Low => "low",
            Self::Medium => "medium",
            Self::High => "high",
        }
    }
}

/// A non-`off` model thinking level as a pi [`ThinkingLevel`].
pub(crate) fn as_thinking_level(level: ModelThinkingLevel) -> Option<ThinkingLevel> {
    match level {
        ModelThinkingLevel::Off => None,
        ModelThinkingLevel::Minimal => Some(ThinkingLevel::Minimal),
        ModelThinkingLevel::Low => Some(ThinkingLevel::Low),
        ModelThinkingLevel::Medium => Some(ThinkingLevel::Medium),
        ModelThinkingLevel::High => Some(ThinkingLevel::High),
        ModelThinkingLevel::Xhigh => Some(ThinkingLevel::Xhigh),
        ModelThinkingLevel::Max => Some(ThinkingLevel::Max),
    }
}

/// Resolve a supported pi level or model-specific Google mapping to a
/// standard Google level.
///
/// # Errors
///
/// When the model maps `level` to a value that is not a standard Google level.
pub fn resolve_google_thinking_level(
    model: &Model,
    level: ThinkingLevel,
) -> Result<ResolvedGoogleThinkingLevel, Thrown> {
    // `undefined` when the key is absent, `null` when mapped to null.
    let mapped: Option<Option<&str>> = model
        .thinking_level_map
        .as_ref()
        .and_then(|map| map.get(&ModelThinkingLevel::from(level)))
        .map(Option::as_deref);
    let resolved = match mapped {
        Some(Some(value)) => value.to_lowercase(),
        Some(None) | None => level.as_str().to_owned(),
    };
    match resolved.as_str() {
        "minimal" => Ok(ResolvedGoogleThinkingLevel::Minimal),
        "low" => Ok(ResolvedGoogleThinkingLevel::Low),
        "medium" => Ok(ResolvedGoogleThinkingLevel::Medium),
        "high" => Ok(ResolvedGoogleThinkingLevel::High),
        _ => {
            let mapped = match mapped {
                Some(Some(value)) => value.to_owned(),
                Some(None) => "null".to_owned(),
                None => "undefined".to_owned(),
            };
            Err(ErrorObject::new(format!(
                "Unsupported Google thinking level mapping for {}/{}: {} -> {mapped}",
                model.provider,
                model.id,
                level.as_str()
            ))
            .thrown())
        }
    }
}

/// Matches Gemini 3 Pro/Flash IDs with or without a minor version, such as
/// gemini-3-flash-preview, gemini-3.1-pro-preview, and gemini-3.8-flash.
static GEMINI_3_LEVEL_MODEL: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"gemini-3(?:\.\d+)?-(?:pro|flash)").unwrap_or_else(|error| panic!("{error}"))
});
/// Matches both hosted Gemma 4 naming forms: gemma-4-* and gemma4-*.
static GEMMA_4_MODEL: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"gemma-?4").unwrap_or_else(|error| panic!("{error}")));
static GEMINI_MAJOR_VERSION: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"^gemini(?:-live)?-(\d+)").unwrap_or_else(|error| panic!("{error}"))
});

/// Whether this model uses Gemini's discrete `thinkingLevel` control instead
/// of the token-based `thinkingBudget` control. Supported levels come from
/// the model's `thinkingLevelMap`; this only selects the Google wire format.
#[must_use]
pub fn uses_google_thinking_level(model: &Model) -> bool {
    let id = model.id.to_lowercase();
    GEMINI_3_LEVEL_MODEL.is_match(&id)
        || id == "gemini-flash-latest"
        || id == "gemini-flash-lite-latest"
        || GEMMA_4_MODEL.is_match(&id)
}

/// TS `toGoogleThinkingLevel`.
#[must_use]
pub const fn to_google_thinking_level(
    level: ResolvedGoogleThinkingLevel,
) -> GoogleApiThinkingLevel {
    match level {
        ResolvedGoogleThinkingLevel::Minimal => GoogleApiThinkingLevel::Minimal,
        ResolvedGoogleThinkingLevel::Low => GoogleApiThinkingLevel::Low,
        ResolvedGoogleThinkingLevel::Medium => GoogleApiThinkingLevel::Medium,
        ResolvedGoogleThinkingLevel::High => GoogleApiThinkingLevel::High,
    }
}

/// TS `toGoogleSdkThinkingLevel`: the SDK enum shares the wire values.
#[must_use]
pub const fn to_google_sdk_thinking_level(level: GoogleApiThinkingLevel) -> &'static str {
    level.as_str()
}

/// TS `getDisabledGoogleThinkingConfig`: the `ThinkingConfig` that turns
/// thinking off (or as low as the model allows).
///
/// # Errors
///
/// When the fallback level has an unsupported mapping.
pub fn get_disabled_google_thinking_config(model: &Model) -> Result<JsonValue, Thrown> {
    if !uses_google_thinking_level(model) {
        return Ok(json!({ "thinkingBudget": 0 }));
    }
    let Some(fallback) = as_thinking_level(clamp_thinking_level(model, ModelThinkingLevel::Off))
    else {
        return Ok(json!({ "thinkingBudget": 0 }));
    };
    let resolved = resolve_google_thinking_level(model, fallback)?;
    let api_level = to_google_thinking_level(resolved);
    Ok(json!({ "thinkingLevel": to_google_sdk_thinking_level(api_level) }))
}

/// Determines whether a streamed Gemini `Part` should be treated as
/// "thinking".
///
/// Protocol note (Gemini / Vertex AI thought signatures):
/// - `thought: true` is the definitive marker for thinking content (thought
///   summaries).
/// - `thoughtSignature` is an encrypted representation of the model's
///   internal thought process used to preserve reasoning context across
///   multi-turn interactions. It can appear on ANY part type (text,
///   functionCall, etc.); it does NOT indicate the part itself is thinking.
/// - For non-functionCall responses, the signature appears on the last part
///   for context replay.
/// - When persisting/replaying model outputs, signature-bearing parts must be
///   preserved as-is; do not merge/move signatures across parts.
///
/// See: <https://ai.google.dev/gemini-api/docs/thought-signatures>
#[must_use]
pub fn is_thinking_part(thought: Option<&JsonValue>, _thought_signature: Option<&str>) -> bool {
    thought == Some(&JsonValue::Bool(true))
}

/// Retain thought signatures during streaming.
///
/// Some backends only send `thoughtSignature` on the first delta for a given
/// part/block; later deltas may omit it. This keeps the last non-empty
/// signature for the current block. It does NOT merge or move signatures
/// across distinct response parts.
#[must_use]
pub fn retain_thought_signature(
    existing: Option<String>,
    incoming: Option<&str>,
) -> Option<String> {
    match incoming {
        Some(incoming) if !incoming.is_empty() => Some(incoming.to_owned()),
        _ => existing,
    }
}

/// Thought signatures must be base64 for Google APIs (`TYPE_BYTES`).
fn is_valid_thought_signature(signature: Option<&str>) -> bool {
    let Some(signature) = signature.filter(|signature| !signature.is_empty()) else {
        return false;
    };
    if signature.len() % 4 != 0 {
        return false;
    }
    // /^[A-Za-z0-9+/]+={0,2}$/
    let body = signature.trim_end_matches('=');
    let padding = signature.len() - body.len();
    !body.is_empty()
        && padding <= 2
        && body
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'+' || byte == b'/')
}

/// Only keep signatures from the same provider/model and with valid base64.
fn resolve_thought_signature(
    same_provider_and_model: bool,
    signature: Option<&str>,
) -> Option<String> {
    (same_provider_and_model && is_valid_thought_signature(signature))
        .then(|| signature.map(str::to_owned))
        .flatten()
}

/// Models via Google APIs that require explicit tool call IDs in function
/// calls/responses.
#[must_use]
pub fn requires_tool_call_id(model_id: &str) -> bool {
    model_id.starts_with("claude-")
        || model_id.starts_with("gpt-oss-")
        || get_gemini_major_version(model_id).is_some_and(|major| major >= 3)
}

/// `Number.parseInt` of the leading `gemini[-live]-<digits>` version; digit
/// runs beyond `u64` saturate (they compare as large numbers in JS too).
fn get_gemini_major_version(model_id: &str) -> Option<u64> {
    let lowered = model_id.to_lowercase();
    let digits = GEMINI_MAJOR_VERSION
        .captures(&lowered)?
        .get(1)?
        .as_str()
        .to_owned();
    Some(digits.parse::<u64>().unwrap_or(u64::MAX))
}

fn supports_multimodal_function_response(model_id: &str) -> bool {
    get_gemini_major_version(model_id).is_none_or(|major| major >= 3)
}

const JSON_SCHEMA_META_DECLARATIONS: [&str; 8] = [
    "$schema",
    "$id",
    "$anchor",
    "$dynamicAnchor",
    "$vocabulary",
    "$comment",
    "$defs",
    // pre-draft-2019-09 equivalent of $defs
    "definitions",
];

/// Strip meta-declarations from a schema object. Arrays and primitives are
/// returned unchanged (objects nested inside arrays are not visited).
fn sanitize_for_open_api(schema: &JsonValue) -> JsonValue {
    let JsonValue::Object(object) = schema else {
        return schema.clone();
    };
    JsonValue::Object(
        object
            .iter()
            .filter(|(key, _)| !JSON_SCHEMA_META_DECLARATIONS.contains(&key.as_str()))
            .map(|(key, value)| (key.clone(), sanitize_for_open_api(value)))
            .collect(),
    )
}

/// Which schema field `convert_tools` fills (TS `useParameters`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ToolSchemaField {
    /// `parametersJsonSchema`: full JSON Schema (anyOf, oneOf, const, ...).
    ParametersJsonSchema,
    /// Legacy `parameters` (`OpenAPI` 3.03 Schema), meta keys stripped. Needed
    /// for Cloud Code Assist with Claude models, where the API translates
    /// `parameters` into Anthropic's `input_schema`.
    Parameters,
}

/// Convert tools to Gemini function declarations format. `None` for an
/// empty tool list.
///
/// # Errors
///
/// When a tool requires strict sampling that cannot be provided.
pub fn convert_tools(
    tools: &[Tool],
    field: ToolSchemaField,
    supports_strict_mode: bool,
) -> Result<Option<Vec<JsonValue>>, Thrown> {
    if tools.is_empty() {
        return Ok(None);
    }
    let mut declarations = Vec::with_capacity(tools.len());
    for tool in tools {
        let strict = resolve_json_schema_strict_sampling(tool, supports_strict_mode, None)
            .map_err(thrown)?;
        let parameters = get_json_schema_tool_parameters(
            tool,
            if strict == Some(true) {
                StrictToolParameters::Strict
            } else {
                StrictToolParameters::AsDeclared
            },
        )
        .map_err(thrown)?;
        let mut declaration = JsonObject::new();
        declaration.insert("name".into(), tool.name.clone().into());
        declaration.insert("description".into(), tool.description.clone().into());
        match field {
            ToolSchemaField::Parameters => {
                declaration.insert("parameters".into(), sanitize_for_open_api(&parameters));
            }
            ToolSchemaField::ParametersJsonSchema => {
                declaration.insert("parametersJsonSchema".into(), parameters);
            }
        }
        declarations.push(JsonValue::Object(declaration));
    }
    Ok(Some(vec![json!({ "functionDeclarations": declarations })]))
}

/// Gemini 3+ enforces required function parameters in validated
/// tool-calling modes.
#[must_use]
pub fn supports_google_strict_tool_sampling(model_id: &str) -> bool {
    get_gemini_major_version(model_id).is_some_and(|major| major >= 3)
}

/// The SDK `FunctionCallingConfigMode` values pi-ai sends.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FunctionCallingConfigMode {
    Auto,
    None,
    Any,
    Validated,
}

impl FunctionCallingConfigMode {
    /// The wire value.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Auto => "AUTO",
            Self::None => "NONE",
            Self::Any => "ANY",
            Self::Validated => "VALIDATED",
        }
    }
}

/// Map a tool choice string to Gemini `FunctionCallingConfigMode`.
#[must_use]
pub fn map_tool_choice(choice: &str) -> FunctionCallingConfigMode {
    match choice {
        "none" => FunctionCallingConfigMode::None,
        "any" => FunctionCallingConfigMode::Any,
        _ => FunctionCallingConfigMode::Auto,
    }
}

/// TS `resolveGoogleFunctionCallingMode`.
///
/// # Errors
///
/// When a tool requires strict sampling that cannot be provided.
pub fn resolve_google_function_calling_mode(
    tools: &[Tool],
    tool_choice: Option<&str>,
    supports_strict_mode: bool,
) -> Result<Option<FunctionCallingConfigMode>, Thrown> {
    let mut use_strict_mode = false;
    for tool in tools {
        if resolve_json_schema_strict_sampling(tool, supports_strict_mode, None).map_err(thrown)?
            == Some(true)
        {
            use_strict_mode = true;
            break;
        }
    }
    if let Some(choice @ ("none" | "any")) = tool_choice {
        return Ok(Some(map_tool_choice(choice)));
    }
    if use_strict_mode {
        return Ok(Some(FunctionCallingConfigMode::Validated));
    }
    // JS truthiness: an empty string means no choice.
    Ok(tool_choice
        .filter(|choice| !choice.is_empty())
        .map(map_tool_choice))
}

/// Map a Gemini `FinishReason` to a stop reason.
///
/// # Errors
///
/// `Unhandled stop reason: <reason>` for a value outside the SDK enum.
pub fn map_stop_reason(reason: &str) -> Result<StopReason, Thrown> {
    match reason {
        "STOP" => Ok(StopReason::Stop),
        "MAX_TOKENS" => Ok(StopReason::Length),
        "BLOCKLIST"
        | "PROHIBITED_CONTENT"
        | "SPII"
        | "SAFETY"
        | "IMAGE_SAFETY"
        | "IMAGE_PROHIBITED_CONTENT"
        | "IMAGE_RECITATION"
        | "IMAGE_OTHER"
        | "RECITATION"
        | "FINISH_REASON_UNSPECIFIED"
        | "OTHER"
        | "LANGUAGE"
        | "MALFORMED_FUNCTION_CALL"
        | "UNEXPECTED_TOOL_CALL"
        | "TOO_MANY_TOOL_CALLS"
        | "NO_IMAGE" => Ok(StopReason::Error),
        other => Err(ErrorObject::new(format!("Unhandled stop reason: {other}")).thrown()),
    }
}

/// Map a string finish reason to a stop reason (for raw API responses).
#[must_use]
pub fn map_stop_reason_string(reason: &str) -> StopReason {
    match reason {
        "STOP" => StopReason::Stop,
        "MAX_TOKENS" => StopReason::Length,
        _ => StopReason::Error,
    }
}

/// TS `Pick<StreamOptions, "maxRetries" | "maxRetryDelayMs" | "signal">`.
#[derive(Debug, Clone, Default)]
pub struct GoogleRetryOptions {
    pub max_retries: Option<u32>,
    pub max_retry_delay_ms: Option<f64>,
    pub signal: Option<AbortSignal>,
}

/// Run a Google request with the shared provider retry policy
/// (408/409/429/5xx with backoff, honoring retry-after). The SDK's
/// `ApiError` has a `status` property but no `headers` property, and the
/// retry policy only retries errors that carry both, so the error gains an
/// undefined `headers` before it is rethrown.
///
/// # Errors
///
/// The last request error, or the retry policy's abort/cap errors.
pub async fn retry_google_request<T, F, Fut>(
    mut request: F,
    options: Option<&GoogleRetryOptions>,
) -> Result<T, Thrown>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<T, Thrown>>,
{
    let retry_options = ProviderRetryOptions {
        max_retries: options.and_then(|options| options.max_retries),
        max_retry_delay_ms: options.and_then(|options| options.max_retry_delay_ms),
        signal: options.and_then(|options| options.signal.clone()),
        no_retry_statuses: Vec::new(),
    };
    retry_provider_request(
        || {
            let attempt = request();
            async move { attempt.await.map_err(add_missing_headers) }
        },
        &retry_options,
    )
    .await
}

/// `if (error instanceof Error && "status" in error && !("headers" in error))
/// error.headers = undefined`.
fn add_missing_headers(error: Thrown) -> Thrown {
    match error.downcast_ref::<ErrorObject>() {
        Some(object) if object.status.is_some() && object.headers.is_none() => {
            let mut object = object.clone();
            object.headers = Some(None);
            Arc::new(object)
        }
        Some(_) | None => error,
    }
}
