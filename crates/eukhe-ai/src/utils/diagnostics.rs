//! Thrown values and assistant-message diagnostics.
//!
//! TS throws `unknown`; Rust carries a thrown value as [`Thrown`], the same
//! shared error type as an abort reason, so abort reasons flow through
//! unchanged. A JS `Error` with a `name`/`code` is an [`ErrorObject`]; a
//! thrown non-`Error` value (a string, a number, ...) is a [`ThrownValue`].

use std::error::Error;
use std::sync::Arc;

use eukhe_chord::context::{AbortError, AbortReason};

use eukhe_types::pi_ai::{AssistantMessage, JsonObject, JsonValue};
pub use eukhe_types::pi_ai::{AssistantMessageDiagnostic, DiagnosticCode, DiagnosticErrorInfo};

use super::js::js_to_string;
use super::models_error::ModelsError;
use super::now_ms;

/// A thrown value (TS `unknown` in `catch`).
pub type Thrown = AbortReason;

/// A non-`Error` value stored on an SDK error property: plain parsed data, a
/// readable stream (an object with a `pipe()` method), or another class
/// instance (anything whose prototype is not `Object.prototype`/`null`).
#[derive(Debug, Clone, PartialEq)]
pub enum SdkValue {
    Json(JsonValue),
    Stream,
    Instance,
}

/// The `$response` property of an AWS SDK (Bedrock) service exception.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct SdkResponse {
    /// `$response.statusCode`.
    pub status_code: Option<JsonValue>,
    /// `$response.body`.
    pub body: Option<SdkValue>,
}

/// A JS `Error` object: `name`, `message`, an optional `code`, and the
/// optional properties provider SDK errors carry, which
/// `normalizeProviderError` and `retryProviderRequest` probe.
#[derive(Debug, Clone, PartialEq, Default, thiserror::Error)]
#[error("{message}")]
pub struct ErrorObject {
    pub name: String,
    pub message: String,
    pub code: Option<DiagnosticCode>,
    /// `statusCode` (Mistral SDK).
    pub status_code: Option<JsonValue>,
    /// `status` (`openai`, `@google/genai`, Anthropic SDKs). The outer
    /// `Option` is the property's presence, `Some(None)` an `undefined` value.
    pub status: Option<Option<JsonValue>>,
    /// `headers` (`openai`/Anthropic `APIError`). The outer `Option` is the
    /// property's presence, `Some(None)` an `undefined` value.
    pub headers: Option<Option<reqwest::header::HeaderMap>>,
    /// `body` (Mistral SDK).
    pub body: Option<SdkValue>,
    /// `error`: the parsed JSON body (`openai` SDK).
    pub error: Option<SdkValue>,
    /// `$metadata.httpStatusCode` (AWS SDK).
    pub metadata_http_status_code: Option<JsonValue>,
    /// `$response` (AWS SDK).
    pub response: Option<SdkResponse>,
}

impl ErrorObject {
    /// `new Error(message)`.
    #[must_use]
    pub fn new(message: impl Into<String>) -> Self {
        Self::named("Error", message)
    }

    /// An error with a custom `name`, such as `AbortError`.
    #[must_use]
    pub fn named(name: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            message: message.into(),
            ..Self::default()
        }
    }

    /// Attach an `error.code`.
    #[must_use]
    pub fn with_code(mut self, code: DiagnosticCode) -> Self {
        self.code = Some(code);
        self
    }

    /// Box as a [`Thrown`].
    #[must_use]
    pub fn thrown(self) -> Thrown {
        Arc::new(self)
    }
}

/// A thrown value that is not an `Error` (a string, number, plain object,
/// ...); displays as JS `String(value)`.
#[derive(Debug, Clone, PartialEq, thiserror::Error)]
#[error("{}", js_to_string(.0))]
pub struct ThrownValue(pub JsonValue);

impl ThrownValue {
    /// A thrown string.
    #[must_use]
    pub fn string(text: impl Into<String>) -> Self {
        Self(JsonValue::String(text.into()))
    }

    /// Box as a [`Thrown`].
    #[must_use]
    pub fn thrown(self) -> Thrown {
        Arc::new(self)
    }
}

/// Box any error as a [`Thrown`].
#[must_use]
pub fn thrown(error: impl Error + Send + Sync + 'static) -> Thrown {
    Arc::new(error)
}

/// The JS `error.name` of a thrown `Error`: the [`ErrorObject`] name,
/// `ModelsError`, `AbortError`, or `Error` for every other Rust error.
#[must_use]
pub fn error_name(error: &(dyn Error + 'static)) -> String {
    if let Some(object) = error.downcast_ref::<ErrorObject>() {
        return object.name.clone();
    }
    if error.is::<ModelsError>() {
        return "ModelsError".to_owned();
    }
    if error.is::<AbortError>() {
        return "AbortError".to_owned();
    }
    "Error".to_owned()
}

/// The JS `error.code` when it is a string or number.
fn error_code(error: &(dyn Error + 'static)) -> Option<DiagnosticCode> {
    if let Some(object) = error.downcast_ref::<ErrorObject>() {
        return object.code.clone();
    }
    if let Some(models_error) = error.downcast_ref::<ModelsError>() {
        return Some(DiagnosticCode::String(
            models_error.code.as_str().to_owned(),
        ));
    }
    None
}

/// TS `formatThrownValue`: an `Error`'s message (or its name when the message
/// is empty); any other value as `String(value)`.
#[must_use]
pub fn format_thrown_value(value: &Thrown) -> String {
    if let Some(ThrownValue(value)) = value.downcast_ref::<ThrownValue>() {
        return js_to_string(value);
    }
    let message = value.to_string();
    if message.is_empty() {
        error_name(value.as_ref())
    } else {
        message
    }
}

/// TS `extractDiagnosticError`.
#[must_use]
pub fn extract_diagnostic_error(error: &Thrown) -> DiagnosticErrorInfo {
    if error.is::<ThrownValue>() {
        return DiagnosticErrorInfo {
            name: Some("ThrownValue".to_owned()),
            message: format_thrown_value(error),
            stack: None,
            code: None,
        };
    }
    let name = error_name(error.as_ref());
    let message = error.to_string();
    DiagnosticErrorInfo {
        message: if message.is_empty() {
            name.clone()
        } else {
            message
        },
        name: (!name.is_empty()).then_some(name),
        // Rust errors carry no JS stack trace.
        stack: None,
        code: error_code(error.as_ref()),
    }
}

/// TS `createAssistantMessageDiagnostic`.
#[must_use]
pub fn create_assistant_message_diagnostic(
    kind: &str,
    error: &Thrown,
    details: Option<JsonObject>,
) -> AssistantMessageDiagnostic {
    AssistantMessageDiagnostic {
        kind: kind.to_owned(),
        timestamp: now_ms(),
        error: Some(extract_diagnostic_error(error)),
        details,
    }
}

/// TS `appendAssistantMessageDiagnostic`.
pub fn append_assistant_message_diagnostic(
    message: &mut AssistantMessage,
    diagnostic: AssistantMessageDiagnostic,
) {
    message
        .diagnostics
        .get_or_insert_with(Vec::new)
        .push(diagnostic);
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;
    use crate::utils::models_error::ModelsErrorCode;
    use crate::utils::test_support::faux_text_message;

    #[test]
    fn formats_thrown_values_like_js() {
        assert_eq!(
            format_thrown_value(&ErrorObject::new("boom").thrown()),
            "boom"
        );
        assert_eq!(
            format_thrown_value(&ErrorObject::named("TypeError", "").thrown()),
            "TypeError"
        );
        assert_eq!(
            format_thrown_value(&ThrownValue::string("text").thrown()),
            "text"
        );
        assert_eq!(
            format_thrown_value(&ThrownValue(json!(1.5)).thrown()),
            "1.5"
        );
        assert_eq!(
            format_thrown_value(&ThrownValue(json!({ "a": 1 })).thrown()),
            "[object Object]"
        );
        assert_eq!(
            format_thrown_value(&ThrownValue(json!([1, null, "x"])).thrown()),
            "1,,x"
        );
    }

    #[test]
    fn extracts_diagnostic_errors() {
        assert_eq!(
            extract_diagnostic_error(&ThrownValue::string("oops").thrown()),
            DiagnosticErrorInfo {
                name: Some("ThrownValue".into()),
                message: "oops".into(),
                stack: None,
                code: None,
            }
        );
        let error = ErrorObject::named("SystemError", "")
            .with_code(DiagnosticCode::String("ECONNRESET".into()))
            .thrown();
        assert_eq!(
            extract_diagnostic_error(&error),
            DiagnosticErrorInfo {
                name: Some("SystemError".into()),
                message: "SystemError".into(),
                stack: None,
                code: Some(DiagnosticCode::String("ECONNRESET".into())),
            }
        );
        let models_error = thrown(ModelsError::new(ModelsErrorCode::Auth, "no key"));
        assert_eq!(
            extract_diagnostic_error(&models_error),
            DiagnosticErrorInfo {
                name: Some("ModelsError".into()),
                message: "no key".into(),
                stack: None,
                code: Some(DiagnosticCode::String("auth".into())),
            }
        );
        assert_eq!(
            extract_diagnostic_error(&thrown(eukhe_chord::context::AbortError))
                .name
                .as_deref(),
            Some("AbortError")
        );
    }

    #[test]
    fn creates_and_appends_diagnostics() {
        let mut message = faux_text_message("x");
        let details: JsonObject = json!({ "attempt": 1 }).as_object().unwrap().clone();
        let diagnostic = create_assistant_message_diagnostic(
            "retry",
            &ErrorObject::new("boom").thrown(),
            Some(details),
        );
        assert_eq!(diagnostic.kind, "retry");
        assert!(diagnostic.timestamp > 0);
        assert_eq!(diagnostic.error.as_ref().unwrap().message, "boom");
        append_assistant_message_diagnostic(&mut message, diagnostic.clone());
        append_assistant_message_diagnostic(&mut message, diagnostic.clone());
        assert_eq!(
            message.diagnostics,
            Some(vec![diagnostic.clone(), diagnostic])
        );
    }
}
