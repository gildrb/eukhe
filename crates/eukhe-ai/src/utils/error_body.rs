//! Shared normalization for provider HTTP error objects.
//!
//! Endpoints behind a proxy or gateway may return a non-2xx response whose
//! body the provider SDK cannot fold into `error.message`. The error still
//! carries the HTTP status and the raw/parsed body under SDK-specific field
//! names (see [`ErrorObject`]). [`normalize_provider_error`] reads the known
//! shapes (Mistral, `openai`, `@google/genai`, AWS Bedrock) and returns a
//! struct each provider composes into its display string. Which place's
//! body counts, its trim and cap, and the display string are the compiled
//! core's (`eukhe_bend::rules::error_body`); this module reads the SDK's
//! fields, serializes object bodies, renders the status, and finds whether
//! the message already carries the body (the Anthropic / `@google/genai`
//! happy path): a substring search, linear here where the core's naive
//! search was quadratic (20,000 chars against a 4,000-char body: 3.5 s).

use eukhe_bend::rules::error_body::{self as rules, Probe, Shown};
use eukhe_types::pi_ai::JsonValue;

use super::diagnostics::{ErrorObject, SdkValue, Thrown, ThrownValue};
use super::js::{json_stringify, number_to_js_string};

/// A provider error reduced to what display strings need.
#[derive(Debug, Clone, PartialEq)]
pub struct NormalizedProviderError {
    /// HTTP status code, when one could be extracted.
    pub status: Option<f64>,
    /// Raw HTTP body reason, trimmed and truncated to the cap.
    pub body: Option<String>,
    /// `error.message`, or `safeJsonStringify(error)` for a non-`Error` throw.
    pub message: String,
    /// True when `message` already contains the body (no separate body to add).
    pub message_carries_body: bool,
}

/// TS `normalizeProviderError`.
#[must_use]
pub fn normalize_provider_error(error: &Thrown) -> NormalizedProviderError {
    if let Some(ThrownValue(value)) = error.downcast_ref::<ThrownValue>() {
        return NormalizedProviderError {
            status: None,
            body: None,
            message: safe_json_stringify(value),
            message_carries_body: false,
        };
    }
    let message = error.to_string();
    let Some(object) = error.downcast_ref::<ErrorObject>() else {
        return NormalizedProviderError {
            status: None,
            body: None,
            message,
            message_carries_body: true,
        };
    };
    let body = Place::of(object.body.as_ref());
    let parsed = Place::of(object.error.as_ref());
    let response = Place::of(
        object
            .response
            .as_ref()
            .and_then(|response| response.body.as_ref()),
    );
    let body = rules::body(body.probe(), parsed.probe(), response.probe());
    let message_carries_body = body.as_deref().is_none_or(|body| message.contains(body));
    NormalizedProviderError {
        status: extract_status(object),
        body,
        message,
        message_carries_body,
    }
}

/// What one place of the error holds, owned: a JSON string, or a plain
/// object with a key serialized (class instances and streams never count:
/// serializing them yields internals noise that would replace the real
/// message).
enum Place {
    Nothing,
    Text(String),
    Object(String),
}

impl Place {
    fn of(value: Option<&SdkValue>) -> Place {
        match value {
            Some(SdkValue::Json(JsonValue::String(text))) => Place::Text(text.clone()),
            Some(SdkValue::Json(JsonValue::Object(object))) if !object.is_empty() => {
                Place::Object(json_stringify(&JsonValue::Object(object.clone())))
            }
            Some(SdkValue::Json(_) | SdkValue::Stream | SdkValue::Instance) | None => {
                Place::Nothing
            }
        }
    }

    fn probe(&self) -> Probe<'_> {
        match self {
            Place::Nothing => Probe::Nothing,
            Place::Text(text) => Probe::Text(text),
            Place::Object(text) => Probe::Object(text),
        }
    }
}

/// `typeof value === "number"`.
fn number_property(value: Option<&JsonValue>) -> Option<f64> {
    value?.as_f64()
}

/// Probe the HTTP status, first numeric hit wins, in SDK-field order:
/// `statusCode` (Mistral) → `status` (`openai`, `@google/genai`) →
/// `$metadata.httpStatusCode` (Bedrock) → `$response.statusCode` (Bedrock).
fn extract_status(error: &ErrorObject) -> Option<f64> {
    number_property(error.status_code.as_ref())
        .or_else(|| number_property(error.status.as_ref().and_then(Option::as_ref)))
        .or_else(|| number_property(error.metadata_http_status_code.as_ref()))
        .or_else(|| {
            number_property(
                error
                    .response
                    .as_ref()
                    .and_then(|response| response.status_code.as_ref()),
            )
        })
}

/// Compose a display string from a normalized error: `"<status>: <body>"`
/// or `"<prefix> (<status>): <body>"` when the message lacks the body, else
/// the message (after the prefix and the status when both are given).
#[must_use]
pub fn format_provider_error(norm: &NormalizedProviderError, prefix: Option<&str>) -> String {
    let status = norm.status.map(number_to_js_string);
    rules::show(&Shown {
        carried: norm.message_carries_body,
        status: status.as_deref(),
        body: norm.body.as_deref(),
        prefix,
        message: &norm.message,
    })
}

/// Truncate `text` to `max_chars` UTF-16 code units with a marker.
#[must_use]
pub fn truncate_error_text(text: &str, max_chars: usize) -> String {
    rules::truncate(text, max_chars)
}

/// `JSON.stringify(value)` (a JSON value always serializes).
#[must_use]
pub fn safe_json_stringify(value: &JsonValue) -> String {
    json_stringify(value)
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::super::diagnostics::SdkResponse;
    use super::*;

    fn error_object(message: &str) -> ErrorObject {
        ErrorObject::new(message)
    }

    #[test]
    fn extracts_status_and_body_from_a_mistral_shaped_error() {
        let error = ErrorObject {
            status_code: Some(json!(403)),
            body: Some(SdkValue::Json(json!(
                r#"{"error":"blocked by gateway WAF"}"#
            ))),
            ..error_object("Mistral request failed")
        }
        .thrown();
        let norm = normalize_provider_error(&error);
        assert_eq!(norm.status, Some(403.0));
        assert_eq!(
            norm.body.as_deref(),
            Some(r#"{"error":"blocked by gateway WAF"}"#)
        );
        assert!(!norm.message_carries_body);
    }

    #[test]
    fn reads_the_parsed_body_off_an_openai_api_error_when_the_message_is_opaque() {
        let error = ErrorObject {
            status: Some(Some(json!(403))),
            error: Some(SdkValue::Json(json!({ "error": "blocked by gateway WAF" }))),
            ..error_object("403 status code (no body)")
        }
        .thrown();
        let norm = normalize_provider_error(&error);
        assert_eq!(norm.status, Some(403.0));
        assert_eq!(
            norm.body.as_deref(),
            Some(r#"{"error":"blocked by gateway WAF"}"#)
        );
        assert!(!norm.message_carries_body);
    }

    #[test]
    fn preserves_the_message_when_google_genai_already_folds_the_body_into_it() {
        let body = json!({ "error": { "code": 403, "message": "Permission denied" } }).to_string();
        let error = ErrorObject {
            status: Some(Some(json!(403))),
            ..error_object(&body)
        }
        .thrown();
        let norm = normalize_provider_error(&error);
        assert_eq!(norm.status, Some(403.0));
        assert!(norm.message_carries_body);
        assert_eq!(norm.message, body);
    }

    #[test]
    fn extracts_status_and_body_from_a_bedrock_shaped_service_exception() {
        let error = ErrorObject {
            metadata_http_status_code: Some(json!(403)),
            response: Some(SdkResponse {
                status_code: Some(json!(403)),
                body: Some(SdkValue::Json(json!(
                    r#"{"message":"blocked by gateway WAF"}"#
                ))),
            }),
            ..ErrorObject::named("UnknownError", "UnknownError")
        }
        .thrown();
        let norm = normalize_provider_error(&error);
        assert_eq!(norm.status, Some(403.0));
        assert_eq!(
            norm.body.as_deref(),
            Some(r#"{"message":"blocked by gateway WAF"}"#)
        );
        assert!(!norm.message_carries_body);
    }

    #[test]
    fn ignores_a_bedrock_response_stream_instead_of_serializing_its_internals() {
        let error = ErrorObject {
            metadata_http_status_code: Some(json!(400)),
            response: Some(SdkResponse {
                status_code: Some(json!(400)),
                body: Some(SdkValue::Stream),
            }),
            ..ErrorObject::named(
                "ValidationException",
                "Invocation of model ID anthropic.claude-opus-5 with on-demand throughput isn't supported.",
            )
        }
        .thrown();
        let norm = normalize_provider_error(&error);
        assert_eq!(norm.status, Some(400.0));
        assert_eq!(norm.body, None);
        assert!(norm
            .message
            .contains("on-demand throughput isn't supported"));
        assert!(norm.message_carries_body);
    }

    #[test]
    fn ignores_a_class_instance_response_body_without_a_pipe_method_instead_of_serializing_it() {
        let error = ErrorObject {
            metadata_http_status_code: Some(json!(400)),
            response: Some(SdkResponse {
                status_code: Some(json!(400)),
                body: Some(SdkValue::Instance),
            }),
            ..ErrorObject::named(
                "ValidationException",
                "Input is too long for requested model.",
            )
        }
        .thrown();
        let norm = normalize_provider_error(&error);
        assert_eq!(norm.status, Some(400.0));
        assert_eq!(norm.body, None);
        assert!(norm.message.contains("Input is too long"));
        assert!(norm.message_carries_body);
    }

    #[test]
    fn ignores_a_class_instance_error_field_instead_of_serializing_it() {
        let error = ErrorObject {
            status: Some(Some(json!(502))),
            error: Some(SdkValue::Instance),
            ..error_object("TLS handshake failed")
        }
        .thrown();
        let norm = normalize_provider_error(&error);
        assert_eq!(norm.body, None);
        assert_eq!(norm.message, "TLS handshake failed");
        assert!(norm.message_carries_body);
    }

    #[test]
    fn still_surfaces_a_plain_parsed_json_body_object() {
        let error = ErrorObject {
            status: Some(Some(json!(400))),
            error: Some(SdkValue::Json(
                json!({ "message": "schema validation failed", "field": "tools[0]" }),
            )),
            ..error_object("400 status code (no body)")
        }
        .thrown();
        let norm = normalize_provider_error(&error);
        assert_eq!(
            norm.body.as_deref(),
            Some(r#"{"message":"schema validation failed","field":"tools[0]"}"#)
        );
        assert!(!norm.message_carries_body);
    }

    #[test]
    fn json_stringifies_a_non_error_thrown_value() {
        let norm = normalize_provider_error(&ThrownValue(json!({ "reason": "boom" })).thrown());
        assert_eq!(norm.status, None);
        assert_eq!(norm.body, None);
        assert_eq!(norm.message, r#"{"reason":"boom"}"#);
        assert!(!norm.message_carries_body);
    }

    #[test]
    fn treats_an_empty_parsed_body_object_as_no_body() {
        let error = ErrorObject {
            status: Some(Some(json!(403))),
            error: Some(SdkValue::Json(json!({}))),
            ..error_object("403 status code (no body)")
        }
        .thrown();
        let norm = normalize_provider_error(&error);
        assert_eq!(norm.body, None);
        assert!(norm.message_carries_body);
    }

    fn waf_error() -> NormalizedProviderError {
        normalize_provider_error(
            &ErrorObject {
                status: Some(Some(json!(403))),
                error: Some(SdkValue::Json(json!({ "error": "blocked by gateway WAF" }))),
                ..error_object("403 status code (no body)")
            }
            .thrown(),
        )
    }

    #[test]
    fn applies_a_provider_prefix_with_status_and_body() {
        assert_eq!(
            format_provider_error(&waf_error(), Some("OpenAI API error")),
            r#"OpenAI API error (403): {"error":"blocked by gateway WAF"}"#
        );
    }
}
