//! Shared normalization for provider HTTP error objects.
//!
//! Endpoints behind a proxy or gateway may return a non-2xx response whose
//! body the provider SDK cannot fold into `error.message`. The error still
//! carries the HTTP status and the raw/parsed body under SDK-specific field
//! names (see [`ErrorObject`]). [`normalize_provider_error`] probes the known
//! shapes (Mistral, `openai`, `@google/genai`, AWS Bedrock) and returns a
//! struct each provider composes into its display string.
//! `message_carries_body` captures the Anthropic / `@google/genai` happy path
//! where the SDK already folded the body into the message.

use eukhe_types::pi_ai::JsonValue;

use super::diagnostics::{ErrorObject, SdkValue, Thrown, ThrownValue};
use super::js::{json_stringify, number_to_js_string, utf16_len, utf16_prefix};

/// Cap on the body text surfaced from a provider error.
pub const MAX_PROVIDER_ERROR_BODY_CHARS: usize = 4000;

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
    let (status, body) = error
        .downcast_ref::<ErrorObject>()
        .map_or((None, None), |object| {
            (extract_status(object), extract_body(object))
        });
    let message_carries_body = body
        .as_ref()
        .is_none_or(|body| message.contains(body.as_str()));
    NormalizedProviderError {
        status,
        body,
        message,
        message_carries_body,
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

/// Probe the raw body reason, first usable hit wins, in SDK-field order:
/// `body` string (Mistral) → `error` parsed JSON body object (`openai`) →
/// `$response.body` (Bedrock). Empty objects and unread response streams are
/// treated as no body. The chosen body is truncated to the cap.
fn extract_body(error: &ErrorObject) -> Option<String> {
    let body_text = pick_body_text(error)?;
    let trimmed = body_text.trim_matches(super::js::is_js_whitespace);
    if trimmed.is_empty() {
        return None;
    }
    Some(truncate_error_text(trimmed, MAX_PROVIDER_ERROR_BODY_CHARS))
}

fn pick_body_text(error: &ErrorObject) -> Option<String> {
    if let Some(SdkValue::Json(JsonValue::String(body))) = &error.body {
        return Some(body.clone());
    }
    if let Some(SdkValue::Json(value)) = &error.error {
        if is_plain_non_empty_object(value) {
            return Some(safe_json_stringify(value));
        }
    }
    match error
        .response
        .as_ref()
        .and_then(|response| response.body.as_ref())
    {
        Some(SdkValue::Json(JsonValue::String(body))) => Some(body.clone()),
        Some(SdkValue::Json(value)) if is_plain_non_empty_object(value) => {
            Some(safe_json_stringify(value))
        }
        Some(SdkValue::Json(_) | SdkValue::Stream | SdkValue::Instance) | None => None,
    }
}

/// Only a plain, non-empty object counts as an HTTP body. Class instances
/// ([`SdkValue::Instance`]) and streams never do: serializing them yields
/// internals noise that would replace the real message.
fn is_plain_non_empty_object(value: &JsonValue) -> bool {
    value.as_object().is_some_and(|object| !object.is_empty())
}

/// Compose a display string from a normalized error. When the message
/// already carries the body or no body/status was extracted, the message is
/// returned (prefixed with the status when a prefix is given). Otherwise the
/// status and body are surfaced: `"<status>: <body>"` or
/// `"<prefix> (<status>): <body>"`.
#[must_use]
pub fn format_provider_error(norm: &NormalizedProviderError, prefix: Option<&str>) -> String {
    match (norm.message_carries_body, norm.status, norm.body.as_deref()) {
        (false, Some(status), Some(body)) => {
            let status = number_to_js_string(status);
            match prefix {
                Some(prefix) => format!("{prefix} ({status}): {body}"),
                None => format!("{status}: {body}"),
            }
        }
        (_, status, _) => match (prefix, status) {
            (Some(prefix), Some(status)) => {
                format!(
                    "{prefix} ({}): {}",
                    number_to_js_string(status),
                    norm.message
                )
            }
            _ => norm.message.clone(),
        },
    }
}

/// Truncate `text` to `max_chars` UTF-16 code units with a marker.
#[must_use]
pub fn truncate_error_text(text: &str, max_chars: usize) -> String {
    let length = utf16_len(text);
    if length <= max_chars {
        return text.to_owned();
    }
    format!(
        "{}... [truncated {} chars]",
        utf16_prefix(text, max_chars),
        length - max_chars
    )
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

    #[test]
    fn truncates_the_body_at_the_cap() {
        let long_body = "x".repeat(MAX_PROVIDER_ERROR_BODY_CHARS + 50);
        let error = ErrorObject {
            status_code: Some(json!(500)),
            body: Some(SdkValue::Json(JsonValue::String(long_body.clone()))),
            ..error_object("failed")
        }
        .thrown();
        let norm = normalize_provider_error(&error);
        let body = norm.body.unwrap();
        assert!(body.contains("... [truncated 50 chars]"));
        assert!(body.len() < long_body.len());
    }

    #[test]
    fn sets_message_carries_body_when_the_message_already_contains_the_extracted_body() {
        let error = ErrorObject {
            status_code: Some(json!(500)),
            body: Some(SdkValue::Json(json!("upstream exploded"))),
            ..error_object("500: upstream exploded")
        }
        .thrown();
        assert!(normalize_provider_error(&error).message_carries_body);
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
    fn surfaces_status_and_body_without_a_prefix() {
        let formatted = format_provider_error(&waf_error(), None);
        assert!(formatted.contains("403"));
        assert!(formatted.contains("blocked by gateway WAF"));
        assert_ne!(formatted, "403 status code (no body)");
    }

    #[test]
    fn applies_a_provider_prefix_with_status_and_body() {
        assert_eq!(
            format_provider_error(&waf_error(), Some("OpenAI API error")),
            r#"OpenAI API error (403): {"error":"blocked by gateway WAF"}"#
        );
    }

    #[test]
    fn preserves_the_message_with_prefix_and_status_when_it_already_carries_the_body() {
        let body = json!({ "error": { "message": "Permission denied" } }).to_string();
        let norm = normalize_provider_error(
            &ErrorObject {
                status: Some(Some(json!(403))),
                ..error_object(&body)
            }
            .thrown(),
        );
        assert_eq!(
            format_provider_error(&norm, Some("OpenAI API error")),
            format!("OpenAI API error (403): {body}")
        );
    }

    #[test]
    fn returns_the_bare_message_for_a_non_error_value() {
        let norm = normalize_provider_error(&ThrownValue(json!({ "reason": "boom" })).thrown());
        assert_eq!(format_provider_error(&norm, None), r#"{"reason":"boom"}"#);
    }
}
