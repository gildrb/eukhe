//! The outcome/provider/model/error classification family (moved with its
//! concern): the TS `runOutcome`/`telemetryProviderCategory`/`modelCategory`/
//! `errorCategory` ports and their string-matching helpers.
use eukhe_types::pi_ai::{AssistantMessage, StopReason};
use serde_json::Value;

/// Run outcome per the TS `runOutcome`: aborted beats error beats success.
pub(crate) fn run_outcome(last_assistant: Option<&AssistantMessage>) -> &'static str {
    match last_assistant {
        Some(message) => match message.stop_reason {
            StopReason::Aborted => "aborted",
            StopReason::Error => "error",
            _ => "success",
        },
        None => "error",
    }
}

pub(crate) fn opt_value(value: Option<u64>) -> Value {
    value.map_or(Value::Null, Value::from)
}

/// TS `telemetryProviderCategory`.
pub fn provider_category(provider: Option<&str>) -> String {
    let Some(provider) = provider else {
        return "unknown".to_string();
    };
    let normalized = provider.to_ascii_lowercase();
    let categories = [
        "anthropic",
        "openai",
        "google",
        "prime",
        "openrouter",
        "bedrock",
        "vertex",
        "mistral",
        "groq",
        "xai",
    ];
    categories
        .iter()
        .find(|category| normalized.contains(*category))
        .map_or_else(|| "custom".to_string(), std::string::ToString::to_string)
}

/// TS `modelCategory`.
pub(crate) fn model_category(model: &str) -> &str {
    let normalized = model.to_ascii_lowercase();
    let categories = [
        "claude", "gpt", "o1", "o3", "o4", "gemini", "glm", "kimi", "qwen", "deepseek", "llama",
        "mistral",
    ];
    categories
        .iter()
        .find(|category| normalized.contains(*category))
        .copied()
        .unwrap_or("custom")
}

/// TS `errorCategory`: classify the assistant error message; null when the
/// run did not end in an error. Regex ports:
/// `\b401\b|\b403\b|auth|api.?key|credential|unauthori[sz]ed|forbidden` etc.
pub(crate) fn error_category(last_assistant: Option<&AssistantMessage>) -> Value {
    let Some(message) = last_assistant else {
        return Value::Null;
    };
    if message.stop_reason != StopReason::Error {
        return Value::Null;
    }
    let error = message
        .error_message
        .as_deref()
        .unwrap_or_default()
        .to_ascii_lowercase();
    let authentication = error.contains("auth")
        || error.contains("credential")
        || error.contains("unauthori")
        || error.contains("forbidden")
        || contains_any(&error, &["401", "403"])
        || near(&error, "api", "key");
    if authentication {
        return Value::from("authentication");
    }
    if contains_any(&error, &["429"]) || near(&error, "rate", "limit") || error.contains("quota") {
        return Value::from("rate_limit");
    }
    if error.contains("timeout") || error.contains("timed out") {
        return Value::from("timeout");
    }
    let context_limit = error.contains("context")
        || contains_in_order(&error, "token", "limit")
        || error.contains("too long")
        || contains_in_order(&error, "maximum", "length");
    if context_limit {
        return Value::from("context_limit");
    }
    if error.contains("network")
        || error.contains("socket")
        || error.contains("connection")
        || error.contains("fetch")
    {
        return Value::from("network");
    }
    if looks_like_5xx(&error) || error.contains("overload") || error.contains("unavailable") {
        return Value::from("provider_unavailable");
    }
    Value::from("other")
}

/// TS `a.?b` two-word match: the words with at most one character between.
fn near(haystack: &str, first: &str, second: &str) -> bool {
    haystack.match_indices(first).any(|(index, _)| {
        let rest = &haystack[index + first.len()..];
        rest.find(second).is_some_and(|offset| offset <= 1)
    })
}

/// TS `a.*b` two-word match: both present, `first` before `second`.
fn contains_in_order(haystack: &str, first: &str, second: &str) -> bool {
    haystack
        .find(first)
        .and_then(|first_at| haystack[first_at + first.len()..].find(second).map(|_| ()))
        .is_some()
}

fn contains_any(haystack: &str, needles: &[&str]) -> bool {
    needles.iter().any(|needle| haystack.contains(needle))
}

/// `\b5\d\d\b` from the TS regex, approximated on a lowercased message: a
/// 500..=599 run bounded by non-digits.
fn looks_like_5xx(error: &str) -> bool {
    let bytes = error.as_bytes();
    for index in 0..bytes.len() {
        if bytes[index] != b'5' || index + 2 >= bytes.len() {
            continue;
        }
        let (b, c) = (bytes[index + 1], bytes[index + 2]);
        if !b.is_ascii_digit() || !c.is_ascii_digit() {
            continue;
        }
        let digit_before = index > 0 && bytes[index - 1].is_ascii_digit();
        let digit_after = index + 3 < bytes.len() && bytes[index + 3].is_ascii_digit();
        if !digit_before && !digit_after {
            return true;
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use eukhe_types::pi_ai::{AssistantContentBlock, TextContent, Usage, UsageCost};

    fn assistant_message() -> AssistantMessage {
        AssistantMessage {
            content: vec![AssistantContentBlock::Text(TextContent {
                text: "private assistant text".to_string(),
                text_signature: None,
                cache_breakpoint: None,
            })],
            api: "test".to_string(),
            provider: "openai".to_string(),
            model: "gpt-test".to_string(),
            response_model: None,
            response_id: None,
            provider_thinking_level: None,
            thinking_level: None,
            diagnostics: None,
            usage: Usage {
                input: 100,
                output: 20,
                cache_read: 50,
                cache_write: 0,
                cache_write_1h: None,
                reasoning: None,
                total_tokens: 170,
                cost: UsageCost::default(),
            },
            stop_reason: StopReason::Stop,
            deferred: None,
            error_message: None,
            raw_stop_reason: None,
            end_turn: None,
            timestamp: 0,
        }
    }

    fn assistant_with_error(error: &str) -> AssistantMessage {
        let mut message = assistant_message();
        message.stop_reason = StopReason::Error;
        message.error_message = Some(error.to_string());
        message
    }

    /// Error-category classifier matrix (TS `errorCategory`).
    #[test]
    fn error_categories() {
        fn category(error: &str) -> String {
            let message = assistant_with_error(error);
            error_category(Some(&message))
                .as_str()
                .expect("category")
                .to_string()
        }
        assert_eq!(category("Unauthorized: invalid api key"), "authentication");
        assert_eq!(category("403 forbidden"), "authentication");
        assert_eq!(category("credential expired"), "authentication");
        assert_eq!(category("429 quota exceeded"), "rate_limit");
        assert_eq!(category("request timed out"), "timeout");
        assert_eq!(category("context length too long"), "context_limit");
        assert_eq!(category("maximum context length exceeded"), "context_limit");
        assert_eq!(category("network socket connection reset"), "network");
        assert_eq!(category("fetch failed"), "network");
        assert_eq!(
            category("503 overloaded, service unavailable"),
            "provider_unavailable"
        );
        assert_eq!(category("something unexpected happened"), "other");
        assert_eq!(
            error_category(Some(&assistant_message())),
            serde_json::Value::Null
        );
    }

    /// Provider/model categories (TS `telemetryProviderCategory` /
    /// `modelCategory`).
    #[test]
    fn provider_and_model_categories() {
        assert_eq!(provider_category(Some("prime")), "prime");
        assert_eq!(provider_category(Some("ANTHROPIC")), "anthropic");
        assert_eq!(provider_category(Some("custom-host")), "custom");
        assert_eq!(provider_category(None), "unknown");
        assert_eq!(model_category("glm-4.6"), "glm");
        assert_eq!(model_category("Claude-Sonnet-4"), "claude");
        assert_eq!(model_category("kimi-k2"), "kimi");
        assert_eq!(model_category("my-finetune"), "custom");
    }
}
