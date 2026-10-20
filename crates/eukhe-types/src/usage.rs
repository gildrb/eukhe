//! Context-usage helpers over raw message JSON: pure data helpers shared
//! by crates that read session files in different representations
//! (eukhe-daemon's wire-shaped session store, eukhe-core's typed session manager).
//! Port of `calculateContextTokens` / `getAssistantUsage` from the TS core
//! (compaction + agent-session). The token estimate from text is
//! [`crate::token_estimate`].

use serde_json::Value;

/// `totalTokens` when present, else the four-field sum (TS
/// `calculateContextTokens` over the raw usage object).
pub fn calculate_context_tokens(usage: &Value) -> u64 {
    usage
        .get("totalTokens")
        .and_then(Value::as_u64)
        .filter(|total| *total > 0)
        .unwrap_or_else(|| {
            usage
                .get("input")
                .and_then(Value::as_u64)
                .unwrap_or_default()
                + usage
                    .get("output")
                    .and_then(Value::as_u64)
                    .unwrap_or_default()
                + usage
                    .get("cacheRead")
                    .and_then(Value::as_u64)
                    .unwrap_or_default()
                + usage
                    .get("cacheWrite")
                    .and_then(Value::as_u64)
                    .unwrap_or_default()
        })
}

/// Assistant usage that is safe to read (TS `getAssistantUsage` skips
/// aborted and error stops).
pub fn valid_assistant_usage(message: &Value) -> Option<Value> {
    if message.get("role").and_then(Value::as_str) != Some("assistant") {
        return None;
    }
    if let Some("aborted" | "error") = message.get("stopReason").and_then(Value::as_str) {
        return None;
    }
    message
        .get("usage")
        .cloned()
        .filter(|usage| !usage.is_null())
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn total_tokens_wins_when_positive() {
        assert_eq!(
            calculate_context_tokens(&json!({ "totalTokens": 42, "input": 100 })),
            42
        );
        // A zero totalTokens falls back to the four-field sum.
        assert_eq!(
            calculate_context_tokens(
                &json!({ "totalTokens": 0, "input": 10, "output": 20, "cacheRead": 5, "cacheWrite": 7 })
            ),
            42
        );
    }

    #[test]
    fn assistant_usage_skips_aborted_and_error_stops() {
        assert_eq!(
            valid_assistant_usage(&json!({ "role": "user", "usage": { "input": 1 } })),
            None
        );
        assert_eq!(
            valid_assistant_usage(
                &json!({ "role": "assistant", "stopReason": "aborted", "usage": { "input": 1 } })
            ),
            None
        );
        assert_eq!(
            valid_assistant_usage(
                &json!({ "role": "assistant", "stopReason": "error", "usage": { "input": 1 } })
            ),
            None
        );
        let usage = valid_assistant_usage(&json!({ "role": "assistant", "usage": { "input": 3 } }));
        assert_eq!(usage, Some(json!({ "input": 3 })));
    }
}
