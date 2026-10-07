//! Context overflow detection.
//!
//! The patterns match the errors providers return when the input exceeds the
//! model's context window (see the TS source for one example per provider):
//! Anthropic, Bedrock, `OpenAI` (and `LiteLLM` / OpenAI-compatible proxies),
//! Google, xAI, Groq, `OpenRouter`, Together AI, GitHub Copilot, llama.cpp,
//! LM Studio, `MiniMax`, Kimi For Coding, Mistral, DS4, z.ai, Ollama, and
//! `DashScope`/Qwen. Cerebras overflows as a bodyless 400/413. z.ai can
//! overflow silently (usage above the window) and Xiaomi `MiMo` truncates
//! input and stops with `length` and zero output.
//!
//! JS `\d` is ASCII-only, so the Rust patterns spell it `[0-9]`.

use std::sync::LazyLock;

use regex::Regex;

use eukhe_types::pi_ai::{AssistantMessage, StopReason};

fn case_insensitive(pattern: &str) -> Regex {
    Regex::new(&format!("(?i){pattern}"))
        .unwrap_or_else(|error| panic!("invalid overflow pattern {pattern}: {error}"))
}

static OVERFLOW_PATTERNS: LazyLock<Vec<Regex>> = LazyLock::new(|| {
    [
        r"prompt (?:is )?too long",   // Anthropic and z.ai token overflow
        r"prompt exceeds max length", // z.ai CN endpoint token overflow
        r"request_too_large",         // Anthropic request byte-size overflow (HTTP 413)
        r"input is too long for requested model", // Amazon Bedrock
        r"exceeds the context window", // OpenAI (Completions & Responses API)
        r"exceeds (?:the )?(?:model'?s )?maximum context length(?: of [0-9,]+ tokens?|\s*\([0-9,]+\))", // OpenAI-compatible proxies (LiteLLM)
        r"input token count.*exceeds the maximum", // Google (Gemini)
        r"maximum prompt length is [0-9]+",        // xAI (Grok)
        r"reduce the length of the messages",      // Groq
        r"maximum context length is [0-9]+ tokens", // OpenRouter (most backends)
        r"exceeds (?:the )?maximum allowed input length of [0-9,]+ tokens?", // OpenRouter/Poolside
        r"input \([0-9]+ tokens\) is longer than the model'?s context length \([0-9]+ tokens\)", // Together AI
        r"exceeds the limit of [0-9]+",        // GitHub Copilot
        r"exceeds the available context size", // llama.cpp server
        r"greater than the context length",    // LM Studio
        r"context window exceeds limit",       // MiniMax
        r"exceeded model token limit",         // Kimi For Coding
        r"too large for model with [0-9]+ maximum context length", // Mistral
        r"prompt has [0-9,]+ tokens?, but the configured context size is [0-9,]+ tokens?", // DS4 server
        r"model_context_window_exceeded", // z.ai non-standard finish_reason surfaced as error text
        r"prompt too long; exceeded (?:max )?context length", // Ollama explicit overflow error
        r"range of input length should be", // DashScope / Qwen Token Plan
        r"context[_ ]length[_ ]exceeded", // Generic fallback
        r"too many tokens",               // Generic fallback
        r"token limit exceeded",          // Generic fallback
    ]
    .into_iter()
    .map(case_insensitive)
    .collect()
});

static CEREBRAS_BODYLESS_OVERFLOW_PATTERN: LazyLock<Regex> =
    LazyLock::new(|| case_insensitive(r"^4(?:00|13)\s*(?:status code)?\s*\(no body\)"));

/// Errors that are not overflow (rate limiting, server errors) even when they
/// match an overflow pattern, e.g. Bedrock's "`ThrottlingException`: Too many
/// tokens, please wait before trying again."
static NON_OVERFLOW_PATTERNS: LazyLock<Vec<Regex>> = LazyLock::new(|| {
    [
        r"^(Throttling error|Service unavailable):", // AWS Bedrock non-overflow errors (formatBedrockError prefixes)
        r"rate limit",                               // Generic rate limiting
        r"too many requests",                        // Generic HTTP 429 style
    ]
    .into_iter()
    .map(case_insensitive)
    .collect()
});

/// Whether an assistant message represents a context overflow error:
///
/// 1. error-based overflow: `stop_reason` `error` with a known message;
/// 2. silent overflow (z.ai): a successful response whose input usage exceeds
///    `context_window`;
/// 3. length-stop overflow (Xiaomi `MiMo`): `length` with zero output and the
///    input filling the context window.
///
/// Pass `context_window` to detect cases 2 and 3 (`None`/`Some(0)` skips them).
#[must_use]
pub fn is_context_overflow(message: &AssistantMessage, context_window: Option<u64>) -> bool {
    if message.stop_reason == StopReason::Error {
        if let Some(error_message) = message
            .error_message
            .as_deref()
            .filter(|text| !text.is_empty())
        {
            let is_non_overflow = NON_OVERFLOW_PATTERNS
                .iter()
                .any(|pattern| pattern.is_match(error_message));
            if !is_non_overflow {
                if OVERFLOW_PATTERNS
                    .iter()
                    .any(|pattern| pattern.is_match(error_message))
                {
                    return true;
                }
                if message.provider == "cerebras"
                    && CEREBRAS_BODYLESS_OVERFLOW_PATTERN.is_match(error_message)
                {
                    return true;
                }
            }
        }
    }

    let Some(context_window) = context_window.filter(|window| *window > 0) else {
        return false;
    };
    let input_tokens = message.usage.input + message.usage.cache_read;
    if message.stop_reason == StopReason::Stop && input_tokens > context_window {
        return true;
    }
    if message.stop_reason == StopReason::Length && message.usage.output == 0 {
        // JS number arithmetic: token counts are far below 2^53.
        #[allow(clippy::cast_precision_loss)]
        let filled = input_tokens as f64 >= context_window as f64 * 0.99;
        if filled {
            return true;
        }
    }
    false
}

/// Whether a length stop ended below the intended output limit
/// (`desired_max_output`, the original limit before context-based clamping):
/// context pressure or provider truncation, worth one compact-and-retry.
#[must_use]
pub fn is_recoverable_length(message: &AssistantMessage, desired_max_output: u64) -> bool {
    message.stop_reason == StopReason::Length
        && desired_max_output > 0
        && message.usage.output < desired_max_output
}

/// The overflow patterns, for testing purposes.
#[must_use]
pub fn get_overflow_patterns() -> Vec<Regex> {
    OVERFLOW_PATTERNS.clone()
}

#[cfg(test)]
mod tests {
    use eukhe_types::pi_ai::{Usage, UsageCost};

    use super::*;

    fn message(
        stop_reason: StopReason,
        provider: &str,
        error_message: Option<&str>,
        usage: Usage,
    ) -> AssistantMessage {
        AssistantMessage {
            content: Vec::new(),
            api: "openai-completions".into(),
            provider: provider.into(),
            model: "qwen3.5:35b".into(),
            response_model: None,
            response_id: None,
            provider_thinking_level: None,
            thinking_level: None,
            diagnostics: None,
            usage,
            stop_reason,
            deferred: None,
            error_message: error_message.map(str::to_owned),
            raw_stop_reason: None,
            end_turn: None,
            timestamp: 1,
        }
    }

    fn create_error_message(error_message: &str, provider: &str) -> AssistantMessage {
        message(
            StopReason::Error,
            provider,
            Some(error_message),
            Usage::default(),
        )
    }

    fn create_length_stop_message(
        input: u64,
        cache_read: u64,
        output: u64,
        cache_write: u64,
    ) -> AssistantMessage {
        message(
            StopReason::Length,
            "test-provider",
            None,
            Usage {
                input,
                output,
                cache_read,
                cache_write,
                total_tokens: input + cache_read + cache_write + output,
                cost: UsageCost::default(),
                ..Usage::default()
            },
        )
    }

    #[test]
    fn detects_explicit_ollama_prompt_too_long_errors() {
        let message = create_error_message(
            "400 `prompt too long; exceeded max context length by 100918 tokens`",
            "ollama",
        );
        assert!(is_context_overflow(&message, Some(32768)));
    }

    #[test]
    fn detects_zai_prompt_too_long_errors() {
        let message =
            create_error_message(r#"400 {"code":"1261","message":"Prompt too long"}"#, "zai");
        assert!(is_context_overflow(&message, Some(1_048_576)));
    }

    #[test]
    fn detects_zai_cn_endpoint_prompt_exceeds_max_length_errors() {
        let message = create_error_message(
            r#"400 {"code":"1261","message":"Prompt exceeds max length"}"#,
            "zai",
        );
        assert!(is_context_overflow(&message, Some(1_048_576)));
    }

    #[test]
    fn detects_together_ai_context_length_errors() {
        let message = create_error_message(
            "400 The input (516368 tokens) is longer than the model's context length (262144 tokens).",
            "ollama",
        );
        assert!(is_context_overflow(&message, Some(262_144)));
    }

    #[test]
    fn detects_litellm_wrapped_openai_maximum_context_length_errors() {
        let message = create_error_message(
            "Error: 503 litellm.ServiceUnavailableError: litellm.MidStreamFallbackError: litellm.APIConnectionError: APIConnectionError: OpenAIException - Requested token count exceeds the model's maximum context length of 131072 tokens.",
            "ollama",
        );
        assert!(is_context_overflow(&message, Some(131_072)));
    }

    #[test]
    fn detects_openai_compatible_parenthesized_maximum_context_length_errors() {
        let message = create_error_message(
            "Error: 400 Input length (265330) exceeds model's maximum context length (262144).",
            "ollama",
        );
        assert!(is_context_overflow(&message, Some(262_144)));
    }

    #[test]
    fn detects_openrouter_poolside_maximum_allowed_input_length_errors() {
        let message = create_error_message(
            "Provider returned error: Input length 131393 exceeds the maximum allowed input length of 131040 tokens.",
            "ollama",
        );
        assert!(is_context_overflow(&message, Some(131_072)));
    }

    #[test]
    fn detects_ds4_configured_context_size_errors() {
        let message = create_error_message(
            "400 Prompt has 256468 tokens, but the configured context size is 256000 tokens",
            "ollama",
        );
        assert!(is_context_overflow(&message, Some(256_000)));
        let comma_message = create_error_message(
            "Prompt has 5,958,968 tokens, but the configured context size is 256,000 tokens",
            "ollama",
        );
        assert!(is_context_overflow(&comma_message, Some(256_000)));
    }

    #[test]
    fn does_not_treat_generic_non_overflow_ollama_errors_as_overflow() {
        let message = create_error_message("500 `model runner crashed unexpectedly`", "ollama");
        assert!(!is_context_overflow(&message, Some(32768)));
    }

    #[test]
    fn only_treats_bodyless_400_and_413_errors_as_overflow_for_cerebras() {
        for error_message in ["400 status code (no body)", "413 status code (no body)"] {
            assert!(is_context_overflow(
                &create_error_message(error_message, "cerebras"),
                Some(131_072)
            ));
            assert!(!is_context_overflow(
                &create_error_message(error_message, "opencode-go"),
                Some(1_000_000)
            ));
        }
    }

    #[test]
    fn does_not_treat_bedrock_throttling_too_many_tokens_as_overflow() {
        let message = create_error_message(
            "Throttling error: Too many tokens, please wait before trying again.",
            "ollama",
        );
        assert!(!is_context_overflow(&message, Some(200_000)));
    }

    #[test]
    fn does_not_treat_bedrock_service_unavailable_as_overflow() {
        let message = create_error_message(
            "Service unavailable: The service is temporarily unavailable.",
            "ollama",
        );
        assert!(!is_context_overflow(&message, Some(200_000)));
    }

    #[test]
    fn does_not_treat_generic_rate_limit_errors_as_overflow() {
        let message = create_error_message(
            "Rate limit exceeded, please retry after 30 seconds.",
            "ollama",
        );
        assert!(!is_context_overflow(&message, Some(200_000)));
    }

    #[test]
    fn does_not_treat_http_429_style_errors_as_overflow() {
        let message = create_error_message("Too many requests. Please slow down.", "ollama");
        assert!(!is_context_overflow(&message, Some(200_000)));
    }

    #[test]
    fn detects_xiaomi_style_overflow() {
        let message = create_length_stop_message(58, 1_048_512, 0, 0);
        assert!(is_context_overflow(&message, Some(1_048_576)));
    }

    #[test]
    fn treats_a_length_stop_below_the_desired_output_limit_as_recoverable() {
        let message = create_length_stop_message(3, 253_584, 16, 25_554);
        assert!(is_recoverable_length(&message, 128_000));
    }

    #[test]
    fn does_not_recover_a_length_stop_that_reached_the_desired_output_limit() {
        let message = create_length_stop_message(4062, 0, 1024, 0);
        assert!(!is_recoverable_length(&message, 1024));
    }

    #[test]
    fn treats_zero_output_length_stops_as_recoverable_without_context_metadata() {
        let message = create_length_stop_message(100, 0, 0, 0);
        assert!(is_recoverable_length(&message, 128_000));
    }

    #[test]
    fn does_not_treat_normal_length_stops_with_output_as_context_overflow() {
        let message = create_length_stop_message(1000, 0, 4096, 0);
        assert!(!is_context_overflow(&message, Some(200_000)));
    }

    #[test]
    fn does_not_treat_zero_output_length_stops_far_below_context_as_context_overflow() {
        let message = create_length_stop_message(100, 0, 0, 0);
        assert!(!is_context_overflow(&message, Some(200_000)));
    }
}
