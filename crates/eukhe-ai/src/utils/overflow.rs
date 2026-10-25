//! Context overflow detection.
//!
//! The rule runs as the compiled core (`eukhe_bend::rules::overflow`,
//! `laws/overflow.bend`): the patterns of the errors providers return when
//! the input exceeds the model's context window (Anthropic, Bedrock,
//! `OpenAI` (and `LiteLLM` / OpenAI-compatible proxies), Google, xAI, Groq,
//! `OpenRouter`, Together AI, GitHub Copilot, llama.cpp, LM Studio,
//! `MiniMax`, Kimi For Coding, Mistral, DS4, z.ai, Ollama, and
//! `DashScope`/Qwen), Cerebras' bodyless 400/413, z.ai's silent overflow
//! (usage above the window) and Xiaomi `MiMo`'s length stop with zero
//! output. This module hands the core the reply's facts.

use eukhe_bend::rules::overflow::{self as rule, Reply, Stop};
use eukhe_types::pi_ai::{AssistantMessage, StopReason};

fn stop(reason: StopReason) -> Stop {
    match reason {
        StopReason::Stop => Stop::Stop,
        StopReason::Length => Stop::Length,
        StopReason::Pending | StopReason::ToolUse | StopReason::Aborted | StopReason::Deferred => {
            Stop::Other
        }
        StopReason::Error => Stop::Error,
    }
}

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
    let error_message = match message.stop_reason {
        StopReason::Error => message.error_message.as_deref().unwrap_or_default(),
        StopReason::Pending
        | StopReason::Stop
        | StopReason::Length
        | StopReason::ToolUse
        | StopReason::Aborted
        | StopReason::Deferred => "",
    };
    rule::is_overflow(&Reply {
        stop: stop(message.stop_reason),
        message: error_message,
        provider: &message.provider,
        window: context_window.unwrap_or(0),
        input: message.usage.input,
        cache_read: message.usage.cache_read,
        output: message.usage.output,
    })
}

/// Whether a length stop ended below the intended output limit
/// (`desired_max_output`, the original limit before context-based clamping):
/// context pressure or provider truncation, worth one compact-and-retry.
#[must_use]
pub fn is_recoverable_length(message: &AssistantMessage, desired_max_output: u64) -> bool {
    rule::is_recoverable_length(
        stop(message.stop_reason),
        desired_max_output,
        message.usage.output,
    )
}
