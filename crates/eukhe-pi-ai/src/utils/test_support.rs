//! Test fixtures shared by the utility tests (the TS tests build the same
//! shapes with `fauxAssistantMessage`).

use eukhe_types::pi_ai::{AssistantContentBlock, AssistantMessage, StopReason, TextContent, Usage};

/// TS `fauxAssistantMessage(content, { stopReason, errorMessage })`.
pub(crate) fn faux_assistant_message(
    content: Vec<AssistantContentBlock>,
    stop_reason: StopReason,
    error_message: Option<&str>,
) -> AssistantMessage {
    AssistantMessage {
        content,
        api: "faux".into(),
        provider: "faux".into(),
        model: "faux-1".into(),
        response_model: None,
        response_id: None,
        provider_thinking_level: None,
        thinking_level: None,
        diagnostics: None,
        usage: Usage::default(),
        stop_reason,
        deferred: None,
        error_message: error_message.map(str::to_owned),
        raw_stop_reason: None,
        end_turn: None,
        timestamp: 0,
    }
}

/// TS `fauxAssistantMessage(text)`.
pub(crate) fn faux_text_message(text: &str) -> AssistantMessage {
    faux_assistant_message(
        vec![AssistantContentBlock::Text(TextContent::new(text))],
        StopReason::Stop,
        None,
    )
}

/// TS `fauxAssistantMessage("", { stopReason, errorMessage })`.
pub(crate) fn faux_stop_message(
    stop_reason: StopReason,
    error_message: Option<&str>,
) -> AssistantMessage {
    faux_assistant_message(
        vec![AssistantContentBlock::Text(TextContent::new(""))],
        stop_reason,
        error_message,
    )
}
