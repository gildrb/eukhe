//! Thinking facts of a model that more than one wire API reads.

use eukhe_types::pi_ai::Model;

use crate::quirks::Quirks;

/// Whether `model` takes adaptive thinking (`thinking.type: adaptive` with
/// an effort), on Anthropic Messages and on Bedrock alike: the model's
/// explicit `compat.forceAdaptiveThinking` (an Anthropic Messages compat
/// block), else the quirks rulebook's `adaptive_thinking`, else false.
#[must_use]
pub fn adaptive_thinking(model: &Model) -> bool {
    model
        .compat
        .as_ref()
        .and_then(|compat| compat.as_anthropic_messages())
        .and_then(|compat| compat.force_adaptive_thinking)
        .or_else(|| Quirks::of(model).adaptive_thinking())
        .unwrap_or(false)
}
