//! How a reader bills a replayed signed thinking block as input, by the
//! catalog's `thinking-replay-tokens` rules: a model line's lineage rule
//! (`rules/classes/*.kdl`) applies on every host; readers without one are
//! charged the counted tokens of the signature.

use super::ModelRef;
use super::cascade::{Selector, Target, resolve_axis};

/// What a replayed thinking block costs the reader.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ThinkingReplayTokens {
    /// The reasoning the signature carries, at the size its turn billed as
    /// output; the signature's own bytes are free.
    Output,
    /// The signature's bytes stand in for that reasoning.
    Signature,
}

/// The `thinking-replay-tokens` rules at reference commit c28b3e3.
static RULES: &[(Selector, ThinkingReplayTokens)] = &[
    // classes/anthropic.kdl:26 — every Claude line, on every host.
    (
        Selector {
            class: Some("anthropic"),
            ..Selector::ANY
        },
        ThinkingReplayTokens::Output,
    ),
];

/// How `model` bills replayed thinking: `Signature` unless its lineage
/// declares otherwise.
#[must_use]
pub fn resolve_thinking_replay_tokens(model: ModelRef<'_>) -> ThinkingReplayTokens {
    resolve_axis(RULES, &Target::new(model))
        .copied()
        .unwrap_or(ThinkingReplayTokens::Signature)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn replay(provider: &str, id: &str, api: &str) -> ThinkingReplayTokens {
        resolve_thinking_replay_tokens(ModelRef { id, provider, api })
    }

    #[test]
    fn claude_bills_replayed_thinking_as_output_on_every_host() {
        for (provider, id, api) in [
            ("anthropic", "claude-opus-5", "anthropic-messages"),
            (
                "amazon-bedrock",
                "us.anthropic.claude-sonnet-4-6",
                "bedrock-converse-stream",
            ),
            ("google-vertex", "claude-fable-5@20250929", "google-vertex"),
            (
                "openrouter",
                "anthropic/claude-haiku-4.5",
                "openai-completions",
            ),
            ("", "claude-3-5-sonnet-20241022", ""),
        ] {
            assert_eq!(
                replay(provider, id, api),
                ThinkingReplayTokens::Output,
                "{provider}/{id}"
            );
        }
    }

    #[test]
    fn other_readers_bill_the_signature() {
        for (provider, id, api) in [
            ("openai", "gpt-5.5", "openai-responses"),
            ("google", "gemini-3.5-flash", "google-generative-ai"),
            ("deepseek", "deepseek-v4-pro", "openai-completions"),
            ("", "", "anthropic-messages"),
        ] {
            assert_eq!(
                replay(provider, id, api),
                ThinkingReplayTokens::Signature,
                "{provider}/{id}"
            );
        }
    }
}
