//! Which embedded tokenizer a model reads with, by model id and provider.

use std::collections::HashMap;
use std::sync::{LazyLock, Mutex, PoisonError};

use super::revision::revision_at_least as at_least;
use super::taxonomy::{ModelIdentity, bare_of, classify_model};

/// An embedded tokenizer a model's text is billed in.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ModelTokenizer {
    ClaudeV3,
    ClaudeV47,
    ClaudeV5,
    ClaudeV5Sonnet,
    Qwen3,
    DeepSeekV3,
    KimiK2,
    Glm5,
    Cl100k,
    O200k,
}

impl ModelTokenizer {
    const ALL: [Self; 10] = [
        Self::ClaudeV3,
        Self::ClaudeV47,
        Self::ClaudeV5,
        Self::ClaudeV5Sonnet,
        Self::Qwen3,
        Self::DeepSeekV3,
        Self::KimiK2,
        Self::Glm5,
        Self::Cl100k,
        Self::O200k,
    ];

    /// The tokenizer's catalog name (`Model.tokenizer`).
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::ClaudeV3 => "claude-v3",
            Self::ClaudeV47 => "claude-v47",
            Self::ClaudeV5 => "claude-v5",
            Self::ClaudeV5Sonnet => "claude-v5-sonnet",
            Self::Qwen3 => "qwen3",
            Self::DeepSeekV3 => "deepseek-v3",
            Self::KimiK2 => "kimi-k2",
            Self::Glm5 => "glm5",
            Self::Cl100k => "cl100k",
            Self::O200k => "o200k",
        }
    }

    /// The tokenizer whose catalog name is `name`.
    #[must_use]
    pub fn from_name(name: &str) -> Option<Self> {
        Self::ALL
            .into_iter()
            .find(|tokenizer| tokenizer.name() == name)
    }

    /// The embedded encoding this tokenizer counts with.
    #[must_use]
    pub const fn encoding(self) -> crate::Encoding {
        match self {
            Self::ClaudeV3 => crate::Encoding::ClaudeV3,
            Self::ClaudeV47 => crate::Encoding::ClaudeV47,
            Self::ClaudeV5 => crate::Encoding::ClaudeV5,
            Self::ClaudeV5Sonnet => crate::Encoding::ClaudeV5Sonnet,
            Self::Qwen3 => crate::Encoding::Qwen3,
            Self::DeepSeekV3 => crate::Encoding::DeepSeekV3,
            Self::KimiK2 => crate::Encoding::KimiK2,
            Self::Glm5 => crate::Encoding::Glm5,
            Self::Cl100k => crate::Encoding::Cl100kBase,
            Self::O200k => crate::Encoding::O200kBase,
        }
    }
}

fn claude_tokenizer(identity: &ModelIdentity) -> Option<ModelTokenizer> {
    if identity.class != "anthropic" {
        return None;
    }
    let revision = identity.revision;
    Some(match identity.family {
        Some("opus") if at_least(revision, "5") => ModelTokenizer::ClaudeV5,
        Some("opus") if at_least(revision, "4.7") => ModelTokenizer::ClaudeV47,
        Some("sonnet" | "fable" | "mythos") if at_least(revision, "5") => {
            ModelTokenizer::ClaudeV5Sonnet
        }
        // Haiku 5.5 moved to the post-4.7 tokenizer (~30% more tokens than
        // Haiku 4.5). No Haiku-measured vocabulary is embedded; Sonnet 5's
        // is the nearest.
        Some("haiku") if at_least(revision, "5.5") => ModelTokenizer::ClaudeV5Sonnet,
        _ => ModelTokenizer::ClaudeV3,
    })
}

/// GPT-5 and later bill text in `o200k_base`, GPT-3.5 and GPT-4 (Turbo) in
/// `cl100k_base`. GPT-4.1, GPT-4.5, gpt-4o and the o-series are `o200k`
/// too, which is the default for a model without a tokenizer.
fn openai_tokenizer(identity: &ModelIdentity) -> Option<ModelTokenizer> {
    if identity.class != "openai" {
        return None;
    }
    let revision = identity.revision;
    if at_least(revision, "5") {
        return Some(ModelTokenizer::O200k);
    }
    (identity.family == Some("gpt") && at_least(revision, "3.5") && !at_least(revision, "4.1"))
        .then_some(ModelTokenizer::Cl100k)
}

fn resolve_uncached(model_id: &str, provider: &str) -> Option<ModelTokenizer> {
    // Provider-scoped identity overrides (e.g. Yolo-Auto's `yolo` alias for
    // Qwen3.8 Flash) only apply when the provider is known; bare ids stay
    // provider-agnostic so unrelated namespaces never inherit them.
    let identity = classify_model(provider, bare_of(model_id));
    let revision = identity.revision;
    claude_tokenizer(&identity)
        .or_else(|| {
            (identity.class == "qwen" && at_least(revision, "3.5")).then_some(ModelTokenizer::Qwen3)
        })
        .or_else(|| (identity.class == "deepseek").then_some(ModelTokenizer::DeepSeekV3))
        .or_else(|| (identity.class == "kimi").then_some(ModelTokenizer::KimiK2))
        .or_else(|| {
            (identity.class == "glm" && at_least(revision, "5")).then_some(ModelTokenizer::Glm5)
        })
        .or_else(|| openai_tokenizer(&identity))
}

// Resolution is pure and catalog ids recur across providers and aliases.
const MAX_TOKENIZER_CACHE_ENTRIES: usize = 2048;

static CACHE: LazyLock<Mutex<HashMap<String, Option<ModelTokenizer>>>> =
    LazyLock::new(|| Mutex::new(HashMap::with_capacity(MAX_TOKENIZER_CACHE_ENTRIES)));

/// The exact locally embedded tokenizer for a model id on `provider` (`""`
/// when unknown); `None` means the model has no embedded tokenizer and
/// counts in `o200k_base`. Catalog policy, memoized per `(provider, id)` in
/// a cache cleared whenever it reaches 2,048 entries.
#[must_use]
pub fn resolve_model_tokenizer(model_id: &str, provider: &str) -> Option<ModelTokenizer> {
    let key = format!("{provider}\0{model_id}");
    if let Some(&cached) = CACHE
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .get(&key)
    {
        return cached;
    }
    let tokenizer = resolve_uncached(model_id, provider);
    let mut cache = CACHE.lock().unwrap_or_else(PoisonError::into_inner);
    if cache.len() == MAX_TOKENIZER_CACHE_ENTRIES {
        cache.clear();
    }
    cache.insert(key, tokenizer);
    tokenizer
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tok(model_id: &str, provider: &str) -> Option<&'static str> {
        resolve_model_tokenizer(model_id, provider).map(ModelTokenizer::name)
    }

    // Model-to-tokenizer routing cases.
    #[test]
    fn routes_only_tokenizer_generations_covered_by_embedded_vocabularies() {
        assert_eq!(tok("anthropic/claude-opus-4-7", ""), Some("claude-v47"));
        assert_eq!(tok("claude-sonnet-5", ""), Some("claude-v5-sonnet"));
        assert_eq!(tok("Qwen/Qwen3.8-27B", ""), Some("qwen3"));
        assert_eq!(tok("qwen3-32b", ""), None);
        assert_eq!(tok("deepseek-chat", ""), Some("deepseek-v3"));
        assert_eq!(tok("deepseek-r1-0528", ""), Some("deepseek-v3"));
        assert_eq!(tok("deepseek-r1-distill-qwen-32b", ""), None);
        assert_eq!(tok("moonshotai/Kimi-K3", ""), Some("kimi-k2"));
        assert_eq!(tok("moonshot-v1-128k", ""), None);
        assert_eq!(tok("glm-5.2", ""), Some("glm5"));
        assert_eq!(tok("glm-4.7", ""), None);
        assert_eq!(tok("gpt-6.1-sol", "openai-codex"), Some("o200k"));
        assert_eq!(tok("gpt-5.1-codex-max", ""), Some("o200k"));
        assert_eq!(tok("openai/gpt-5.5", "openrouter"), Some("o200k"));
        assert_eq!(tok("gpt-4-turbo", ""), Some("cl100k"));
        assert_eq!(tok("gpt-4-0613", ""), Some("cl100k"));
        assert_eq!(tok("gpt-3.5-turbo", ""), Some("cl100k"));
        assert_eq!(tok("gpt-4.1", ""), None);
        assert_eq!(tok("gpt-4o", ""), None);
        assert_eq!(tok("gpt-realtime-2.1", ""), None);
        assert_eq!(tok("openai/gpt-oss-120b", ""), None);
        assert_eq!(tok("yolo", ""), None);
        assert_eq!(tok("yolo-auto/yolo", "yolo-auto"), Some("qwen3"));
    }

    #[test]
    fn splits_claude_generations() {
        assert_eq!(tok("claude-opus-5", ""), Some("claude-v5"));
        assert_eq!(tok("claude-opus-4-6", ""), Some("claude-v3"));
        assert_eq!(tok("claude-haiku-4-5", ""), Some("claude-v3"));
        assert_eq!(tok("claude-haiku-5-5", ""), Some("claude-v5-sonnet"));
        assert_eq!(tok("claude-haiku-5", ""), Some("claude-v3"));
        assert_eq!(tok("claude-fable-5-1", ""), Some("claude-v5-sonnet"));
        assert_eq!(tok("claude-mythos-preview", ""), Some("claude-v3"));
        assert_eq!(
            tok("us.anthropic.claude-opus-4-7-v1:0", "amazon-bedrock"),
            Some("claude-v47")
        );
        assert_eq!(
            tok("claude-sonnet-5@20260101", "google-vertex"),
            Some("claude-v5-sonnet")
        );
    }

    #[test]
    fn cached_resolution_matches_and_names_round_trip() {
        for _ in 0..2 {
            assert_eq!(tok("glm-5.2", "zai"), Some("glm5"));
        }
        for tokenizer in ModelTokenizer::ALL {
            assert_eq!(ModelTokenizer::from_name(tokenizer.name()), Some(tokenizer));
        }
        assert_eq!(ModelTokenizer::from_name("o200k_base"), None);
    }
}
