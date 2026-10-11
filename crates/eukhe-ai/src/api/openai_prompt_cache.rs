//! Port of `api/openai-prompt-cache.ts`.

/// Maximum `prompt_cache_key` length in code points.
pub const OPENAI_PROMPT_CACHE_KEY_MAX_LENGTH: usize = 64;

/// Truncate a prompt cache key to [`OPENAI_PROMPT_CACHE_KEY_MAX_LENGTH`]
/// code points (TS `Array.from(key)` counts code points).
#[must_use]
pub fn clamp_openai_prompt_cache_key(key: Option<&str>) -> Option<String> {
    let key = key?;
    Some(
        match key.char_indices().nth(OPENAI_PROMPT_CACHE_KEY_MAX_LENGTH) {
            Some((end, _)) => key[..end].to_owned(),
            None => key.to_owned(),
        },
    )
}
