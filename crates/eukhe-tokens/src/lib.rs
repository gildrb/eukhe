//! Token counts with the models' real tokenizers. Every token count eukhe
//! shows or decides on comes from here; none is a characters-per-token
//! guess.
//!
//! - Tokenizers: exact offline counts for the `OpenAI`, Claude, Qwen,
//!   `DeepSeek`, Kimi, GLM and Jev families (port of omp's `utok`), the
//!   vocabularies zstd-embedded and decoded on first use.
//! - Policy: which tokenizer a model reads with (omp's catalog
//!   `resolveModelTokenizer`; unknown models count in `o200k_base`), how it
//!   prices an image and a replayed thinking block.
//! - Counting: messages and transcripts under one model's tokenizer (omp's
//!   `Tokenizer`), with the provider-reported usage where a turn has one.

mod batch;
mod counter;
mod policy;
mod utok;

pub use batch::count_batch;
pub use counter::{
    AssistantTurn, MessageParts, Part, TokenBudgetCheck, Tokenizer, ai_assistant, ai_blocks,
};
pub use policy::{
    AutoLevel, ImageDetail, ImageSize, ImageTokenization, ModelRef, ModelTokenizer, PatchSizing,
    ThinkingReplayTokens, base64_image_size, billed_image_tokens, image_tokens,
    resolve_image_tokenization, resolve_model_tokenizer, resolve_thinking_replay_tokens,
};
pub use utok::Encoding;
