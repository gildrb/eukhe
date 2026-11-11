//! Model policy ported from omp's catalog (c28b3e3): which embedded
//! tokenizer a model reads with, how it prices an image, how it bills a
//! replayed thinking block. Every decision starts from the model's identity
//! (`taxonomy`), the class/family/revision omp's compat rules classify a
//! wire id into.

mod cascade;
mod image;
mod image_header;
mod revision;
mod taxonomy;
mod thinking;
mod tokenizer;

pub use image::{
    AutoLevel, ImageDetail, ImageSize, ImageTokenization, PatchSizing, billed_image_tokens,
    image_tokens, resolve_image_tokenization,
};
pub use image_header::base64_image_size;
pub use thinking::{ThinkingReplayTokens, resolve_thinking_replay_tokens};
pub use tokenizer::{ModelTokenizer, resolve_model_tokenizer};

/// A model as the policies read it: its id on its host, and the wire API
/// carrying the request. Empty strings mean unknown.
#[derive(Clone, Copy, Debug)]
pub struct ModelRef<'a> {
    pub id: &'a str,
    pub provider: &'a str,
    pub api: &'a str,
}
