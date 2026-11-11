//! Universal offline tokenizer (`utok`).
//!
//! Exact token counting (and, where meaningful, encoding) for six model
//! families, with all vocabulary data zstd-compressed and embedded in the
//! binary. No network, no files, no external tokenizer runtimes.
//!
//! | [`Encoding`] | family | mechanism |
//! |---|---|---|
//! | `O200kBase` | GPT-4o / o1 / GPT-5+ | byte-level BPE (tiktoken ranks) |
//! | `Cl100kBase` | GPT-3.5 / GPT-4 | byte-level BPE |
//! | `ClaudeV3` / `ClaudeV47` / `ClaudeV5` / `ClaudeV5Sonnet` | Claude generations | ctok count reconstruction (count-only) |
//! | `Qwen3` | Qwen 3.5 / 3.6 / 3.8 (248k vocab) | byte-level BPE + NFC |
//! | `DeepSeekV3` | `DeepSeek` V3 … V4 | byte-level BPE, 3-stage split chain |
//! | `KimiK2` | Kimi K2 … K3 | byte-level BPE (tiktoken ranks) |
//! | `Glm5` | GLM-5.x (exact), GLM-4.x (near-exact) | byte-level BPE, `ignore_merges` |
//! | `Jev` | `TypeSafe` Jev 1.13 | measured whole-word vocab + restricted o200k BPE (count-only) |
//!
//! Semantics are `encode_ordinary`: plain content, no special tokens, no
//! chat-template frame. This matches budget checks where fragments are
//! summed.
//!
//! Every vocabulary is decoded once, on the first count or encode of its
//! family, and reused for the life of the process.
//!
//! Internally the input is encoding-generic ([`Utf`]): `&str`/`String`
//! (UTF-8), `&[u16]` (UTF-16) and `&[u32]` (UTF-32) tokenize natively in
//! their own code units — no UTF-8 transcode, no scratch buffer. The
//! pre-tokenizer scans codepoints in place, and rank tables lazily
//! expand per-flavor lookup views (`bpe.rs`). Valid text yields
//! flavor-invariant ids/counts; malformed units decode permissively as
//! U+FFFD (matching a lossy JS crossing). The public API takes `&str`; the
//! UTF-16/UTF-32 flavors stay crate-internal, exercised by the parity tests.

mod bpe;
mod claude;
mod jev;
mod pretoken;
mod scan;
mod tables;
mod ucd;
mod utf;
use self::utf::Utf;

/// A tokenizer family. Copy-cheap; all state is in lazily-initialized
/// process-wide tables (first use pays one zstd decode of ~0.5–1 MB).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Encoding {
    /// GPT-4o / o1 / GPT-5 (`OpenAI` default).
    O200kBase,
    /// GPT-3.5 / GPT-4 / older `OpenAI`.
    Cl100kBase,
    /// Claude 3 through Opus 4.6 (and every non-opus Claude < 5).
    ClaudeV3,
    /// Claude Opus 4.7–4.9.
    ClaudeV47,
    /// Claude Opus 5+.
    ClaudeV5,
    /// Claude Sonnet/Fable 5+ (non-opus 5-series frame variant).
    ClaudeV5Sonnet,
    /// Qwen 3.5 / 3.6 / 3.8 (248,044-token vocabulary, NFC input).
    Qwen3,
    /// `DeepSeek` V3 / V3.1 / V3.2 / R1 / V4 (identical base BPE).
    DeepSeekV3,
    /// Kimi K2 / K2.5 / K3 (163,584-token base vocabulary).
    KimiK2,
    /// GLM-5 (154,820-token vocabulary; ID-preserving superset of GLM-4.x).
    Glm5,
    /// `TypeSafe` Jev 1.13 `state` input tokens (measured reconstruction).
    Jev,
}

impl Encoding {
    /// Exact content token count of `text` (no specials, no message frame).
    #[must_use]
    pub fn count(self, text: &str) -> u32 {
        self.count_in(text)
    }

    /// Token ids for `text`.
    ///
    /// `None` for the Claude families and Jev: both are reconstructed from
    /// counts, not boundaries, so no id sequence exists.
    #[must_use]
    pub fn encode(self, text: &str) -> Option<Vec<u32>> {
        self.encode_in(text)
    }

    /// [`Self::count`] in any UTF flavor.
    pub(crate) fn count_in<T: Utf + ?Sized>(self, text: &T) -> u32 {
        match self {
            Self::ClaudeV3 => claude::content_token_count(text.units(), claude::Family::V3),
            Self::ClaudeV47 => claude::content_token_count(text.units(), claude::Family::V47),
            Self::ClaudeV5 => claude::content_token_count(text.units(), claude::Family::V5),
            Self::ClaudeV5Sonnet => {
                claude::content_token_count(text.units(), claude::Family::V5Sonnet)
            }
            Self::Jev => jev::content_token_count(text.units()),
            Self::O200kBase
            | Self::Cl100kBase
            | Self::Qwen3
            | Self::DeepSeekV3
            | Self::KimiK2
            | Self::Glm5 => tables::bpe_for(self).count(text.units()),
        }
    }

    /// [`Self::encode`] in any UTF flavor.
    pub(crate) fn encode_in<T: Utf + ?Sized>(self, text: &T) -> Option<Vec<u32>> {
        match self {
            Self::ClaudeV3
            | Self::ClaudeV47
            | Self::ClaudeV5
            | Self::ClaudeV5Sonnet
            | Self::Jev => None,
            Self::O200kBase
            | Self::Cl100kBase
            | Self::Qwen3
            | Self::DeepSeekV3
            | Self::KimiK2
            | Self::Glm5 => Some(tables::bpe_for(self).encode(text.units())),
        }
    }
}

#[cfg(test)]
#[allow(
    clippy::cast_possible_truncation,
    reason = "test PRNG output and fixture ids narrow on purpose"
)]
#[path = "tests"]
mod tests {
    #[path = "claude.rs"]
    mod claude;
    #[path = "deepseek.rs"]
    mod deepseek;
    #[path = "glm.rs"]
    mod glm;
    #[path = "jev.rs"]
    mod jev;
    #[path = "kimi.rs"]
    mod kimi;
    #[path = "openai.rs"]
    mod openai;
    #[path = "qwen.rs"]
    mod qwen;
    #[path = "rank_table.rs"]
    mod rank_table;
    #[path = "throughput.rs"]
    mod throughput;
}
