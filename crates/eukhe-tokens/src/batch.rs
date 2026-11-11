//! Batch token counting via the embedded utok universal tokenizer: one
//! encoding, many texts, one count per text.
//!
//! Encodings (see [`Encoding`]):
//!
//!   - `O200kBase` — GPT-4o / o1 / GPT-5 (the modern `OpenAI` default).
//!   - `Cl100kBase` — GPT-3.5 / GPT-4 / older models.
//!   - `ClaudeV3` / `ClaudeV47` / `ClaudeV5` / `ClaudeV5Sonnet` — offline
//!     reconstructions of Anthropic's `count_tokens`: v3 serves Claude 3
//!     through Opus 4.6, v4.7 serves Opus 4.7–4.9, v5 the 5-series.
//!   - `Qwen3` — Qwen 3.5 / 3.6 / 3.8 (248k vocabulary, NFC input).
//!   - `DeepSeekV3` — `DeepSeek` V3 through V4 (identical base BPE).
//!   - `KimiK2` — Kimi K2 through K3.
//!   - `Glm5` — GLM-5.x exact; GLM-4.x near-exact (ID-preserving subset).
//!   - `Jev` — `TypeSafe` Jev 1.13 `state` input tokens (measured
//!     reconstruction, request frame excluded).
//!
//! All vocabularies are zstd-embedded in the binary and decoded once on
//! first use. Counts measure content, not wire-protocol framing: BPE
//! encodings use ordinary encoding without special-token handling, and the
//! Claude counts exclude the fixed per-message frame.

use rayon::prelude::*;

use crate::utok::Encoding;

/// Scheduling a Rayon job costs more than tokenizing a small prompt batch,
/// so smaller batches count on the calling thread; large batches amortize
/// the pool handoff across enough independent strings.
const PARALLEL_BATCH_MIN: usize = 16;

/// Total tokens of `texts` under `encoding`: the sum of each fragment's
/// independent [`Encoding::count`] (fragments are never joined, so no
/// merge crosses a fragment boundary).
///
/// Batches of at least 16 fragments count in parallel on the global Rayon
/// pool; smaller batches count serially.
#[must_use]
pub fn count_batch(encoding: Encoding, texts: &[&str]) -> u64 {
    if texts.len() >= PARALLEL_BATCH_MIN {
        texts
            .par_iter()
            .map(|text| u64::from(encoding.count(text)))
            .sum()
    } else {
        texts
            .iter()
            .map(|text| u64::from(encoding.count(text)))
            .sum()
    }
}

#[cfg(test)]
mod tests {
    use super::{PARALLEL_BATCH_MIN, count_batch};
    use crate::utok::Encoding;

    /// Both the serial and the parallel path sum the per-fragment counts.
    #[test]
    fn batch_sums_independent_fragment_counts() {
        let fragments = ["hello world", "fn main() {}", "中文文本", "", "  \n\t"];
        for encoding in [Encoding::O200kBase, Encoding::ClaudeV5Sonnet, Encoding::Jev] {
            let serial: Vec<&str> = fragments.to_vec();
            let parallel: Vec<&str> = fragments
                .iter()
                .copied()
                .cycle()
                .take(PARALLEL_BATCH_MIN * 2)
                .collect();
            for texts in [serial, parallel] {
                let want: u64 = texts.iter().map(|t| u64::from(encoding.count(t))).sum();
                assert_eq!(count_batch(encoding, &texts), want, "{encoding:?}");
            }
        }
    }

    /// Fragments count independently: the sum is not the joined count.
    #[test]
    fn batch_does_not_join_fragments() {
        let texts = ["hel", "lo"];
        assert_eq!(count_batch(Encoding::O200kBase, &texts), 2);
        assert_eq!(Encoding::O200kBase.count("hello"), 1);
    }
}
