//! Harness digest delivery on the durable Harness: compose the
//! continual-harness state into the model-facing `[harness-digest]` digest
//! and deliver it at cold context boundaries (first request, resume,
//! compaction head). Only the newest digest reaches the model — a fresh
//! delivery supersedes the older in-context copies with context edits —
//! while persisted transcripts keep every copy (the newest remains
//! authoritative), exactly as the legacy import admits old digests
//! ([`super::import`]). Port of `session_engine::harness_digest` over
//! [`crate::refinement`] state.

mod deliver;
mod render;
#[cfg(test)]
mod tests;

// Consumed by the compaction summary path (`eukhe-core/src/durable/compaction`),
// which lands in this wave; the digest module is private to `durable`, so
// the re-exports read as unused until then.
#[allow(
    unused_imports,
    reason = "consumed by durable/compaction (same wave); private module re-exports"
)]
pub use render::{
    conversation_digest, digest_context, digest_from_frame, digest_query_terms,
    harness_digest_message_text, recent_texts_newest_first, render_digest_with_fingerprint,
    HarnessDigestContext, HarnessDigestRender, HARNESS_DIGEST_CUSTOM_TYPE, HARNESS_DIGEST_PREFIX,
    HARNESS_DIGEST_SUFFIX,
};

pub(crate) use deliver::extension;
