//! Trusted ID and sequence branding (`ids.ts`).

use crate::errors::StorageError;
use crate::types::{DurableId, Seq, Storage};

/// Apply an ID brand at a trusted numeric allocation or decoding boundary.
#[must_use]
pub fn id_from_number<I: DurableId>(value: u64) -> I {
    I::from_number(value)
}

/// Apply the commit-sequence brand at a trusted storage boundary.
#[must_use]
pub fn seq_from_number(value: u64) -> Seq {
    Seq::from_number(value)
}

/// Mint a fresh ID of kind `I` from the Session-global namespace (TS
/// `storage.mintId<I>()`; the brand is applied here because a generic method
/// would make [`Storage`] not object-safe).
///
/// # Errors
/// The storage failed to allocate.
pub async fn mint<I: DurableId, S: Storage + ?Sized>(storage: &S) -> Result<I, StorageError> {
    storage.mint_id().await.map(I::from_number)
}
