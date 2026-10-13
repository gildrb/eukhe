//! Block ops (`PUT N*:`, `PUT <N*:`, `PUT >N*:`, `CUT N*`, register forms).
//!
//! omp resolves `N*` to the syntactic block opening on line N with
//! tree-sitter. eukhe has no block resolver, so every block op is rejected
//! with omp's no-resolver message (`BLOCK_RESOLVER_UNAVAILABLE`) instead of
//! being guessed at.

use super::{messages::BLOCK_RESOLVER_UNAVAILABLE, types::Edit};
use crate::error::EditError;

/// Reject an edit stream that contains a block locator.
pub(crate) fn reject_block_edits(edits: &[Edit]) -> Result<(), EditError> {
    let first_block = edits.iter().find_map(|edit| match edit {
        Edit::Block { line_num, .. } => Some(*line_num),
        Edit::Insert { .. } | Edit::Delete { .. } | Edit::Cut { .. } | Edit::Paste { .. } => None,
    });
    match first_block {
        Some(line_num) => Err(EditError::apply(format!(
            "line {line_num}: {BLOCK_RESOLVER_UNAVAILABLE}"
        ))),
        None => Ok(()),
    }
}
