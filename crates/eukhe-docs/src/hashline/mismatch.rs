//! Snapshot-tag mismatch diagnostics (omp `modes/hashline/mismatch.rs`).

use super::messages::{format_anchored_context, tag_source_hint};
use crate::error::EditError;

/// Context needed to explain a stale or unrecognized snapshot tag.
pub(crate) struct MismatchDetails {
    pub(crate) path: String,
    pub(crate) expected_file_hash: String,
    pub(crate) actual_file_hash: String,
    pub(crate) file_lines: Vec<String>,
    pub(crate) anchor_lines: Vec<u32>,
    /// The tag names a snapshot this worker holds for the path.
    pub(crate) hash_recognized: bool,
}

/// The model-facing stale or unknown snapshot tag rejection. It names the
/// live text's header: the caller records that snapshot with the printed
/// context lines seen, so a retry on those lines works without a read.
pub(crate) fn mismatch_error(details: &MismatchDetails) -> EditError {
    let path = &details.path;
    let tag = &details.expected_file_hash;
    let first = if details.hash_recognized {
        format!("Edit rejected for {path}: file changed between read and edit (#{tag} is stale).")
    } else {
        format!(
            "Edit rejected for {path}: #{tag} is not a tag this session holds for this file (an \
             invented tag, or an old read, e.g. from before a restart)."
        )
    };
    let mut lines = vec![
        first,
        format!(
            "The current header is [{path}#{}]: copy it verbatim to edit the lines shown below; \
             for other lines, {}",
            details.actual_file_hash,
            tag_source_hint(path)
        ),
    ];
    let context = format_anchored_context(&details.anchor_lines, &details.file_lines);
    if !context.is_empty() {
        lines.push(String::new());
        lines.extend(context);
    }
    EditError::matched(lines.join("\n"))
}
