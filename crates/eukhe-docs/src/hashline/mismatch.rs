//! Snapshot-tag mismatch diagnostics (omp `modes/hashline/mismatch.rs`).

use super::messages::format_anchored_context;
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

/// The model-facing stale or unknown snapshot tag rejection.
pub(crate) fn mismatch_error(details: &MismatchDetails) -> EditError {
    let path = format!(" for {}", details.path);
    let mut lines = if details.hash_recognized {
        vec![
            format!("Edit rejected{path}: file changed between read and edit."),
            format!(
                "Section is bound to #{}, but the current file hashes to #{}. If a prior edit in this \
                 session modified this file, copy the [path#newhash] header from that edit's \
                 response; otherwise re-read the file with `read` to refresh the tag before retrying.",
                details.expected_file_hash, details.actual_file_hash
            ),
        ]
    } else {
        vec![
            format!(
                "Edit rejected{path}: tag #{} is not among the versions of this file that this \
                 worker holds (an older read, or one from before a restart).",
                details.expected_file_hash
            ),
            format!(
                "The current file hashes to #{}. Re-read the file with `read` and use the \
                 [path#tag] header it gives. Do not invent a tag.",
                details.actual_file_hash
            ),
        ]
    };
    let context = format_anchored_context(&details.anchor_lines, &details.file_lines);
    if !context.is_empty() {
        lines.push(String::new());
        lines.extend(context);
    }
    EditError::matched(lines.join("\n"))
}
