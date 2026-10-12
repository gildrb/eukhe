//! Block ops (`PUT N*:`, `PUT >N*:`, `CUT N*`, register forms) (omp
//! `modes/hashline/block.rs`).
//!
//! omp resolves `N*` to the syntactic block opening on line N with
//! tree-sitter. eukhe has no grammars yet (tool-surface design, Phase 5), so
//! every block takes omp's unresolved path: after-block inserts and pastes
//! lower to plain `PUT >N` with a warning, and block replace or cut is
//! rejected with the explicit-range form.

use super::{
    apply::STRUCTURAL_CLOSER_RE,
    messages::{
        block_unresolved_message, insert_after_block_closer_lowered_warning,
        insert_after_block_unresolved_lowered_warning, paste_after_block_closer_lowered_warning,
        paste_after_block_unresolved_lowered_warning, AbsoluteRangeOp,
    },
    types::{BlockMode, Cursor, Edit, PasteTarget},
};
use crate::error::EditError;

/// Whether an edit stream contains a deferred block operation.
pub(crate) fn has_block_edit(edits: &[Edit]) -> bool {
    edits.iter().any(|edit| matches!(edit, Edit::Block { .. }))
}

/// Resolve deferred block operations against `text` to ordinary edits.
pub(crate) fn resolve_block_edits(
    edits: &[Edit],
    text: &str,
    on_warning: &mut dyn FnMut(String),
) -> Result<Vec<Edit>, EditError> {
    if !has_block_edit(edits) {
        return Ok(edits.to_vec());
    }
    let lines: Vec<&str> = text.split('\n').collect();
    let mut resolved = Vec::new();
    let mut synth_index = 0;
    for edit in edits {
        let Edit::Block {
            anchor,
            payloads,
            mode,
            register,
            line_num,
            ..
        } = edit
        else {
            resolved.push(edit.clone());
            continue;
        };
        let is_closer = lines
            .get(anchor.line.saturating_sub(1) as usize)
            .is_some_and(|line| STRUCTURAL_CLOSER_RE.is_match(line));
        match mode {
            Some(BlockMode::PasteAfter) => {
                on_warning(if is_closer {
                    paste_after_block_closer_lowered_warning(anchor.line)
                } else {
                    paste_after_block_unresolved_lowered_warning(anchor.line)
                });
                resolved.push(Edit::Paste {
                    at: PasteTarget::Gap {
                        cursor: Cursor::AfterAnchor(*anchor),
                    },
                    register: register.clone(),
                    line_num: *line_num,
                    index: synth_index,
                });
                synth_index += 1;
            }
            Some(BlockMode::InsertAfter) => {
                on_warning(if is_closer {
                    insert_after_block_closer_lowered_warning(anchor.line)
                } else {
                    insert_after_block_unresolved_lowered_warning(anchor.line)
                });
                for payload in payloads {
                    resolved.push(Edit::Insert {
                        cursor: Cursor::AfterAnchor(*anchor),
                        text: payload.clone(),
                        line_num: *line_num,
                        index: synth_index,
                        replacement: false,
                    });
                    synth_index += 1;
                }
            }
            Some(BlockMode::Cut) | None => {
                let op = if *mode == Some(BlockMode::Cut) {
                    AbsoluteRangeOp::Cut
                } else {
                    AbsoluteRangeOp::Replace
                };
                return Err(EditError::apply(format!(
                    "line {line_num}: {}",
                    block_unresolved_message(anchor.line, op, &lines, register.as_deref())
                )));
            }
        }
    }
    Ok(resolved)
}
