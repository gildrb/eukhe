//! Clipboard registers: `CUT … [@name]` captures, register `PUT`s paste
//! (omp `modes/hashline/clipboard.rs`).

use super::{
    messages::{
        ambiguous_anonymous_paste_message, empty_register_paste_warning,
        empty_register_span_paste_message, EMPTY_PASTE,
    },
    types::{Anchor, BlockMode, Cursor, Edit, ParsedRange, PasteTarget},
};
use crate::{error::EditError, store::Clipboard};

fn describe_cut(range: ParsedRange, register: Option<&str>) -> String {
    let span = if range.start.line == range.end.line {
        range.start.line.to_string()
    } else {
        format!("{}.={}", range.start.line, range.end.line)
    };
    register.map_or_else(
        || format!("CUT {span}"),
        |register| format!("CUT {span} @{register}"),
    )
}

/// Whether an edit stream reads or writes a clipboard register.
pub(crate) fn has_clipboard_edit(edits: &[Edit]) -> bool {
    edits.iter().any(|edit| match edit {
        Edit::Cut { .. } | Edit::Paste { .. } => true,
        Edit::Block { mode, register, .. } => {
            matches!(mode, Some(BlockMode::Cut | BlockMode::PasteAfter)) || register.is_some()
        }
        Edit::Insert { .. } | Edit::Delete { .. } => false,
    })
}

fn known_registers(clipboard: &Clipboard) -> Vec<&str> {
    let mut known: Vec<_> = clipboard
        .named
        .as_ref()
        .into_iter()
        .flat_map(|registers| registers.keys().map(String::as_str))
        .collect();
    known.sort_unstable();
    known
}

/// The lines a paste reads. A named gap paste of an empty register pastes
/// nothing and warns; a named span paste of one, or an anonymous paste with
/// no single pending cut, is rejected.
fn read_register(
    register: Option<&str>,
    target: PasteTarget,
    clipboard: &mut Clipboard,
    line_num: u32,
    on_warning: &mut dyn FnMut(String),
) -> Result<Vec<String>, EditError> {
    if let Some(register) = register {
        if let Some(lines) = clipboard
            .named
            .as_ref()
            .and_then(|named| named.get(register))
        {
            return Ok(lines.clone());
        }
        let known = known_registers(clipboard);
        return match target {
            PasteTarget::Span { .. } => Err(EditError::apply(format!(
                "line {line_num}: {}",
                empty_register_span_paste_message(register, &known)
            ))),
            PasteTarget::Gap { .. } => {
                on_warning(format!(
                    "line {line_num}: {}",
                    empty_register_paste_warning(register, &known)
                ));
                Ok(Vec::new())
            }
        };
    }

    let pending = clipboard.pending_anon_cuts.as_deref().unwrap_or_default();
    if pending.len() > 1 {
        let pending: Vec<_> = pending.iter().map(String::as_str).collect();
        return Err(EditError::apply(format!(
            "line {line_num}: {}",
            ambiguous_anonymous_paste_message(&pending)
        )));
    }
    let Some(lines) = clipboard.lines.clone() else {
        return Err(EditError::apply(format!("line {line_num}: {EMPTY_PASTE}")));
    };
    clipboard.pending_anon_cuts = Some(Vec::new());
    Ok(lines)
}

fn write_register(
    range: ParsedRange,
    register: Option<&str>,
    line_num: u32,
    file_lines: &[String],
    clipboard: &mut Clipboard,
) -> Result<(), EditError> {
    if range.start.line == 0 || range.end.line as usize > file_lines.len() {
        return Err(EditError::apply(format!(
            "line {line_num}: `{}` is out of range (file has {} lines).",
            describe_cut(range, register),
            file_lines.len()
        )));
    }
    let captured = file_lines[(range.start.line - 1) as usize..range.end.line as usize].to_vec();
    if let Some(register) = register {
        clipboard
            .named
            .get_or_insert_with(Default::default)
            .insert(register.to_owned(), captured);
    } else {
        clipboard.lines = Some(captured);
        clipboard
            .pending_anon_cuts
            .get_or_insert_with(Vec::new)
            .push(describe_cut(range, register));
    }
    Ok(())
}

/// Lower cut/paste operations into inserts and deletes against the original
/// file lines.
pub(crate) fn resolve_clipboard_edits(
    edits: &[Edit],
    file_lines: &[String],
    clipboard: &mut Clipboard,
    on_warning: &mut dyn FnMut(String),
) -> Result<Vec<Edit>, EditError> {
    if !has_clipboard_edit(edits) {
        return Ok(edits.to_vec());
    }
    let mut resolved = Vec::new();
    let mut synth_index = 0;
    for edit in edits {
        match edit {
            Edit::Cut {
                range,
                register,
                line_num,
                ..
            } => write_register(
                *range,
                register.as_deref(),
                *line_num,
                file_lines,
                clipboard,
            )?,
            Edit::Paste {
                at,
                register,
                line_num,
                ..
            } => {
                let lines =
                    read_register(register.as_deref(), *at, clipboard, *line_num, on_warning)?;
                match at {
                    PasteTarget::Gap { cursor } => {
                        for text in lines {
                            resolved.push(Edit::Insert {
                                cursor: *cursor,
                                text,
                                line_num: *line_num,
                                index: synth_index,
                                replacement: false,
                            });
                            synth_index += 1;
                        }
                    }
                    PasteTarget::Span { range } => {
                        if range.start.line == 0 || range.end.line as usize > file_lines.len() {
                            let register = register
                                .as_ref()
                                .map_or_else(String::new, |value| format!(" @{value}"));
                            return Err(EditError::apply(format!(
                                "line {line_num}: `PUT {}.={}{}` is out of range (file has {} lines).",
                                range.start.line,
                                range.end.line,
                                register,
                                file_lines.len()
                            )));
                        }
                        let cursor = Cursor::BeforeAnchor(Anchor {
                            line: range.start.line,
                        });
                        for text in lines {
                            resolved.push(Edit::Insert {
                                cursor,
                                text,
                                line_num: *line_num,
                                index: synth_index,
                                replacement: true,
                            });
                            synth_index += 1;
                        }
                        for line in range.start.line..=range.end.line {
                            resolved.push(Edit::Delete {
                                anchor: Anchor { line },
                                line_num: *line_num,
                                index: synth_index,
                            });
                            synth_index += 1;
                        }
                    }
                }
            }
            Edit::Insert { .. } | Edit::Delete { .. } | Edit::Block { .. } => {
                resolved.push(edit.clone());
            }
        }
    }
    Ok(resolved)
}

/// Validate anonymous clipboard sequencing without mutating the supplied
/// clipboard.
pub(crate) fn validate_clipboard_sequence(
    edits: &[Edit],
    clipboard: &Clipboard,
) -> Result<(), EditError> {
    let mut fork = clipboard.fork();
    for edit in edits {
        match edit {
            Edit::Cut {
                range, register, ..
            } => {
                if let Some(register) = register {
                    fork.named
                        .get_or_insert_with(Default::default)
                        .insert(register.clone(), Vec::new());
                } else {
                    fork.lines = Some(Vec::new());
                    fork.pending_anon_cuts
                        .get_or_insert_with(Vec::new)
                        .push(describe_cut(*range, None));
                }
            }
            Edit::Paste {
                at,
                register,
                line_num,
                ..
            } => {
                read_register(register.as_deref(), *at, &mut fork, *line_num, &mut |_| {})?;
            }
            Edit::Insert { .. } | Edit::Delete { .. } | Edit::Block { .. } => {}
        }
    }
    Ok(())
}
