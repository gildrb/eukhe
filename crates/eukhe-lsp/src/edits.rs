//! Applying a workspace edit's text edits to a file's text.

use eukhe_types::lsp::{LspPoint, LspTextEdit};

/// Why edits do not apply to a text.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum EditError {
    #[error("edit position {line}:{column} is outside the text")]
    OutOfRange { line: u32, column: u32 },
    #[error("edits overlap at {line}:{column}")]
    Overlap { line: u32, column: u32 },
}

/// `text` with `edits` applied (LSP semantics: every span addresses the
/// original text; edits must not overlap; inserts at one point keep their
/// order).
///
/// # Errors
///
/// A span is outside `text`, or two edits overlap.
pub fn apply_text_edits(text: &str, edits: &[LspTextEdit]) -> Result<String, EditError> {
    let mut resolved = edits
        .iter()
        .enumerate()
        .map(|(order, edit)| {
            let start = byte_offset(text, edit.span.start)?;
            let end = byte_offset(text, edit.span.end)?;
            Ok((
                start,
                end.max(start),
                order,
                edit.new_text.as_str(),
                edit.span.start,
            ))
        })
        .collect::<Result<Vec<_>, EditError>>()?;
    resolved.sort_by_key(|(start, end, order, _, _)| (*start, *end, *order));
    for pair in resolved.windows(2) {
        if let [(_, previous_end, _, _, _), (start, _, _, _, point)] = pair {
            if start < previous_end {
                return Err(EditError::Overlap {
                    line: point.line,
                    column: point.column,
                });
            }
        }
    }
    let mut output = String::with_capacity(text.len());
    let mut cursor = 0;
    for (start, end, _, new_text, _) in resolved {
        output.push_str(&text[cursor..start]);
        output.push_str(new_text);
        cursor = end;
    }
    output.push_str(&text[cursor..]);
    Ok(output)
}

/// The byte offset of a 1-based point; a column past the line's end
/// clamps to the end of the line (before its terminator).
fn byte_offset(text: &str, point: LspPoint) -> Result<usize, EditError> {
    let out_of_range = EditError::OutOfRange {
        line: point.line,
        column: point.column,
    };
    let line_index = point
        .line
        .checked_sub(1)
        .ok_or_else(|| out_of_range.clone())? as usize;
    let column_index = point
        .column
        .checked_sub(1)
        .ok_or_else(|| out_of_range.clone())? as usize;
    let mut line_start = 0;
    for _ in 0..line_index {
        let newline = text[line_start..]
            .find('\n')
            .ok_or_else(|| out_of_range.clone())?;
        line_start += newline + 1;
    }
    let rest = &text[line_start..];
    let line_end = rest.find('\n').map_or(rest.len(), |end| {
        if rest[..end].ends_with('\r') {
            end - 1
        } else {
            end
        }
    });
    let line = &rest[..line_end];
    let within = line
        .char_indices()
        .nth(column_index)
        .map_or(line.len(), |(offset, _)| offset);
    Ok(line_start + within)
}

#[cfg(test)]
mod tests {
    use eukhe_types::lsp::LspSpan;

    use super::*;

    fn edit(start: (u32, u32), end: (u32, u32), new_text: &str) -> LspTextEdit {
        LspTextEdit {
            span: LspSpan {
                start: LspPoint {
                    line: start.0,
                    column: start.1,
                },
                end: LspPoint {
                    line: end.0,
                    column: end.1,
                },
            },
            new_text: new_text.to_owned(),
        }
    }

    #[test]
    fn edits_apply_against_the_original_text() {
        let text = "fn é() {\r\n    é();\r\n}\n";
        let edits = [
            edit((2, 5), (2, 6), "bar"),
            edit((1, 4), (1, 5), "bar"),
            edit((3, 2), (3, 2), " // end"),
        ];
        assert_eq!(
            apply_text_edits(text, &edits),
            Ok("fn bar() {\r\n    bar();\r\n} // end\n".to_owned())
        );
        assert_eq!(
            apply_text_edits(
                text,
                &[edit((1, 1), (1, 5), "x"), edit((1, 3), (1, 6), "y")]
            ),
            Err(EditError::Overlap { line: 1, column: 3 })
        );
        assert_eq!(
            apply_text_edits(text, &[edit((9, 1), (9, 1), "x")]),
            Err(EditError::OutOfRange { line: 9, column: 1 })
        );
    }
}
