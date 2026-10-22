//! Shared tool-card rows: element shapes more than one card lays out.

use serde_json::Value;

use super::summary::body_row;
use super::{hidden_image_text, image_rows, ToolResultView};
use crate::element::{Element, Inline};
use crate::theme::{Theme, ThemeColor};

/// The image metadata rows below a card (see [`image_rows`]).
pub(super) fn images(
    result: Option<&ToolResultView>,
    show_images: bool,
    theme: &Theme,
) -> impl Iterator<Item = Element> {
    image_rows(result, show_images, theme)
        .into_iter()
        .map(Element::line)
}

/// A result's images under the one-row summary (the default detail,
/// where the output stays folded): images are content, not noise, so a
/// shown image keeps its metadata row and a hidden one its `[Image:
/// mime]` placeholder row (the text the expanded output carries).
pub(super) fn collapsed_images(
    result: Option<&ToolResultView>,
    show_images: bool,
    theme: &Theme,
) -> Vec<Element> {
    if show_images {
        return images(result, show_images, theme).collect();
    }
    result
        .into_iter()
        .flat_map(|result| result.content.iter())
        .filter(|block| block.get("type").and_then(Value::as_str) == Some("image"))
        .map(|block| {
            body_row(
                /* first */ false,
                vec![Inline::role(
                    hidden_image_text(block),
                    ThemeColor::ToolOutput,
                )],
            )
        })
        .collect()
}
