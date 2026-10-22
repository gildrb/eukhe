//! Shared tool-card rows: element shapes more than one card lays out.

use super::{image_rows, ToolResultView};
use crate::element::Element;
use crate::theme::Theme;

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
