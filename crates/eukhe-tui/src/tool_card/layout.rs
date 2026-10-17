//! Shared tool-card rows: element shapes more than one card lays out.

use super::{image_rows, ToolResultView};
use crate::element::{Element, Fit, Inline};
use crate::theme::{Theme, ThemeColor};

/// Each line of `text` word-wrapped, in one theme role.
pub(super) fn wrapped_text(text: &str, role: ThemeColor) -> impl Iterator<Item = Element> + '_ {
    text.split('\n')
        .map(move |line| Element::text(Fit::Wrap, vec![Inline::role(line, role)]))
}

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
