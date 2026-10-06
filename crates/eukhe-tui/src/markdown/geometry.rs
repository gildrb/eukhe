//! The span-wrapping row sink and the block-spacing rule shared by the
//! Markdown renderer.
use super::{Block, BlockKind};
use crate::style::Style;
use crate::{Line, Span};

pub(super) struct WrapOutput<'a> {
    output: &'a mut Vec<Line>,
    current: Line,
    pub(super) has_content: bool,
}

impl<'a> WrapOutput<'a> {
    pub(super) fn render(output: &'a mut Vec<Line>) -> Self {
        Self {
            output,
            current: Vec::new(),
            has_content: false,
        }
    }

    pub(super) fn push(&mut self, text: &str, style: Style) {
        self.has_content = true;
        self.current.push(Span::styled(text.to_owned(), style));
    }

    pub(super) fn finish_row(&mut self, trim: bool) {
        if trim {
            while self
                .current
                .last()
                .is_some_and(|span| span.content.trim().is_empty())
            {
                self.current.pop();
            }
        }
        self.output.push(std::mem::take(&mut self.current));
        self.has_content = false;
    }
}

pub(super) fn blank_after(next: Option<&Block>, exclude_lists: bool) -> bool {
    match next {
        Some(next) => {
            !(next.sep_blank || exclude_lists && matches!(next.kind, BlockKind::List { .. }))
        }
        None => false,
    }
}
