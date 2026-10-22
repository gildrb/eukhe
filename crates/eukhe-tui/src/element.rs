//! Typed elements for tool cards and the one renderer that turns them into
//! rows. A card says what to show: text in a theme role, a status mark, a
//! guttered row, an inset column. Only this renderer picks the status
//! glyphs and colors and the width cuts.

use crate::style::Style;
use crate::theme::{Theme, ThemeColor};
use crate::width::{line_width, str_width, truncate_line, wrap_line};
use crate::{Line, Span};

/// How a run of text is colored.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Ink {
    /// The terminal's own colors.
    Plain,
    /// A theme text role.
    Role(ThemeColor),
    /// A style the content chose itself (syntax colors, nested renderers).
    Content(Style),
}

/// The state of a tool call, as a status mark shows it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Status {
    Queued,
    Running,
    Done,
    Error,
    Aborted,
}

/// The cells a status mark takes: the width of `ok`; the one-cell marks
/// (`x`, the working icon, the queued dot) pad to it, so the names after
/// them line up.
pub(crate) const STATUS_MARK_WIDTH: usize = 2;

/// One piece of a text row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Inline {
    /// Text in one ink.
    Run { text: String, ink: Ink },
    /// A status mark in the status color: the status glyph, the working
    /// icon while running.
    Status { status: Status },
}

impl Inline {
    /// Text in the terminal's own colors.
    pub(crate) fn plain(text: impl Into<String>) -> Self {
        Inline::Run {
            text: text.into(),
            ink: Ink::Plain,
        }
    }

    /// Text in a theme role.
    pub(crate) fn role(text: impl Into<String>, role: ThemeColor) -> Self {
        Inline::Run {
            text: text.into(),
            ink: Ink::Role(role),
        }
    }
}

/// A span another renderer already styled keeps its style.
impl From<Span> for Inline {
    fn from(span: Span) -> Self {
        Inline::Run {
            text: span.content,
            ink: Ink::Content(span.style),
        }
    }
}

/// How a text row fits the width it gets.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Fit {
    /// As is; an enclosing inset cuts it.
    Keep,
    /// Cut to the width, ending in an ellipsis when cut.
    Ellipsis,
}

/// One node of a card.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Element {
    /// One row of inline pieces, fitted to the width.
    Text { inlines: Vec<Inline>, fit: Fit },
    /// A wrapped row whose first line leads with `gutter`; later lines
    /// indent by the gutter's width.
    Row {
        gutter: Vec<Inline>,
        body: Vec<Inline>,
    },
    /// Children from top to bottom.
    Column(Vec<Element>),
    /// The child moved right by `left` blank columns; every row is cut at
    /// the width.
    Inset { left: usize, child: Box<Element> },
}

impl Element {
    /// A row with nothing on it.
    pub(crate) fn blank() -> Self {
        Element::Text {
            inlines: Vec::new(),
            fit: Fit::Keep,
        }
    }

    /// One text row.
    pub(crate) fn text(fit: Fit, inlines: Vec<Inline>) -> Self {
        Element::Text { inlines, fit }
    }

    /// A row another renderer already styled, kept as is.
    pub(crate) fn line(line: Line) -> Self {
        Element::Text {
            inlines: line.into_iter().map(Inline::from).collect(),
            fit: Fit::Keep,
        }
    }
}

/// The animation frame the working icon shows.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Tick(pub(crate) usize);

/// Draw an element into rows at `width`.
pub(crate) fn render(element: &Element, theme: &Theme, width: usize, tick: Tick) -> Vec<Line> {
    let mut rows = Vec::new();
    Painter { theme, tick }.paint(element, width, &mut rows);
    rows
}

struct Painter<'a> {
    theme: &'a Theme,
    tick: Tick,
}

impl Painter<'_> {
    fn paint(&self, element: &Element, width: usize, rows: &mut Vec<Line>) {
        match element {
            Element::Text { inlines, fit } => {
                let line = self.line(inlines);
                match fit {
                    Fit::Keep => rows.push(line),
                    Fit::Ellipsis => {
                        rows.push(truncate_line(&line, width, crate::glyphs::ELLIPSIS));
                    }
                }
            }
            Element::Row { gutter, body } => {
                let gutter = self.line(gutter);
                let indent = line_width(&gutter);
                let wrapped = wrap_line(&self.line(body), width.saturating_sub(indent).max(1));
                for (index, mut row) in wrapped.into_iter().enumerate() {
                    let mut line = if index == 0 {
                        gutter.clone()
                    } else {
                        vec![Span::raw(" ".repeat(indent))]
                    };
                    line.append(&mut row);
                    rows.push(line);
                }
            }
            Element::Column(children) => {
                for child in children {
                    self.paint(child, width, rows);
                }
            }
            Element::Inset { left, child } => {
                let mut inner = Vec::new();
                self.paint(child, width.saturating_sub(*left).max(1), &mut inner);
                for mut row in inner {
                    let mut line = vec![Span::raw(" ".repeat(*left))];
                    line.append(&mut row);
                    rows.push(truncate_line(&line, width, ""));
                }
            }
        }
    }

    fn line(&self, inlines: &[Inline]) -> Line {
        inlines
            .iter()
            .map(|inline| match inline {
                Inline::Run { text, ink } => Span::styled(text.clone(), self.ink(*ink)),
                Inline::Status { status } => self.status(*status),
            })
            .collect()
    }

    fn ink(&self, ink: Ink) -> Style {
        match ink {
            Ink::Plain => Style::default(),
            Ink::Role(role) => self.theme.fg_style(role),
            Ink::Content(style) => style,
        }
    }

    /// The status mark, padded to the two cells of `ok` so the rows'
    /// names line up whatever the status.
    fn status(&self, status: Status) -> Span {
        let (icon, role) = match status {
            Status::Queued => (crate::glyphs::DOT_OFF, ThemeColor::Muted),
            Status::Running => (
                crate::chat::working_icon_frame(self.tick.0),
                ThemeColor::BashMode,
            ),
            Status::Done => (crate::glyphs::OK, ThemeColor::Success),
            Status::Error => (crate::glyphs::FAIL, ThemeColor::Error),
            Status::Aborted => (crate::glyphs::FAIL, ThemeColor::Warning),
        };
        let mut mark = icon.to_string();
        while str_width(&mark) < STATUS_MARK_WIDTH {
            mark.push(' ');
        }
        Span::styled(mark, self.theme.fg_style(role))
    }
}

#[cfg(test)]
mod tests;
