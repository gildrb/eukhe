//! Typed elements for tool cards and the one renderer that turns them into
//! rows. A card says what to show: text in a theme role, a status, a
//! panel. Only this renderer picks the status glyphs and colors, the panel
//! fill, the padding and the width cuts.

use crate::style::Style;
use crate::theme::{Theme, ThemeBg, ThemeColor};
use crate::width::{line_width, truncate_line, wrap_line};
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

/// How a status shows inline.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Mark {
    /// The status glyph; the working icon while running.
    Icon,
    /// The status word; the working icon leads it while running.
    Word,
}

/// One piece of a text row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Inline {
    /// Text in one ink.
    Run { text: String, ink: Ink },
    /// A status mark in the status color.
    Status { status: Status, mark: Mark },
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
    /// As is; an enclosing inset or panel cuts it.
    Keep,
    /// Word-wrapped into as many rows as it needs.
    Wrap,
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
    /// A filled panel: the `title - status` header, then a blank row and
    /// the children when there are any.
    Panel(Panel),
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

/// A panel's props: the header, its fill and padding, and its rows.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Panel {
    pub(crate) title: String,
    pub(crate) status: Status,
    /// The background every panel row is filled with.
    pub(crate) fill: ThemeBg,
    /// Blank columns on each side of every row.
    pub(crate) padding: usize,
    pub(crate) children: Vec<Element>,
}

impl Panel {
    /// The width the children get inside the padding.
    pub(crate) fn content_width(&self, width: usize) -> usize {
        width.saturating_sub(2 * self.padding).max(1)
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
                    Fit::Wrap => rows.extend(wrap_line(&line, width)),
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
            Element::Panel(panel) => self.panel(panel, width, rows),
        }
    }

    fn panel(&self, panel: &Panel, width: usize, rows: &mut Vec<Line>) {
        let fill = Fill {
            style: self.theme.bg_style(panel.fill),
            padding: panel.padding,
            content_width: panel.content_width(width),
            width,
        };
        let header = vec![
            Span::styled(panel.title.clone(), self.theme.fg_style(ThemeColor::Muted)),
            Span::styled(
                crate::glyphs::SEP.to_string(),
                self.theme.fg_style(ThemeColor::Dim),
            ),
            self.status(panel.status, Mark::Word),
        ];
        rows.push(fill.row(header));
        let mut children = Vec::new();
        for child in &panel.children {
            self.paint(child, fill.content_width, &mut children);
        }
        if !children.is_empty() {
            rows.push(fill.row(Vec::new()));
            rows.extend(children.into_iter().map(|child| fill.row(child)));
        }
    }

    fn line(&self, inlines: &[Inline]) -> Line {
        inlines
            .iter()
            .map(|inline| match inline {
                Inline::Run { text, ink } => Span::styled(text.clone(), self.ink(*ink)),
                Inline::Status { status, mark } => self.status(*status, *mark),
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

    fn status(&self, status: Status, mark: Mark) -> Span {
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
        let text = match mark {
            Mark::Icon => icon.to_string(),
            Mark::Word => match status {
                Status::Queued => "queued".to_string(),
                Status::Running => format!("{icon} running"),
                Status::Done => "done".to_string(),
                Status::Error => "error".to_string(),
                Status::Aborted => "aborted".to_string(),
            },
        };
        Span::styled(text, self.theme.fg_style(role))
    }
}

/// How one panel row is padded and filled.
struct Fill {
    style: Style,
    padding: usize,
    content_width: usize,
    width: usize,
}

impl Fill {
    /// The content after the left padding, on the fill, padded out to the
    /// full width; content wider than the panel is cut at the width.
    fn row(&self, content: Line) -> Line {
        let used = line_width(&content);
        let mut line: Line = vec![Span::styled(" ".repeat(self.padding), self.style)];
        line.extend(
            content
                .into_iter()
                .map(|span| Span::styled(span.content, self.style.patch(span.style))),
        );
        if used > self.content_width {
            return truncate_line(&line, self.width, "");
        }
        line.push(Span::styled(
            " ".repeat(self.content_width - used),
            self.style,
        ));
        line.push(Span::styled(" ".repeat(self.padding), self.style));
        line
    }
}

#[cfg(test)]
mod tests;
