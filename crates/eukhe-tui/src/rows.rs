//! The transcript's role gutter: the one place a row's indent and its
//! mark come from. Columns are 0-based. The user header's `>` sits at
//! column 1 and its text at column 3. Every row inside a turn (thinking,
//! tool, injected, usage footer) hangs its mark at column 3. Agent text
//! sits at column 5. Quoted bodies sit behind a dim `| ` bar: the
//! expanded thinking's at column 3, tool output's at column 6. A wrapped
//! row keeps its body column.

use crate::glyphs;
use crate::style::Style;
use crate::theme::{Theme, ThemeColor};
use crate::width::{str_width, truncate_to_width};
use crate::{Line, Span};

/// Where one kind of transcript row sits in the gutter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Gutter {
    /// The user header: the `>` mark at column 1, the text at column 3.
    User,
    /// A row inside a turn: its mark (`+`/`-` thinking, `ok`/`x ` tool,
    /// `[label]` injected, `--` footer) at column 3, the body one space
    /// after the mark; wrapped rows hang at column 5.
    Step,
    /// Agent text and markdown: no mark, the body at column 5.
    Text,
    /// The expanded thinking body: a dim `| ` bar at column 3, the text
    /// at column 5.
    StepQuote,
    /// Quoted tool output: a dim `| ` bar at column 6, the text at
    /// column 8.
    ToolQuote,
}

impl Gutter {
    /// The column of the row's mark (of the bar, for the quote kinds).
    #[must_use]
    pub const fn mark_col(self) -> usize {
        match self {
            Gutter::User => 1,
            Gutter::Step | Gutter::StepQuote => 3,
            Gutter::Text => 5,
            Gutter::ToolQuote => 6,
        }
    }

    /// The column a continuation row's body starts at.
    #[must_use]
    pub const fn body_col(self) -> usize {
        match self {
            Gutter::User => 3,
            Gutter::Step | Gutter::Text | Gutter::StepQuote => 5,
            Gutter::ToolQuote => 8,
        }
    }

    /// The width a body wraps at: the row minus the body column and one
    /// right margin column.
    #[must_use]
    pub fn body_width(self, width: usize) -> usize {
        width.saturating_sub(self.body_col() + 1).max(1)
    }

    const fn has_bar(self) -> bool {
        matches!(self, Gutter::StepQuote | Gutter::ToolQuote)
    }

    /// The first row's prefix: `mark` (in its own style) at the mark
    /// column, then one space. The quote kinds draw their bar, and a row
    /// without a mark hangs like a continuation row.
    #[must_use]
    pub fn lead(self, mark: Option<Span>, theme: &Theme) -> Line {
        match mark {
            Some(mark) if !self.has_bar() => {
                vec![Span::raw(" ".repeat(self.mark_col())), mark, Span::raw(" ")]
            }
            _ => self.hang(theme),
        }
    }

    /// A continuation row's prefix: blank up to the body column, or the
    /// dim bar for the quote kinds.
    #[must_use]
    pub fn hang(self, theme: &Theme) -> Line {
        if self.has_bar() {
            vec![
                Span::raw(" ".repeat(self.mark_col())),
                Span::styled(glyphs::QUOTE_BAR, theme.fg_style(ThemeColor::Dim)),
            ]
        } else {
            vec![Span::raw(" ".repeat(self.body_col()))]
        }
    }

    /// `body` rows placed in the gutter: the first behind `lead(mark)`,
    /// the rest behind `hang`, each padded to `width` with unstyled
    /// spaces.
    #[must_use]
    pub fn place(
        self,
        mark: Option<Span>,
        body: Vec<Line>,
        theme: &Theme,
        width: usize,
    ) -> Vec<Line> {
        let mut mark = mark;
        body.into_iter()
            .map(|line| {
                let mut row = match mark.take() {
                    Some(mark) => self.lead(Some(mark), theme),
                    None => self.hang(theme),
                };
                row.extend(line);
                crate::chat::pad_to(row, width, Style::default())
            })
            .collect()
    }

    /// The plain-text first-row prefix (print mode): [`Gutter::lead`]
    /// without style.
    #[must_use]
    pub fn plain_lead(self, mark: &str) -> String {
        if self.has_bar() || mark.is_empty() {
            return self.plain_hang();
        }
        format!("{}{mark} ", " ".repeat(self.mark_col()))
    }

    /// The plain-text continuation prefix (print mode).
    #[must_use]
    pub fn plain_hang(self) -> String {
        if self.has_bar() {
            format!("{}{}", " ".repeat(self.mark_col()), glyphs::QUOTE_BAR)
        } else {
            " ".repeat(self.body_col())
        }
    }
}

/// The word after the thinking mark.
pub const THINKING_LABEL: &str = "thinking";

/// The collapsed thinking row as plain text, gutter included:
/// `   + thinking: <first paragraph>`, the paragraph's lines joined and
/// cut with `...` where it runs past `width` less the right margin.
#[must_use]
pub fn thinking_summary(thinking: &str, width: usize) -> String {
    let mut lines = thinking
        .lines()
        .map(str::trim)
        .skip_while(|line| line.is_empty());
    let mut text = String::new();
    for line in lines.by_ref().take_while(|line| !line.is_empty()) {
        for word in line.split_whitespace() {
            let word = word.replace("**", "").replace('`', "");
            if word.is_empty() {
                continue;
            }
            if !text.is_empty() {
                text.push(' ');
            }
            text.push_str(&word);
        }
    }
    let lead = format!(
        "{}{THINKING_LABEL}:",
        Gutter::Step.plain_lead(glyphs::MARK_THINKING_COLLAPSED)
    );
    let room = width.saturating_sub(str_width(&lead) + 2);
    if text.is_empty() || room == 0 {
        return lead;
    }
    format!(
        "{lead} {}",
        truncate_to_width(&text, room, glyphs::ELLIPSIS)
    )
}
