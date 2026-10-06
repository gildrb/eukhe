//! The startup chat-view block (`OptChat` spec S10: "On start, print the view, so
//! you see what the agent sees"): when a session opens, the chat memory's
//! current view lands in the transcript as one collapsed summary row --
//! `Chat view: N lines, M messages, X KB` -- that expands (Ctrl+O, or a
//! click on the row) to the full `<chat>` text under the branch gutter.
//! The text is raw: view lines are `id+n|text`, never markdown.

use eukhe_types::daemon::ChatViewSnapshot;

use crate::branch::branch_block;
use crate::chat::Detail;
use crate::theme::{Theme, ThemeColor};
use crate::width::truncate_line;
use crate::{Line, Span};

/// The collapsed row's text: `Chat view: N lines, M messages, X KB`, the
/// size in KiB to one decimal (rounded).
#[must_use]
pub(crate) fn chat_view_summary(view: &ChatViewSnapshot) -> String {
    let count = |n: u64, one: &str, many: &str| format!("{n} {}", if n == 1 { one } else { many });
    let tenths = view.bytes.saturating_mul(10).saturating_add(512) / 1024;
    format!(
        "Chat view: {}, {}, {}.{} KB",
        count(view.lines, "line", "lines"),
        count(view.messages, "message", "messages"),
        tenths / 10,
        tenths % 10,
    )
}

/// The block's rows: an optional leading blank, the one-row summary, and --
/// expanded -- the whole `<chat>` text under the branch gutter.
pub(crate) fn render_chat_view(
    view: &ChatViewSnapshot,
    detail: Detail,
    theme: &Theme,
    width: usize,
    leading: bool,
) -> Vec<Line> {
    let mut out = Vec::new();
    if leading {
        out.push(Vec::new());
    }
    out.push(truncate_line(
        &vec![Span::styled(
            format!(" {} {}", crate::glyphs::NOTICE, chat_view_summary(view)),
            theme.fg_style(ThemeColor::Muted),
        )],
        width,
        "",
    ));
    if detail.tool_output_expanded() {
        out.extend(branch_block(
            &vec![Span::raw(view.text.clone())],
            theme,
            width,
        ));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theme::ColorMode;

    fn plain(rows: &[Line]) -> Vec<String> {
        rows.iter()
            .map(|row| {
                row.iter()
                    .map(|span| span.content.as_str())
                    .collect::<String>()
                    .trim_end()
                    .to_string()
            })
            .collect()
    }

    fn snapshot(text: &str, messages: u64) -> ChatViewSnapshot {
        ChatViewSnapshot {
            text: text.to_string(),
            messages,
            lines: text.lines().count().saturating_sub(2) as u64,
            bytes: text.len() as u64,
        }
    }

    #[test]
    fn the_summary_counts_lines_messages_and_size() {
        assert_eq!(
            chat_view_summary(&snapshot("<chat>\n</chat>", 0)),
            "Chat view: 0 lines, 0 messages, 0.0 KB"
        );
        let one = snapshot("<chat>\n0+1|hello\n</chat>", 1);
        assert_eq!(
            chat_view_summary(&one),
            "Chat view: 1 line, 1 message, 0.0 KB"
        );
        let big = ChatViewSnapshot {
            bytes: 3_200,
            ..snapshot("<chat>\n0+2|a\n2+1|b\n</chat>", 3)
        };
        assert_eq!(
            chat_view_summary(&big),
            "Chat view: 2 lines, 3 messages, 3.1 KB"
        );
    }

    /// Collapsed, the block is the summary row alone; expanded, the raw
    /// `<chat>` text follows under the branch gutter, one row per view
    /// line (no markdown: `|` never becomes a table).
    #[test]
    fn the_block_expands_to_the_raw_view_text() {
        let theme = Theme::builtin("eukhe", ColorMode::TrueColor);
        let view = snapshot("<chat>\n0+2|user: hi | bot: hello\n2+1|plan\n</chat>", 3);
        let collapsed = render_chat_view(&view, Detail::Details, &theme, 80, false);
        assert_eq!(
            plain(&collapsed),
            vec![" * Chat view: 2 lines, 3 messages, 0.0 KB"]
        );
        let expanded = render_chat_view(&view, Detail::All, &theme, 80, true);
        assert_eq!(
            plain(&expanded),
            vec![
                String::new(),
                " * Chat view: 2 lines, 3 messages, 0.0 KB".to_string(),
                " `- <chat>".to_string(),
                "    0+2|user: hi | bot: hello".to_string(),
                "    2+1|plan".to_string(),
                "    </chat>".to_string(),
            ]
        );
    }
}
