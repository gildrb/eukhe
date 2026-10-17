use super::*;
use crate::theme::ColorMode;

fn theme() -> Theme {
    Theme::builtin("eukhe", ColorMode::TrueColor)
}

fn panel(status: Status, padding: usize, children: Vec<Element>) -> Element {
    Element::Panel(Panel {
        title: "bash".to_string(),
        status,
        fill: ThemeBg::ToolPanelBg,
        padding,
        children,
    })
}

#[test]
fn panel_header_shows_the_status_word_in_the_status_color() {
    let theme = theme();
    let bg = theme.bg_style(ThemeBg::ToolPanelBg);
    let cases = [
        (Status::Queued, "queued".to_string(), ThemeColor::Muted),
        (
            Status::Running,
            format!("{} running", crate::glyphs::WORKING[1]),
            ThemeColor::BashMode,
        ),
        (Status::Done, "done".to_string(), ThemeColor::Success),
        (Status::Error, "error".to_string(), ThemeColor::Error),
        (Status::Aborted, "aborted".to_string(), ThemeColor::Warning),
    ];
    for (status, word, role) in cases {
        let fill = 20 - "bash - ".len() - word.len();
        assert_eq!(
            render(&panel(status, 2, Vec::new()), &theme, 24, Tick(1)),
            vec![vec![
                Span::styled("  ", bg),
                Span::styled("bash", bg.patch(theme.fg_style(ThemeColor::Muted))),
                Span::styled(" - ", bg.patch(theme.fg_style(ThemeColor::Dim))),
                Span::styled(word, bg.patch(theme.fg_style(role))),
                Span::styled(" ".repeat(fill), bg),
                Span::styled("  ", bg),
            ]],
            "{status:?}"
        );
    }
}

#[test]
fn status_icons_follow_the_status_and_the_tick() {
    let theme = theme();
    let cases = [
        (Status::Queued, crate::glyphs::DOT_OFF, ThemeColor::Muted),
        (
            Status::Running,
            crate::glyphs::WORKING[2],
            ThemeColor::BashMode,
        ),
        (Status::Done, crate::glyphs::OK, ThemeColor::Success),
        (Status::Error, crate::glyphs::FAIL, ThemeColor::Error),
        (Status::Aborted, crate::glyphs::FAIL, ThemeColor::Warning),
    ];
    for (status, icon, role) in cases {
        let element = Element::text(
            Fit::Keep,
            vec![
                Inline::Status {
                    status,
                    mark: Mark::Icon,
                },
                Inline::plain(" cell"),
            ],
        );
        assert_eq!(
            render(&element, &theme, 40, Tick(2)),
            vec![vec![
                Span::styled(icon, theme.fg_style(role)),
                Span::raw(" cell"),
            ]],
            "{status:?}"
        );
    }
}

#[test]
fn panel_pads_and_fills_children_below_a_blank_row() {
    let theme = theme();
    let bg = theme.bg_style(ThemeBg::SelectedBg);
    let element = Element::Panel(Panel {
        title: "t".to_string(),
        status: Status::Done,
        fill: ThemeBg::SelectedBg,
        padding: 1,
        children: vec![Element::text(
            Fit::Keep,
            vec![Inline::role("out", ThemeColor::ToolOutput)],
        )],
    });
    assert_eq!(
        render(&element, &theme, 12, Tick(0)),
        vec![
            vec![
                Span::styled(" ", bg),
                Span::styled("t", bg.patch(theme.fg_style(ThemeColor::Muted))),
                Span::styled(" - ", bg.patch(theme.fg_style(ThemeColor::Dim))),
                Span::styled("done", bg.patch(theme.fg_style(ThemeColor::Success))),
                Span::styled("  ", bg),
                Span::styled(" ", bg),
            ],
            vec![
                Span::styled(" ", bg),
                Span::styled(" ".repeat(10), bg),
                Span::styled(" ", bg),
            ],
            vec![
                Span::styled(" ", bg),
                Span::styled("out", bg.patch(theme.fg_style(ThemeColor::ToolOutput))),
                Span::styled(" ".repeat(7), bg),
                Span::styled(" ", bg),
            ],
        ]
    );
}

#[test]
fn panel_children_get_the_width_inside_the_padding_and_overlong_rows_are_cut() {
    let theme = theme();
    let bg = theme.bg_style(ThemeBg::ToolPanelBg);
    let element = panel(
        Status::Done,
        2,
        vec![
            Element::text(Fit::Wrap, vec![Inline::plain("aaaa bbbb")]),
            Element::text(Fit::Keep, vec![Inline::plain("abcdefghij")]),
        ],
    );
    let rows = render(&element, &theme, 8, Tick(0));
    assert_eq!(
        rows[2..].to_vec(),
        vec![
            vec![
                Span::styled("  ", bg),
                Span::styled("aaaa", bg),
                Span::styled("", bg),
                Span::styled("  ", bg),
            ],
            vec![
                Span::styled("  ", bg),
                Span::styled("bbbb", bg),
                Span::styled("", bg),
                Span::styled("  ", bg),
            ],
            vec![Span::styled("  abcdef", bg)],
        ]
    );
}

#[test]
fn row_hangs_wrapped_lines_under_the_gutter() {
    let element = Element::Row {
        gutter: vec![Inline::plain("> ")],
        body: vec![Inline::plain("aa bb cc")],
    };
    assert_eq!(
        render(&element, &theme(), 5, Tick(0)),
        vec![
            vec![Span::raw("> "), Span::raw("aa")],
            vec![Span::raw("  "), Span::raw("bb")],
            vec![Span::raw("  "), Span::raw("cc")],
        ]
    );
}

#[test]
fn inset_shifts_its_child_and_cuts_at_the_width() {
    let element = Element::Inset {
        left: 1,
        child: Box::new(Element::Column(vec![
            Element::text(Fit::Keep, vec![Inline::plain("abcdef")]),
            Element::text(Fit::Ellipsis, vec![Inline::plain("abcdef")]),
        ])),
    };
    assert_eq!(
        render(&element, &theme(), 5, Tick(0)),
        vec![
            vec![Span::raw(" abcd")],
            vec![Span::raw(" "), Span::raw("a"), Span::raw("...")],
        ]
    );
}

#[test]
fn styled_lines_keep_their_spans() {
    let theme = theme();
    let line = vec![
        Span::styled("code", theme.fg_style(ThemeColor::MdCodeBlock)),
        Span::raw(""),
    ];
    let element = Element::Column(vec![Element::line(line.clone()), Element::blank()]);
    assert_eq!(render(&element, &theme, 2, Tick(0)), vec![line, Vec::new()]);
}
