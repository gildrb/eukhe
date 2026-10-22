use super::*;
use crate::theme::ColorMode;

fn theme() -> Theme {
    Theme::builtin("eukhe", ColorMode::TrueColor)
}

#[test]
fn status_icons_follow_the_status_and_the_tick_and_pad_to_two_cells() {
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
            vec![Inline::Status { status }, Inline::plain(" cell")],
        );
        let mark = format!("{icon:<STATUS_MARK_WIDTH$}");
        assert_eq!(
            render(&element, &theme, 40, Tick(2)),
            vec![vec![
                Span::styled(mark, theme.fg_style(role)),
                Span::raw(" cell"),
            ]],
            "{status:?}"
        );
    }
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
