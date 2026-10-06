use super::*;
use crate::chat::ChatEntry;
use crate::theme::{ColorMode, Theme};

const WIDTH: usize = 60;
const HEIGHT: usize = 20;

fn view_with_messages(count: usize) -> AgentView {
    let mut view = AgentView::new(Theme::builtin("eukhe", ColorMode::TrueColor));
    view.screen_mode = crate::screen_mode::ScreenMode::Fullscreen;
    for index in 0..count {
        push_message(&mut view, index);
    }
    view
}

fn push_message(view: &mut AgentView, index: usize) {
    view.push_entry(ChatEntry::User {
        text: format!("message {index:02}"),
    });
}

fn text(rows: &[Line]) -> Vec<String> {
    rows.iter().map(crate::app::plain_row).collect()
}

/// The transcript window of one fullscreen frame: the rows above the
/// dock (no toasts in these views).
fn window(view: &mut AgentView) -> Vec<String> {
    let frame = view.compose_fullscreen(WIDTH, HEIGHT);
    assert_eq!(frame.live.len(), HEIGHT);
    assert!(frame.history.is_empty());
    let dock = view.compose_dock(WIDTH).0.len();
    text(&frame.live[..HEIGHT - dock])
}

fn transcript(view: &mut AgentView) -> Vec<String> {
    text(&view.render_transcript(WIDTH))
}

fn more_below(rows: usize) -> String {
    format!("v {rows} more below - Ctrl+End to follow")
}

#[test]
fn every_fullscreen_frame_is_exactly_the_terminal_height() {
    for count in [0, 1, 40] {
        for height in [3, 8, 20, 60] {
            let mut view = view_with_messages(count);
            for request in [ScrollRequest::Up(ScrollAmount::Page), ScrollRequest::Bottom] {
                let frame = view.compose_fullscreen(WIDTH, height);
                assert_eq!(frame.live.len(), height, "{count} entries at {height} rows");
                assert!(frame.history.is_empty());
                view.scroll_viewport(request);
            }
        }
    }
}

#[test]
fn the_window_follows_the_bottom_as_entries_arrive() {
    let mut view = view_with_messages(40);
    let shown = window(&mut view);
    let all = transcript(&mut view);
    assert_eq!(shown, all[all.len() - shown.len()..]);

    push_message(&mut view, 40);
    let shown = window(&mut view);
    let all = transcript(&mut view);
    assert_eq!(shown, all[all.len() - shown.len()..]);
    assert!(shown.iter().any(|row| row.contains("message 40")));
}

#[test]
fn a_scrolled_window_holds_still_while_output_arrives() {
    let mut view = view_with_messages(40);
    window(&mut view);
    view.scroll_viewport(ScrollRequest::Up(ScrollAmount::Page));
    let before = window(&mut view);
    let total_before = transcript(&mut view).len();

    for index in 40..43 {
        push_message(&mut view, index);
    }
    let after = window(&mut view);
    let total_after = transcript(&mut view).len();

    let content = before.len() - 1;
    assert_eq!(before[..content], after[..content]);
    let below_before: usize = before[content]
        .split(' ')
        .nth(1)
        .and_then(|n| n.parse().ok())
        .expect("the indicator counts the rows below");
    assert_eq!(before[content], more_below(below_before));
    assert_eq!(
        after[content],
        more_below(below_before + total_after - total_before)
    );
}

#[test]
fn page_top_and_bottom_move_the_window() {
    let mut view = view_with_messages(40);
    let follow = window(&mut view);
    let all = transcript(&mut view);
    let rows = follow.len();
    let content = rows - 1;

    view.scroll_viewport(ScrollRequest::Top);
    let top = window(&mut view);
    assert_eq!(top[..content], all[..content]);
    assert_eq!(top[content], more_below(all.len() - content));

    // One page keeps the last visible row in view as the first.
    view.scroll_viewport(ScrollRequest::Down(ScrollAmount::Page));
    let paged = window(&mut view);
    let page = content - 1;
    assert_eq!(paged[..content], all[page..page + content]);

    view.scroll_viewport(ScrollRequest::Up(ScrollAmount::Page));
    assert_eq!(window(&mut view), top);

    view.scroll_viewport(ScrollRequest::Bottom);
    assert_eq!(window(&mut view), follow);

    // Paging up from the bottom: the window's old top row ends up one
    // page lower.
    view.scroll_viewport(ScrollRequest::Up(ScrollAmount::Page));
    let up = window(&mut view);
    let first = all.len() - rows - page;
    assert_eq!(up[..content], all[first..first + content]);

    // Paging down past the end follows again.
    view.scroll_viewport(ScrollRequest::Down(ScrollAmount::Page));
    view.scroll_viewport(ScrollRequest::Down(ScrollAmount::Page));
    assert_eq!(window(&mut view), follow);
}

#[test]
fn a_wheel_notch_scrolls_three_rows() {
    let mut view = view_with_messages(40);
    let follow = window(&mut view);
    let all = transcript(&mut view);
    let rows = follow.len();

    view.scroll_viewport(ScrollRequest::wheel(WheelDirection::Up));
    let up = window(&mut view);
    let first = all.len() - rows - crate::screen_mode::WHEEL_ROWS;
    assert_eq!(up[..rows - 1], all[first..first + rows - 1]);

    view.scroll_viewport(ScrollRequest::wheel(WheelDirection::Down));
    let down = window(&mut view);
    let first = first + crate::screen_mode::WHEEL_ROWS;
    assert_eq!(down[..rows - 1], all[first..first + rows - 1]);
}

#[test]
fn a_transcript_that_fits_never_scrolls() {
    let mut view = view_with_messages(1);
    let follow = window(&mut view);
    for request in [
        ScrollRequest::Up(ScrollAmount::Page),
        ScrollRequest::Top,
        ScrollRequest::wheel(WheelDirection::Up),
    ] {
        view.scroll_viewport(request);
        assert_eq!(window(&mut view), follow);
    }
    let all = transcript(&mut view);
    assert_eq!(follow[..all.len()], all[..]);
    assert!(follow[all.len()..].iter().all(String::is_empty));
}
