//! The transcript protocol and the pace through `AgentView::compose`
//! (docs/interface.md S8): committed rows are written once, whatever
//! changes after them, and streamed text shows at its pace.

use super::*;
use crate::chat::{AssistantMessage, MessageBlock};
use crate::theme::{ColorMode, Theme};

fn view_with(entries: Vec<ChatEntry>) -> AgentView {
    let mut view = AgentView::new(Theme::builtin("eukhe", ColorMode::TrueColor));
    view.splash_suppressed = true;
    for entry in entries {
        view.push_entry(entry);
    }
    view
}

fn user(text: &str) -> ChatEntry {
    ChatEntry::User {
        text: text.to_string(),
    }
}

fn plain(rows: &[crate::Line]) -> Vec<String> {
    rows.iter().map(crate::app::plain_row).collect()
}

/// The history of one frame as plain text, with how it starts.
fn history(view: &mut AgentView, width: usize) -> (FrameStart, Vec<String>) {
    let frame = view.compose(width, 24);
    (frame.start, plain(&frame.history))
}

fn streaming(text: &str) -> AssistantMessage {
    AssistantMessage {
        blocks: vec![MessageBlock::Text(text.to_string())],
        has_tool_calls: false,
        streaming: true,
        error: None,
        aborted: false,
    }
}

/// A width change, a detail change, and an edit to a committed entry
/// write no history row again: only rows committed later reach the
/// scrollback, at the width of their own frame (resize policy
/// "preserve").
#[test]
fn committed_rows_are_written_once_whatever_changes_after_them() {
    let mut view = view_with(vec![user("first question")]);
    let (start, first) = history(&mut view, 80);
    assert_eq!(start, FrameStart::First);
    assert!(first.iter().any(|row| row.contains("first question")));

    assert_eq!(history(&mut view, 40), (FrameStart::Continue, Vec::new()));
    view.cycle_detail();
    assert_eq!(history(&mut view, 40), (FrameStart::Continue, Vec::new()));
    if let Some(ChatEntry::User { text }) = view.chat.get_mut(0) {
        *text = "edited".to_string();
    }
    view.mark_entry_stale(0);
    assert_eq!(history(&mut view, 40), (FrameStart::Continue, Vec::new()));

    view.push_entry(user("second question"));
    let (start, second) = history(&mut view, 40);
    let alone = {
        let mut only = view_with(vec![user("x"), user("second question")]);
        let all = plain(&only.compose(40, 24).history);
        let first_rows = plain(&view_with(vec![user("x")]).compose(40, 24).history).len();
        all[first_rows..].to_vec()
    };
    assert_eq!((start, second), (FrameStart::Continue, alone));
}

/// One composed frame painted through the inline terminal onto `screen`;
/// returns the bytes written.
fn paint(
    view: &mut AgentView,
    term: &mut crate::inline_term::InlineTerminal,
    screen: &mut crate::vt::Vt,
) -> (usize, String) {
    let frame = view.compose(60, 12);
    let mut out = Vec::new();
    let painted = term
        .paint(
            &mut out,
            crate::inline_term::InlineFrame {
                history: &frame.history,
                live: &frame.live,
                cursor: frame.cursor,
            },
        )
        .unwrap();
    assert_eq!(painted, crate::inline_term::Painted::Drawn);
    let bytes = String::from_utf8(out).unwrap();
    screen.feed(&bytes);
    (frame.history.len(), bytes)
}

/// A rebuilt transcript never rewrites the old one: the scrollback keeps
/// every old row as written (no screen or scrollback clear), one dim
/// separator row names the break, and the new transcript commits below
/// it. The frames after it continue.
#[test]
fn a_new_transcript_starts_below_a_separator_and_keeps_the_old_rows() {
    let _global = crate::inline_term::live_area_lock();
    let mut view = view_with(vec![user("old question")]);
    let mut term = crate::inline_term::InlineTerminal::new(60, 12);
    let mut screen = crate::vt::Vt::new(60, 12);
    let (old_rows, _) = paint(&mut view, &mut term, &mut screen);
    let before = screen.all();

    view.clear_chat(TranscriptBreak::Session);
    view.chrome.session_name = Some("next".to_string());
    view.push_entry(user("new question"));
    let (new_rows, bytes) = paint(&mut view, &mut term, &mut screen);
    for clear in ["\x1b[3J", "\x1b[2J", "\x1b[H"] {
        assert!(!bytes.contains(clear), "{clear:?} in {bytes:?}");
    }
    let after = screen.all();
    assert_eq!(after[..old_rows], before[..old_rows]);
    let separator = format!("-- new session: next {}", "-".repeat(39));
    assert_eq!(after[old_rows], separator);
    let new_history = after[old_rows + 1..old_rows + new_rows].to_vec();
    let mut fresh = view_with(vec![user("new question")]);
    let expected = plain(&fresh.compose(60, 12).history);
    assert_eq!(new_history, expected);
    assert_eq!(history(&mut view, 60), (FrameStart::Continue, Vec::new()));
}

/// A streamed message shows at its pace: each frame shows more of it,
/// never more than arrived; it stays live until all of it shows after
/// the stream ends, and then commits whole, once.
#[test]
fn streamed_text_shows_at_its_pace_and_commits_whole() {
    let text = "word ".repeat(80);
    let mut view = view_with(vec![user("q")]);
    view.push_entry(ChatEntry::Assistant(Box::new(streaming(&text))));
    history(&mut view, 120);
    let shown = |view: &AgentView| view.paces.get(&1).map(|pace| pace.shown());
    assert_eq!(shown(&view), Some(100));
    history(&mut view, 120);
    assert_eq!(shown(&view), Some(175));

    if let Some(ChatEntry::Assistant(message)) = view.chat.get_mut(1) {
        message.streaming = false;
    }
    let mut frames = 0;
    let committed = loop {
        frames += 1;
        let (_, rows) = history(&mut view, 120);
        if !rows.is_empty() {
            break rows;
        }
        assert!(view.is_pacing(), "a live message is still behind its pace");
    };
    assert_eq!(frames, 17);
    assert!(!view.is_pacing());
    let whole = {
        let mut done = view_with(vec![user("q")]);
        let mut message = streaming(&text);
        message.streaming = false;
        done.push_entry(ChatEntry::Assistant(Box::new(message)));
        let all = plain(&done.compose(120, 24).history);
        let first_rows = plain(&view_with(vec![user("q")]).compose(120, 24).history).len();
        all[first_rows..].to_vec()
    };
    assert_eq!(committed, whole);
}

/// Ctrl+O while a message streams is no arrival: thinking that turns
/// visible counts as shown, so the text already on screen stays, and
/// thinking that turns hidden leaves the text where it was.
#[test]
fn a_detail_change_while_streaming_keeps_the_shown_text() {
    let text = "word ".repeat(20);
    let mut message = streaming(&text);
    message
        .blocks
        .insert(0, MessageBlock::Thinking("t".repeat(500)));
    let mut view = view_with(vec![user("q")]);
    view.push_entry(ChatEntry::Assistant(Box::new(message.clone())));
    let counts = |view: &AgentView| view.paces.get(&1).map(|pace| (pace.recv(), pace.shown()));
    history(&mut view, 120);
    assert_eq!(counts(&view), Some((100, 25)));

    view.detail = Detail::Details;
    history(&mut view, 120);
    assert_eq!(counts(&view), Some((600, 543)));
    let mut cut = message.clone();
    cut.blocks = vec![
        MessageBlock::Thinking("t".repeat(500)),
        MessageBlock::Text("word ".repeat(9).chars().take(43).collect()),
    ];
    assert_eq!(view.paced_message(1, &message), Some(cut));

    view.detail = Detail::Overview;
    history(&mut view, 120);
    assert_eq!(counts(&view), Some((100, 57)));
}

/// The live stack keeps the newest rows when the entries overflow it:
/// the children are cut from their top, so the stack draws them whole
/// and the dock stays at the bottom.
#[test]
fn the_live_stack_keeps_the_newest_rows_above_the_dock() {
    let mut view = view_with(vec![]);
    view.push_entry(ChatEntry::Assistant(Box::new(streaming(&(0..40).fold(
        String::new(),
        |mut text, n| {
            let _ = std::fmt::Write::write_fmt(&mut text, format_args!("line {n}\n\n"));
            text
        },
    )))));
    view.pace_rate = crate::pace::PaceRate {
        min: 10_000,
        lag: 0,
    };
    let frame = view.compose(60, 12);
    let rows = plain(&frame.live);
    assert_eq!(rows.len(), 12);
    let dock = plain(&view.compose_dock(60).0);
    assert_eq!(rows[12 - dock.len()..], dock[..]);
    assert!(rows[12 - dock.len() - 1].contains("line 39"));
}
