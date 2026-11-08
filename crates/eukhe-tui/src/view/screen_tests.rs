//! The transcript protocol and the pace through `AgentView::compose`: committed rows are written once, whatever
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

/// The loader row stays up after the turn ended while its answer's text
/// still shows at its pace, and goes down with the frame that shows the
/// last of it ("Turn visibility": the indicator is on
/// while the reply streams, to its last character on screen). A new
/// loader replaces the held row.
#[test]
fn the_loader_stays_up_until_the_streamed_text_all_shows() {
    let text = "word ".repeat(80);
    let working = WorkingState {
        phase: crate::activity::TurnPhase::Writing,
        message: None,
        download: false,
        tokens: 0,
        elapsed_secs: 0,
    };
    let loader_shown = |view: &mut AgentView| {
        let frame = view.compose(120, 24);
        plain(&frame.live)
            .iter()
            .any(|row| row.contains("Writing - "))
    };
    let mut view = view_with(vec![user("q")]);
    view.push_entry(ChatEntry::Assistant(Box::new(streaming(&text))));
    view.start_loader(working.clone(), std::time::Instant::now());
    assert!(loader_shown(&mut view));
    if let Some(ChatEntry::Assistant(message)) = view.chat.get_mut(1) {
        message.streaming = false;
    }
    // The turn's end stops the loader, then the run's end stops it again.
    view.stop_loader();
    assert_eq!(view.working, None, "the work ended");
    assert!(
        loader_shown(&mut view),
        "the row holds through the run's end"
    );
    view.stop_loader();
    let mut held = 0;
    loop {
        let shown = loader_shown(&mut view);
        if view.is_pacing() {
            assert!(shown, "the row holds while text reveals");
            held += 1;
        } else {
            assert!(
                !shown,
                "the frame that shows the last of the text: no loader"
            );
            break;
        }
    }
    assert!(held > 1, "the text was still behind its pace");
    assert_eq!(view.activity(), crate::activity::AgentActivity::Idle);

    // A reveal cut short by the next turn: its loader takes over, and the
    // next stop with nothing pacing takes the row down at once.
    view.push_entry(ChatEntry::Assistant(Box::new(streaming(&text))));
    view.start_loader(working, std::time::Instant::now());
    loader_shown(&mut view);
    if let Some(ChatEntry::Assistant(message)) = view.chat.get_mut(2) {
        message.streaming = false;
    }
    view.stop_loader();
    assert!(loader_shown(&mut view));
    view.start_loader(
        WorkingState {
            phase: crate::activity::TurnPhase::Sending,
            message: None,
            download: false,
            tokens: 0,
            elapsed_secs: 0,
        },
        std::time::Instant::now(),
    );
    while view.is_pacing() {
        view.compose(120, 24);
    }
    assert!(
        matches!(
            view.activity(),
            crate::activity::AgentActivity::Working {
                phase: crate::activity::TurnPhase::Sending,
                ..
            }
        ),
        "the new turn's loader outlives the reveal"
    );
    view.stop_loader();
    assert!(!loader_shown(&mut view));
}

/// A reply that failed after streaming text stays live while it is the
/// last entry, its text paced out or not: a retry episode's outcome row
/// may still retire its error row, and committed rows are never written
/// again. It commits once an entry follows it, as it reads then -- here
/// without the error row the outcome row replaced.
#[test]
fn a_failed_reply_stays_live_until_an_entry_follows_it() {
    let mut failed = streaming("Here is the pl");
    failed.streaming = false;
    failed.error = Some("Error: 529 overloaded".to_string());
    let mut view = view_with(vec![user("q")]);
    history(&mut view, 80);
    view.push_entry(ChatEntry::Assistant(Box::new(failed)));
    for _ in 0..40 {
        assert_eq!(history(&mut view, 80), (FrameStart::Continue, Vec::new()));
    }
    assert!(!view.is_pacing(), "the text is all on screen");

    if let Some(ChatEntry::Assistant(reply)) = view.chat.get_mut(1) {
        reply.error = None;
    }
    view.mark_entry_stale(1);
    view.push_entry(ChatEntry::Status {
        text: "Retry failed after 0 attempts: 529 overloaded".to_string(),
        kind: crate::chat::StatusKind::Error,
    });
    let (start, committed) = history(&mut view, 80);
    let retired = {
        let mut retired = streaming("Here is the pl");
        retired.streaming = false;
        let mut done = view_with(vec![user("q"), ChatEntry::Assistant(Box::new(retired))]);
        let all = plain(&done.compose(80, 24).history);
        let first_rows = plain(&view_with(vec![user("q")]).compose(80, 24).history).len();
        all[first_rows..].to_vec()
    };
    assert_eq!((start, committed), (FrameStart::Continue, retired));
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
