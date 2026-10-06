//! Terminal app: crossterm event loop driving an [`AgentView`] against a
//! [`SessionStream`] (the replay verifier binary), and the one chat paint
//! both it and the interactive surface use.

use crate::editor::{Editor, EditorEvent};
use crate::inline_term::{InlineFrame, InlineTerminal};
use crate::keys::key_event_to_id;
use crate::session::{SessionEvent, SessionStream};
use crate::theme::Theme;
use crate::view::AgentView;
use anyhow::Result;
use crossterm::event::{Event, KeyCode, KeyEvent, KeyModifiers};
use crossterm::terminal::{self};
use std::io::stdout;
use std::time::Duration;

pub struct AppOptions {
    pub theme: String,
    /// Replay delay per entry while streaming history (ms). 0 = instant load.
    pub replay_delay_ms: u64,
    /// Auto-exit after this many ms of runtime (headless verification).
    pub auto_exit_ms: Option<u64>,
    /// Panic after the first paint (the exit-restore verifier's panic-path
    /// driver: a real unwind on the live surface must still leave the
    /// terminal whole).
    pub panic_after_frame: bool,
}

impl Default for AppOptions {
    fn default() -> Self {
        Self {
            theme: "eukhe".to_string(),
            replay_delay_ms: 0,
            auto_exit_ms: None,
            panic_after_frame: false,
        }
    }
}

#[must_use]
pub fn load_theme(name: &str) -> Theme {
    let mode = crate::theme::detect_color_mode();
    // The default brand theme when the caller passes none (empty) or an
    // unknown name; only known builtins resolve.
    let known = ["eukhe", "dark", "light"];
    let name = if known.contains(&name) { name } else { "eukhe" };
    Theme::builtin(name, mode)
}

/// Run the view against a session stream until the stream ends and the user
/// exits. `on_submit` receives editor submissions (unused in replay mode).
///
/// Every error return funnels through the one exit restore: an early `?`
/// after the mount (a stream read, a draw failure) must not hand the shell
/// a terminal still in TUI state.
///
/// # Errors
///
/// Returns `Err` when the surface fails to mount or the replay loop fails
/// (raw-mode enable, a stream read, or a draw); the exit restore runs
/// first, so the shell never keeps a TUI-state terminal.
pub fn run_app(
    stream: Box<dyn SessionStream>,
    options: &AppOptions,
    on_submit: Box<dyn FnMut(&str) + Send>,
) -> Result<()> {
    match run_app_surface(stream, options, on_submit) {
        Ok(()) => Ok(()),
        Err(error) => {
            crate::exit_restore::restore_terminal();
            Err(error)
        }
    }
}

fn run_app_surface(
    mut stream: Box<dyn SessionStream>,
    options: &AppOptions,
    mut on_submit: Box<dyn FnMut(&str) + Send>,
) -> Result<()> {
    // The TS theme emits raw ANSI color codes regardless of NO_COLOR; match
    // that so the same terminal renders the same frames either way.
    crossterm::style::force_color_output(true);
    // A panic anywhere between the mount below and the deliberate
    // teardown must still hand the terminal back whole (the same
    // unwind-guard contract the session surface arms).
    let _surface_restore = crate::exit_restore::SurfaceRestore::armed();
    // The raw-mode bracket's `cfmakeraw` write clears IXON, which is the
    // kernel's one trigger for lifting a pending Ctrl+S stop (see the
    // flow e2e's launch route).
    terminal::enable_raw_mode()?;
    // The replay surface owns the same enhanced-key modes as the session
    // (TS `ProcessTerminal.start`): bracketed pastes arrive as one chunk.
    crate::enhanced_keys::enable(&mut std::io::stdout())?;
    let mut term = InlineTerminal::new(terminal::size()?.1);

    let theme = load_theme(&options.theme);
    let mut view = AgentView::new(theme);
    let mut running = true;
    let start = std::time::Instant::now();
    let mut stream_ended = false;

    loop {
        // Drain stream events.
        if !stream_ended {
            match stream.poll()? {
                SessionEvent::Item(item) => {
                    if let crate::session::TranscriptItem::ModelChange { provider, model_id } =
                        &item
                    {
                        view.chrome.model_id = Some(model_id.clone());
                        view.chrome.model_provider = Some(provider.clone());
                    }
                    view.push(item);
                    if options.replay_delay_ms > 0 {
                        std::thread::sleep(Duration::from_millis(options.replay_delay_ms));
                    }
                }
                SessionEvent::End => stream_ended = true,
            }
        }

        let (_w, h) = crossterm::terminal::size()?;
        view.set_terminal_rows(h);
        draw(&mut term, &mut view)?;
        // The verifier's panic driver: the unwind must cross the live
        // surface's unwind guard, not the already-restored exit.
        assert!(
            !options.panic_after_frame,
            "eukhe-tui-replay: --panic-exit reached"
        );

        // Input.
        let timeout = Duration::from_millis(if stream_ended { 50 } else { 5 });
        if crossterm::event::poll(timeout)? {
            match crossterm::event::read()? {
                Event::Key(key) => {
                    handle_key(&mut view, key, &mut running, &mut *on_submit);
                }
                Event::Paste(text) => {
                    view.editor.handle_paste(&text);
                }
                // A resize reflows the scrollback the terminal holds: the
                // next frame replays the history at the new size.
                Event::Resize(..) => view.request_replay(),
                Event::FocusGained | Event::FocusLost | Event::Mouse(_) => {}
            }
        }
        // Materialize once per loop turn: a parked request resolves
        // right after its key, and a background `@` search lands on a
        // quiet turn the same way the interactive loop's input-idle
        // tick resolves it (`Editor::materialize_autocomplete`).
        view.editor.materialize_autocomplete();
        let _ = view.editor.take_events();

        if let Some(ms) = options.auto_exit_ms {
            if start.elapsed() >= Duration::from_millis(ms) {
                running = false;
            }
        }
        if !running && stream_ended {
            break;
        }
        if !stream_ended {
            continue;
        }
        if !running {
            break;
        }
    }

    term.release(&mut stdout())?;
    crate::exit_restore::restore_terminal();
    Ok(())
}

fn handle_key(
    view: &mut AgentView,
    key: KeyEvent,
    running: &mut bool,
    on_submit: &mut dyn FnMut(&str),
) {
    // App-level bindings (coding-agent keybindings.ts):
    // ctrl+c exits the app shell in replay mode; escape cancels autocomplete.
    if key.code == KeyCode::Char('c') && key.modifiers.contains(KeyModifiers::CONTROL) {
        if view.editor.is_showing_autocomplete() {
            view.editor.cancel_autocomplete();
            return;
        }
        *running = false;
        return;
    }
    if key.code == KeyCode::Char('d') && key.modifiers.contains(KeyModifiers::CONTROL) {
        *running = false;
        return;
    }
    if key.code == KeyCode::Esc {
        view.editor.cancel_autocomplete();
        return;
    }
    if key.code == KeyCode::Char('o') && key.modifiers.contains(KeyModifiers::CONTROL) {
        // Ctrl+O cycles conversation detail (TS `app.tools.expand`):
        // overview -> details -> all -> overview.
        view.cycle_detail();
        return;
    }
    let Some(id) = key_event_to_id(&key) else {
        return;
    };
    view.editor.handle_input(&id);
    dispatch_events(&mut view.editor, on_submit);
}

pub fn dispatch_events(editor: &mut Editor, on_submit: &mut dyn FnMut(&str)) {
    for ev in editor.take_events() {
        match ev {
            EditorEvent::Submitted(text) => {
                editor.add_to_history(&text);
                on_submit(&text);
            }
            // This minimal harness owns no terminal clipboard channel;
            // the full session UI (session_ui.rs) performs the copy.
            EditorEvent::Changed(_)
            | EditorEvent::AutocompleteToggled(_)
            | EditorEvent::ClipboardWrite(_) => {}
        }
    }
}

/// Paint one chat frame through the inline terminal: a replay frame
/// clears the screen and the scrollback first. The hardware cursor moves
/// to the editor caret every frame (IME candidate windows anchor there)
/// and shows only under `showHardwareCursor`.
pub(crate) fn draw(term: &mut InlineTerminal, view: &mut AgentView) -> Result<()> {
    let (width, height) = terminal::size()?;
    term.set_height(height);
    term.set_cursor_visible(view.show_hardware_cursor);
    let frame = view.compose(usize::from(width), usize::from(height));
    let mut out = stdout().lock();
    if frame.replay {
        term.reset(&mut out)?;
    }
    term.paint(
        &mut out,
        InlineFrame {
            history: &frame.history,
            live: &frame.live,
            cursor: frame.cursor,
        },
    )?;
    Ok(())
}

/// One row as plain text: styling, OSC 133 zone markers, and OSC 8
/// hyperlinks stripped.
pub(crate) fn plain_row(line: &crate::Line) -> String {
    let mut stripped = line.clone();
    crate::osc133::strip(&mut stripped);
    crate::hyperlinks::strip_osc8(&mut stripped);
    stripped.iter().map(|s| s.content.as_str()).collect()
}

/// Compose one frame as plain text (headless structural dump used by the
/// tmux verifier and diff tests): the history rows the frame commits,
/// then the live area. A fresh view's first frame carries the whole
/// transcript.
pub fn render_frame_text(view: &mut AgentView, width: u16, height: u16) -> Vec<String> {
    let frame = view.compose(usize::from(width), usize::from(height));
    frame
        .history
        .iter()
        .chain(&frame.live)
        .map(plain_row)
        .collect()
}
