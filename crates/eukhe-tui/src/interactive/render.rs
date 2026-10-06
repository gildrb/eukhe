//! The render sink concern: the inline-terminal/headless renderer, the
//! startup chrome seeding, the tmux keyboard check, and the suspend-cycle
//! terminal handoff.

use super::{
    mpsc, terminal, AgentView, Duration, ExitGuard, HeadlessStep, InteractiveOptions, KeyEvent,
    Result, SessionUi, UiInput, UiMode,
};
use crate::screen_mode::ScreenMode;

/// One typed string as key events: characters become `Char` presses, `\n`
/// becomes Enter, and `\t` becomes Tab (the keys autocomplete reacts to).
fn typed_keys(text: &str) -> Vec<KeyEvent> {
    text.chars()
        .map(|c| match c {
            '\n' | '\r' => KeyEvent::new(
                crossterm::event::KeyCode::Enter,
                crossterm::event::KeyModifiers::NONE,
            ),
            '\t' => KeyEvent::new(
                crossterm::event::KeyCode::Tab,
                crossterm::event::KeyModifiers::NONE,
            ),
            other => KeyEvent::new(
                crossterm::event::KeyCode::Char(other),
                crossterm::event::KeyModifiers::NONE,
            ),
        })
        .collect()
}

/// Seed the static chrome state for a fresh interactive run: splash
/// version/cwd, the chat name, the `manage` hint for persisted sessions,
/// and the zero dock a fresh session mounts -- the placeholder frame
/// keeps the landed frame's geometry.
pub(super) fn apply_startup_chrome(view: &mut AgentView, options: &InteractiveOptions) {
    view.chrome.version.clone_from(&options.version);
    view.chrome.cwd = options.cwd.to_string_lossy().to_string();
    view.chrome.chat_name = crate::chrome::display_name(&view.chrome.cwd);
    view.chrome.show_manage = !options.no_session;
    view.chrome.tray_depth = options.session_rlm_depth;
    view.chrome.activity = Some(crate::chrome::ActivityDock::default());
}

/// The tmux keyboard notice (TS `checkTmuxKeyboardSetup`): warn once per
/// start when tmux runs without `extended-keys`. Runs `tmux show` read-only
/// against the ambient socket; a timeout or error suppresses the notice.
pub(super) async fn check_tmux_keyboard_setup() -> Option<String> {
    if std::env::var("TMUX").is_err() {
        return None;
    }
    let query = |option: &'static str| async move {
        tokio::time::timeout(
            Duration::from_secs(2),
            tokio::task::spawn_blocking(move || {
                std::process::Command::new("tmux")
                    .args(["show", "-gv", option])
                    // No inherited fds: a probe must never hold the
                    // terminal the TUI owns (the fd-set audit's rule --
                    // no TUI child ever holds /dev/tty).
                    .stdin(std::process::Stdio::null())
                    .stdout(std::process::Stdio::piped())
                    .stderr(std::process::Stdio::null())
                    .output()
            }),
        )
        .await
        .ok()
        .and_then(Result::ok)
        .and_then(Result::ok)
        .and_then(|output| {
            if output.status.success() {
                Some(String::from_utf8_lossy(&output.stdout).trim().to_string())
            } else {
                None
            }
        })
    };
    let extended_keys = query("extended-keys").await?;
    if extended_keys != "on" && extended_keys != "always" {
        return Some(
            "tmux extended-keys is off. Modified Enter keys may not work. Add `set -g extended-keys on` to ~/.tmux.conf and restart tmux.".to_string(),
        );
    }
    None
}

/// Rendering sink: the inline terminal or headless frame capture.
pub(super) enum Renderer {
    Terminal {
        term: crate::inline_term::InlineTerminal,
        /// The screen mode the terminal is set up for; `None` until the
        /// first frame and after a resume: the next draw sets the screen
        /// up for the view's mode (a fullscreen one repaints whole).
        shown: Option<ScreenMode>,
        /// The reader's channel and force-quit guard: the external-editor
        /// cycle stops and respawns the session reader around the child
        /// run, and the terminal renderer owns the seeds for the respawn.
        ui_tx: mpsc::UnboundedSender<UiInput>,
        exit_guard: ExitGuard,
    },
    Headless {
        width: u16,
        height: u16,
        /// Plain text of every history row composed so far (a replay
        /// starts it over).
        history: Vec<String>,
        frames: Vec<String>,
    },
}

/// The renderer handoff of one suspend cycle (TS `handleCtrlZ`):
/// `stop` hands the terminal to the shell (the live area left as output,
/// raw mode off); `resume` takes it back after SIGCONT with every mode
/// re-applied and a new live area below the shell's output.
struct TerminalHandoff<'a> {
    renderer: &'a mut Renderer,
}

impl crate::suspend::SuspendTerminal for TerminalHandoff<'_> {
    fn stop(&mut self) -> Result<()> {
        self.renderer.suspend()
    }

    fn resume(&mut self) -> Result<()> {
        self.renderer.resume()
    }
}

/// Run the terminal handoffs a handled key requested.
///
/// TS `handleCtrlZ` (`app.suspend`, default ctrl+z): hand the terminal
/// to the shell and stop the process group; execution continues here once
/// the user foregrounds the process (SIGCONT), where the cycle re-applies
/// raw mode and the key modes and takes the screen back (TS `ui.start()`).
///
/// TS `openExternalEditor`: hand the terminal to the editor, then resume.
/// The input reader would steal the editor's keys, so it stops (flag +
/// join) and respawns after the resume.
///
/// Headless runs keep no terminal renderer (TS never registers the
/// actions without one), so both requests are observed and dropped.
pub(super) async fn hand_terminal_to_requests(
    session: &mut SessionUi,
    view: &mut AgentView,
    renderer: &mut Renderer,
) {
    use crate::suspend::{SuspendSignals, SuspendTerminal};
    if session.take_suspend_request() && renderer.is_terminal() {
        match crate::suspend::suspend_cycle(
            &mut crate::suspend::ProcessSignals,
            &mut TerminalHandoff {
                renderer: &mut *renderer,
            },
        ) {
            Ok(()) => session.track_suspend_used("resumed"),
            Err(error) => {
                session.track_suspend_used("failed");
                session.error_row(&format!("{error:#}"), view);
                // Try to take the terminal back so the run stays usable;
                // if that also fails, the next draw surfaces the broken
                // frame.
                let _ = renderer.resume();
            }
        }
    }
    let Some(command) = session.take_external_editor_request() else {
        return;
    };
    let (ui_tx, exit_guard) = match &*renderer {
        Renderer::Terminal {
            ui_tx, exit_guard, ..
        } => (ui_tx.clone(), exit_guard.clone()),
        Renderer::Headless { .. } => return,
    };
    crate::input::stop_reader();
    // The suspend path's SIGINT shield: the handoff restores cooked mode
    // (ISIG), and a cooked-mode editor wrapper (`code --wait`, `subl -w`)
    // turns Ctrl+C into SIGINT for the shared foreground group -- the
    // default disposition would kill the TUI mid-edit. The no-op handler
    // (never SIG_IGN) keeps the child's own Ctrl+C: handled signals reset
    // to the default across exec.
    let mut signals = crate::suspend::ProcessSignals;
    let stopped = signals.ignore_sigint().and_then(|()| {
        TerminalHandoff {
            renderer: &mut *renderer,
        }
        .stop()
    });
    let outcome = match stopped {
        Ok(()) => crate::external_editor::edit(&command, &view.editor.get_expanded_text()).await,
        Err(error) => Err(error),
    };
    // The suspend cycle's order: SIGINT is back to the default before the
    // surface takes the terminal.
    let _ = signals.restore_sigint();
    // TS resumes in a `finally`: the surface returns even when the editor
    // run failed.
    let resumed = TerminalHandoff {
        renderer: &mut *renderer,
    }
    .resume();
    if let Err(error) = resumed {
        session.error_row(&format!("{error:#}"), view);
    }
    spawn_session_reader(ui_tx, exit_guard);
    session.apply_external_editor_outcome(outcome, view);
}

/// Start the session surface's terminal input reader (the setup mount and
/// the external-editor cycle's respawn both call it). One reader thread
/// feeds the loop; crossterm events are process-global, so the reader
/// registry joins the previous surface's reader before this one starts
/// polling. The reader also observes Ctrl+C pairs for the exit guard:
/// this thread stays alive when the UI loop is wedged, so the force-quit
/// contract holds regardless of loop state. The paste-aware variant
/// coalesces a marker-less multi-line keystroke burst (tmux 3.2 and older
/// forward pastes without bracketed markers) into one editor paste -- TS
/// `StdinBuffer`'s `isRawMultilinePaste`.
fn spawn_session_reader(ui_tx: mpsc::UnboundedSender<UiInput>, exit_guard: ExitGuard) {
    crate::input::spawn_paste_aware_reader(move |input| match input {
        crate::input::ReaderInput::BurstPaste(text) => ui_tx.send(UiInput::Paste(text)).is_ok(),
        crate::input::ReaderInput::Event(event) => match event {
            crossterm::event::Event::Key(key) => {
                exit_guard.observe_key(&key);
                ui_tx.send(UiInput::Key(key)).is_ok()
            }
            crossterm::event::Event::Paste(text) => ui_tx.send(UiInput::Paste(text)).is_ok(),
            // TS forces a full re-render on resize (tui.ts
            // widthChanged/heightChanged); the loop replays the history at
            // the new size.
            crossterm::event::Event::Resize(..) => ui_tx.send(UiInput::Resize).is_ok(),
            // Wheel reports arrive only while a fullscreen surface has
            // reporting on; every other mouse event and the focus
            // reports carry nothing the surface reads.
            crossterm::event::Event::Mouse(mouse) => {
                match crate::screen_mode::wheel_scroll(mouse) {
                    Some(direction) => ui_tx
                        .send(UiInput::Scroll(crate::view::ScrollRequest::wheel(
                            direction,
                        )))
                        .is_ok(),
                    None => true,
                }
            }
            crossterm::event::Event::FocusGained | crossterm::event::Event::FocusLost => true,
        },
    });
}

impl Renderer {
    pub(super) fn setup(
        ui: UiMode,
        ui_tx: mpsc::UnboundedSender<UiInput>,
        exit_guard: ExitGuard,
        surface_mounted: &std::sync::Arc<std::sync::atomic::AtomicBool>,
    ) -> Result<Renderer> {
        match ui {
            UiMode::Terminal => {
                // The raw-mode bracket's own `cfmakeraw` write clears IXON,
                // which is the kernel's one trigger for lifting a pending
                // Ctrl+S stop: a tty stopped at the shell prompt self-heals
                // here (verified by the flow e2e's launch route).
                terminal::enable_raw_mode()?;
                // The terminal state changed: every later setup step is
                // fallible and an error from any of them still owns the
                // release. The flag arms here, not at the end of setup.
                surface_mounted.store(true, std::sync::atomic::Ordering::SeqCst);
                // Bracketed paste and the kitty keyboard protocol come up
                // with the raw-mode bracket (TS `ProcessTerminal.start`):
                // pastes arrive as one chunk instead of per-line Enter
                // submissions, and the kitty probe (once per process --
                // see `enhanced_keys`) runs before the reader thread
                // starts polling.
                crate::enhanced_keys::enable(&mut std::io::stdout())?;
                spawn_session_reader(ui_tx.clone(), exit_guard.clone());
                // The live area starts at the cursor's line: the shell's
                // next line for a fresh process, the previous surface's
                // cleared live area for a view switch. Nothing is painted
                // until the first frame, which also sets the screen up for
                // the view's mode (a fullscreen handoff keeps the previous
                // surface on screen until then).
                Ok(Renderer::Terminal {
                    term: crate::inline_term::InlineTerminal::new(terminal::size()?.1),
                    shown: None,
                    ui_tx,
                    exit_guard,
                })
            }
            UiMode::Headless(plan) => {
                let steps = plan.steps;
                tokio::spawn(async move {
                    for step in steps {
                        match step {
                            HeadlessStep::Submit(text) => {
                                if ui_tx.send(UiInput::Submit(text)).is_err() {
                                    return;
                                }
                            }
                            HeadlessStep::SubmitAndSettle { text, timeout_ms } => {
                                if ui_tx
                                    .send(UiInput::SubmitAndSettle { text, timeout_ms })
                                    .is_err()
                                {
                                    return;
                                }
                            }
                            HeadlessStep::Type(text) => {
                                for key in typed_keys(&text) {
                                    if ui_tx.send(UiInput::Key(key)).is_err() {
                                        return;
                                    }
                                }
                            }
                            HeadlessStep::Paste(text) => {
                                if ui_tx.send(UiInput::Paste(text)).is_err() {
                                    return;
                                }
                            }
                            HeadlessStep::SettleIdle => {
                                if ui_tx.send(UiInput::SettleIdle).is_err() {
                                    return;
                                }
                            }
                            HeadlessStep::WaitIdle { timeout_ms } => {
                                if ui_tx.send(UiInput::WaitIdle { timeout_ms }).is_err() {
                                    return;
                                }
                            }
                            HeadlessStep::WaitRender { needle, timeout_ms } => {
                                if ui_tx
                                    .send(UiInput::WaitRender { needle, timeout_ms })
                                    .is_err()
                                {
                                    return;
                                }
                            }
                            HeadlessStep::WaitGone { needle, timeout_ms } => {
                                if ui_tx
                                    .send(UiInput::WaitGone { needle, timeout_ms })
                                    .is_err()
                                {
                                    return;
                                }
                            }
                            HeadlessStep::WaitMs(ms) => {
                                tokio::time::sleep(std::time::Duration::from_millis(ms)).await;
                            }
                            HeadlessStep::Key(key) => {
                                if ui_tx.send(UiInput::Key(key)).is_err() {
                                    return;
                                }
                            }
                        }
                    }
                    let _ = ui_tx.send(UiInput::HeadlessDone);
                });
                Ok(Renderer::Headless {
                    width: plan.width,
                    height: plan.height,
                    history: Vec::new(),
                    frames: Vec::new(),
                })
            }
        }
    }

    /// Hand the terminal back to the process (the live area left as
    /// output, or the alternate screen left with wheel reporting off;
    /// keys off, raw mode off, cursor visible) so an interactive client
    /// command or a stopped job can use it. Headless verification runs
    /// keep their plain pipes. The shared exit tail ends the hand-back --
    /// the same whole-terminal contract every exit guarantees.
    fn suspend(&mut self) -> Result<()> {
        match self {
            Renderer::Terminal { term, shown, .. } => {
                // The raw-mode bracket takes the enhanced-key modes with
                // it (TS `stop` on suspend: paste markers off, kitty
                // flags popped); `resume` re-enables both.
                let mut out = std::io::stdout();
                let _ = crate::enhanced_keys::disable(&mut out);
                if !crate::screen_mode::leave_alt_screen(&mut out) {
                    term.release(&mut out)?;
                }
                *shown = None;
                crate::exit_restore::terminal_release_tail(&mut out);
                Ok(())
            }
            Renderer::Headless { .. } => Ok(()),
        }
    }

    /// Take the terminal back after a suspended client command. The next
    /// frame starts a new live area below whatever the command printed,
    /// or (fullscreen) re-enters the alternate screen and repaints it.
    pub(super) fn resume(&mut self) -> Result<()> {
        match self {
            Renderer::Terminal { term, .. } => {
                // The raw re-arm's `cfmakeraw` write clears IXON - the
                // kernel's one trigger for lifting a pending Ctrl+S stop -
                // so a stop armed at the shell while the process sat
                // suspended never holds the resume's repaint (verified by
                // the flow e2e's suspend route).
                terminal::enable_raw_mode()?;
                // The raw-mode bracket re-arms the enhanced-key modes (TS
                // `start` on SIGCONT re-runs the paste enable and the kitty
                // query; the port resolves the kitty capability once per
                // process, so a resume re-applies the resolved state --
                // crossterm's support check monopolizes the event-reader
                // lock for its 2s budget and must not run on the resume
                // path).
                crate::enhanced_keys::enable(&mut std::io::stdout())?;
                *term = crate::inline_term::InlineTerminal::new(terminal::size()?.1);
                Ok(())
            }
            Renderer::Headless { .. } => Ok(()),
        }
    }

    /// Whether this run owns a real terminal (the force-quit guard arms on
    /// terminal runs; headless verification keeps deterministic teardown).
    pub(super) fn is_terminal(&self) -> bool {
        matches!(self, Renderer::Terminal { .. })
    }

    /// Paint one frame on the terminal; headless runs capture through
    /// [`Renderer::render_headless`] instead. The first frame (and the
    /// first after a resume or a `/settings` switch) sets the screen up
    /// for the view's mode.
    pub(super) fn draw(&mut self, view: &mut AgentView) -> Result<()> {
        let Renderer::Terminal { term, shown, .. } = self else {
            return Ok(());
        };
        let mode = view.screen_mode;
        let mut paint = crate::app::Paint::Changed;
        if *shown != Some(mode) {
            let mut out = std::io::stdout().lock();
            let height = terminal::size()?.1;
            match mode {
                ScreenMode::Fullscreen => {
                    if *shown == Some(ScreenMode::Inline) {
                        term.clear_live(&mut out)?;
                    }
                    crate::screen_mode::enter_alt_screen(&mut out)?;
                    paint = crate::app::Paint::Full;
                }
                ScreenMode::Inline => {
                    // Back on the normal screen at the line the inline
                    // live area started on: the history replays, since
                    // entries settled while the alternate screen was up.
                    if crate::screen_mode::leave_alt_screen(&mut out) {
                        *term = crate::inline_term::InlineTerminal::new(height);
                        view.request_replay();
                    }
                }
            }
            *shown = Some(mode);
        }
        match mode {
            ScreenMode::Inline => crate::app::draw(term, view),
            ScreenMode::Fullscreen => crate::app::draw_fullscreen(term, view, paint),
        }
    }

    /// Capture one frame as plain text (headless assertions). Inline:
    /// every history row composed so far, then the live area.
    /// Fullscreen: the screen-sized frame. A frame that has not changed
    /// does not add a duplicate.
    pub(super) fn render_headless_pane(&mut self, view: &mut AgentView) {
        let Renderer::Headless {
            width,
            height,
            history,
            frames,
        } = self
        else {
            return;
        };
        let (width, height) = (usize::from(*width), usize::from(*height));
        let text = match view.screen_mode {
            ScreenMode::Inline => {
                let frame = view.compose(width, height);
                if frame.replay {
                    history.clear();
                }
                history.extend(frame.history.iter().map(crate::app::plain_row));
                let mut text = history.join("\n");
                for row in &frame.live {
                    if !text.is_empty() {
                        text.push('\n');
                    }
                    text.push_str(&crate::app::plain_row(row));
                }
                text
            }
            ScreenMode::Fullscreen => {
                history.clear();
                let frame = view.compose_fullscreen(width, height);
                let rows: Vec<String> = frame.live.iter().map(crate::app::plain_row).collect();
                rows.join("\n")
            }
        };
        if frames.last().map(String::as_str) != Some(text.as_str()) {
            frames.push(text);
        }
    }

    /// The headless capture's frames (None on a terminal renderer): the
    /// render barriers wait on these.
    pub(super) fn headless_frames(&self) -> Option<&[String]> {
        match self {
            Renderer::Headless { frames, .. } => Some(frames),
            Renderer::Terminal { .. } => None,
        }
    }

    /// Capture one session frame as plain text (headless assertions).
    pub(super) fn render_headless(&mut self, session: &mut SessionUi, view: &mut AgentView) {
        self.render_headless_pane(view);
        session.dirty = false;
    }

    /// Teardown. A `handoff` exit (agents-back, `/resume`) clears the live
    /// area so the next surface starts its own there (a fullscreen surface
    /// keeps the alternate screen for the next one to repaint), and keeps
    /// raw mode on (the in-process gap would otherwise echo keypresses).
    /// Every other exit leaves the live area as the final output with the
    /// cursor on the line below it (a fullscreen surface leaves the
    /// alternate screen and prints the transcript to the normal screen),
    /// then restores the terminal -- the resume hint the composition root
    /// prints next lands right below the transcript.
    pub(super) fn finish(self, handoff: SurfaceExit, view: &AgentView) -> Vec<String> {
        let ending = matches!(handoff, SurfaceExit::Process);
        // The exit that ends the process stands the kitty probe down
        // FIRST: an answer landing after the pop below would re-arm
        // CSI-u reporting on the parent shell (the "escape codes while
        // typing" leak). A handoff keeps the process alive and the next
        // surface's probe -- never released here.
        if ending && self.is_terminal() {
            crate::enhanced_keys::release_for_exit();
        }
        // The surface's input reader stands down FIRST (TS tears its
        // listener down with the chat): the drain below reads the tty
        // through crossterm's global event-reader lock, and a parked
        // reader would hold it.
        crate::input::request_reader_stop();
        // A process exit turns wheel reporting off with the alternate
        // screen before the drain, so no report lands in the shell.
        let fullscreen_shown = ending
            && matches!(
                &self,
                Renderer::Terminal {
                    shown: Some(ScreenMode::Fullscreen),
                    ..
                }
            )
            && crate::screen_mode::leave_alt_screen(&mut std::io::stdout());
        // In-flight kitty key releases are consumed before the terminal is
        // restored (TS `drainInput` before `stop`): a release that lands
        // after raw mode is off would leak its escape sequence into the
        // parent shell over slow SSH. A handoff keeps raw mode on, so its
        // drain consumes only what is already buffered.
        if ending {
            crate::enhanced_keys::drain(&mut std::io::stdout());
        } else {
            crate::enhanced_keys::drain_for_handoff(&mut std::io::stdout());
        }
        // The enhanced-key modes release with the raw-mode bracket (TS
        // `stop` writes the paste disable, the kitty pop, and the
        // modifyOtherKeys reset for every exit, handoffs included).
        let _ = crate::enhanced_keys::disable(&mut std::io::stdout());
        match self {
            Renderer::Terminal {
                mut term, shown, ..
            } => {
                let mut out = std::io::stdout();
                if ending {
                    if fullscreen_shown {
                        let (width, height) = terminal::size().unwrap_or((80, 24));
                        let _ = print_transcript(view, width, height, &mut out);
                    } else {
                        let _ = term.release(&mut out);
                    }
                    // The shared exit tail: the synchronized-output
                    // release, the SGR reset, the cursor show, and the
                    // cooked-tty verification.
                    crate::exit_restore::terminal_release_tail(&mut out);
                } else if shown != Some(ScreenMode::Fullscreen) {
                    let _ = term.clear_live(&mut out);
                }
                Vec::new()
            }
            Renderer::Headless { frames, .. } => frames,
        }
    }
}

/// The fullscreen exit's output on the normal screen (after the
/// alternate screen is left): the splash and every entry, the rows inline
/// mode leaves in scrollback, with the cursor on the line below them.
pub(super) fn print_transcript(
    view: &AgentView,
    width: u16,
    height: u16,
    out: &mut impl std::io::Write,
) -> std::io::Result<()> {
    let rows = view.render_history(usize::from(width));
    let mut term = crate::inline_term::InlineTerminal::new(height);
    term.paint(
        out,
        crate::inline_term::InlineFrame {
            history: &rows,
            live: &[],
            cursor: None,
        },
    )?;
    term.release(out)
}

/// How the chat surface ends.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum SurfaceExit {
    /// The process ends (or prints and exits): the live area stays as
    /// output and the terminal is restored.
    Process,
    /// Another surface takes the terminal in-process: the live area is
    /// cleared for it and raw mode stays on.
    Handoff,
}

/// The spinner's wall-clock cadence (TS `Loader` `DEFAULT_INTERVAL_MS`):
/// the animation phase advances one frame per 80ms of animating time
/// regardless of the render rate.
pub(super) const SPINNER_INTERVAL_MS: u128 = 80;

/// The animating loader's next phase boundary, the wake the select needs
/// while a quiet turn waits out its stream: TS `Loader`'s `setInterval`
/// keeps painting the 80ms cadence through quiet turns, and this
/// boundary is that interval's timer. The wake always precedes the
/// phase change it observes -- an off-by-one here parks the loop for a
/// whole boundary instead of firing at the phase edge.
pub(super) fn next_spinner_deadline(
    started: std::time::Instant,
    now: std::time::Instant,
) -> std::time::Instant {
    // The remainder form keeps the arithmetic bounded by one phase: a
    // wide phase counter would truncate through `as usize` on 32-bit
    // targets after ~10.9 years of continuous animation and arm an
    // already-expired deadline, hot-spinning the select's wake.
    let into_phase = now.duration_since(started).as_millis() % SPINNER_INTERVAL_MS;
    now + Duration::from_millis((SPINNER_INTERVAL_MS - into_phase) as u64)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The boundary the select arms is always the current phase's
    /// 80ms edge -- the wake must precede the phase change it observes
    /// (an off-by-one parks the loop for a whole boundary). Samples sit
    /// at least a millisecond inside their phase because `Instant`
    /// round-trips can lose sub-millisecond ticks on the platform
    /// clock, and the phase is floored from whole milliseconds.
    #[test]
    fn spinner_deadline_is_the_current_phase_edge() {
        let started = std::time::Instant::now();
        let at = |ms: u64| started + Duration::from_millis(ms);
        assert_eq!(next_spinner_deadline(started, started), at(80));
        assert_eq!(next_spinner_deadline(started, at(1)), at(80));
        assert_eq!(next_spinner_deadline(started, at(79)), at(80));
        assert_eq!(next_spinner_deadline(started, at(81)), at(160));
        assert_eq!(next_spinner_deadline(started, at(161)), at(240));
        assert_eq!(next_spinner_deadline(started, at(239)), at(240));
    }
}
