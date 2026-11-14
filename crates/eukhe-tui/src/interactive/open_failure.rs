//! The startup open's failure routes: a refused or slow open hands the
//! pane to the agents view with the failure as its status line (the
//! session-picker fallback); a daemon that never came up shows its error
//! in the frame; every other failure ends the surface and returns the
//! error.

use super::{
    mpsc, AgentView, ExitGuard, InteractiveOutcome, Renderer, Result, SessionSelection,
    SurfaceExit, UiInput,
};
use crate::chat::{ChatEntry, StatusKind};
use crate::glyphs::WARN;

/// Why the startup open failed.
pub(super) enum OpenFailure {
    /// The daemon did not start, or the UI could not attach to it.
    Connect(anyhow::Error),
    /// The attached daemon's open failed.
    Open(anyhow::Error),
}

/// End the surface whose daemon never came up or never took the UI's
/// connection: the error shows in the frame until the next key, then the
/// terminal goes back and the error returns (the CLI prints it on the
/// plain screen as well).
///
/// # Errors
///
/// Returns `error`, or a draw failure.
pub(super) async fn finish_failed_connect(
    error: anyhow::Error,
    exit_guard: &ExitGuard,
    mut renderer: Renderer,
    view: &mut AgentView,
    ui_rx: &mut mpsc::UnboundedReceiver<UiInput>,
) -> Result<InteractiveOutcome> {
    if renderer.is_terminal() {
        // Keys typed before the error showed do not acknowledge it.
        while ui_rx.try_recv().is_ok() {}
        view.push_entry(ChatEntry::Status {
            text: format!("{WARN} Error: {error:#}"),
            kind: StatusKind::Error,
        });
        view.push_entry(ChatEntry::Status {
            text: "Press any key to exit.".to_string(),
            kind: StatusKind::Info,
        });
        renderer.draw(view)?;
        while let Some(input) = ui_rx.recv().await {
            match input {
                UiInput::Key(_) => break,
                UiInput::Resize => {
                    if let Ok((_width, height)) = crossterm::terminal::size() {
                        view.set_terminal_rows(height);
                    }
                    view.note_resize();
                    renderer.draw(view)?;
                }
                UiInput::Paste(_)
                | UiInput::Submit(_)
                | UiInput::SubmitAndSettle { .. }
                | UiInput::SettleIdle
                | UiInput::WaitIdle { .. }
                | UiInput::WaitRender { .. }
                | UiInput::WaitGone { .. }
                | UiInput::Scroll(_)
                | UiInput::Mouse(_)
                | UiInput::HeadlessDone => {}
            }
        }
        exit_guard.arm_for_exit();
    }
    renderer.finish(SurfaceExit::Process, view);
    Err(error)
}

/// End the surface whose startup open failed with `error`.
///
/// A daemon refusal for the startup create/attach/resume (the daemon is
/// alive and refused THIS request -- a remembered id whose worker is
/// gone, or a saved-session create the daemon refuses, e.g. "Session is
/// already active in <id>" while another instance holds the session
/// file) and a response/handshake timeout (the daemon alive but slow at
/// load -- operator directive 2026-09-24) hand off to the agents view
/// instead of dying to the shell. Only transport/protocol failures
/// (daemon down, unanswerable socket) stay fatal.
///
/// # Errors
///
/// Returns `error` when it is fatal, after the terminal is handed back.
pub(super) fn finish_failed_open(
    error: anyhow::Error,
    selection: &SessionSelection,
    exit_guard: &ExitGuard,
    renderer: Renderer,
    view: &AgentView,
) -> Result<InteractiveOutcome> {
    // The unknown-session check matches the daemon's RAW refusal message
    // exactly - it must name this attach's own selector - so a selector
    // that happens to contain the phrase could not forge the refusal
    // (and vice versa).
    let unknown_session = match selection {
        SessionSelection::Attach(selector) => {
            let expected = format!("Unknown active session: {selector}");
            error
                .chain()
                .any(|cause| {
                    cause
                        .downcast_ref::<eukhe_client::daemon_client::RequestRejected>()
                        .is_some_and(|rejection| rejection.message == expected)
                })
                .then(|| {
                    format!(
                        "Session {selector} is no longer running -- pick a session to continue."
                    )
                })
        }
        SessionSelection::New | SessionSelection::NewChild { .. } | SessionSelection::Resume(_) => {
            None
        }
    };
    let notice = unknown_session.or_else(|| {
        if eukhe_client::daemon_client::is_daemon_timeout(&error) {
            Some(format!("{error:#} -- pick a session to continue."))
        } else if eukhe_client::daemon_client::is_daemon_rejection(&error) {
            Some(format!("{error:#}"))
        } else {
            None
        }
    });
    let Some(notice) = notice else {
        // The surface is already up: hand the terminal back before the
        // CLI reports the failure on the plain screen.
        if renderer.is_terminal() {
            exit_guard.arm_for_exit();
        }
        renderer.finish(SurfaceExit::Process, view);
        return Err(error);
    };
    // The handoff keeps the process alive: disarm the double-Ctrl+C
    // force-quit watchdog like the normal agents-view handoff does.
    exit_guard.cancel();
    let frames = renderer.finish(SurfaceExit::Handoff, view);
    Ok(InteractiveOutcome {
        return_to_agents_view: true,
        agents_view_notice: Some(notice),
        frames,
        ..Default::default()
    })
}
