//! The inline auth panel's requests on the plain terminal (`eukhe login`):
//! the sign-in URL, progress lines and notices go to stderr; a prompt is
//! answered by the next line on stdin. At the end of stdin (no terminal,
//! a closed pipe), the manual paste that races the browser callback stays
//! open, so the login prints the URL and waits for the callback; a prompt
//! that takes a blank answer gets one, and any other prompt cancels the
//! login.

use std::io::Write;

use eukhe_tui::auth_panel::{AuthPanelRequest, PastePromptTone};
use tokio::sync::{mpsc, oneshot};

/// The line under the sign-in URL when the flow gives no instructions.
const OPEN_URL_INSTRUCTIONS: &str = "Open the URL above in a browser to sign in.";

/// A prompt waiting for its answer.
#[derive(Debug)]
struct Prompt {
    text: String,
    tone: PastePromptTone,
    allow_empty: bool,
    reply: oneshot::Sender<Option<String>>,
}

/// stdin's lines, read on their own thread; the channel closes at the end
/// of input. The thread stays blocked on a stdin nobody writes to until
/// the process exits.
pub(super) fn stdin_lines() -> mpsc::UnboundedReceiver<String> {
    let (lines_tx, lines) = mpsc::unbounded_channel();
    std::thread::spawn(move || {
        for line in std::io::stdin().lines() {
            let Ok(line) = line else { return };
            if lines_tx.send(line).is_err() {
                return;
            }
        }
    });
    lines
}

/// Serve one login's panel requests until the login drops its panel
/// handles; returns the writer.
pub(super) async fn serve<W: Write>(
    mut requests: mpsc::UnboundedReceiver<AuthPanelRequest>,
    mut lines: mpsc::UnboundedReceiver<String>,
    mut out: W,
) -> W {
    let mut pending: Option<Prompt> = None;
    let mut input_open = true;
    loop {
        tokio::select! {
            biased;
            request = requests.recv() => match request {
                Some(request) => pending = shown(request, pending, input_open, &mut out),
                None => return out,
            },
            line = lines.recv(), if input_open && pending.is_some() => {
                pending = match (pending.take(), line) {
                    (Some(prompt), Some(line)) => answered(prompt, &line, &mut out),
                    (Some(prompt), None) => {
                        input_open = false;
                        at_end_of_input(prompt)
                    }
                    (None, _) => None,
                };
            }
        }
    }
}

/// Print one request; a prompt becomes the pending one (a new prompt
/// replaces a prompt the login stopped waiting for).
fn shown(
    request: AuthPanelRequest,
    pending: Option<Prompt>,
    input_open: bool,
    out: &mut impl Write,
) -> Option<Prompt> {
    match request {
        AuthPanelRequest::Progress { message }
        | AuthPanelRequest::Waiting { message }
        | AuthPanelRequest::Notice { message } => {
            print_line(out, &message);
            pending
        }
        AuthPanelRequest::AuthUrl { url, instructions } => {
            print_line(out, &url);
            print_line(
                out,
                instructions.as_deref().unwrap_or(OPEN_URL_INSTRUCTIONS),
            );
            pending
        }
        // A masked prompt reads like any other: stdin is a pipe or a
        // terminal in line mode.
        AuthPanelRequest::PastePrompt {
            prompt,
            tone,
            style: _,
            allow_empty,
            reply,
        } => {
            print_line(out, &prompt);
            let prompt = Prompt {
                text: prompt,
                tone,
                allow_empty,
                reply,
            };
            if input_open {
                Some(prompt)
            } else {
                at_end_of_input(prompt)
            }
        }
        // The session's settle notes: the subscription logins never send
        // them.
        AuthPanelRequest::ProviderSettled { .. } | AuthPanelRequest::McpSettled { .. } => pending,
    }
}

/// A line typed for `prompt`: the trimmed answer, or the prompt again for
/// a blank line it does not take.
fn answered(prompt: Prompt, line: &str, out: &mut impl Write) -> Option<Prompt> {
    let answer = line.trim();
    if answer.is_empty() && !prompt.allow_empty {
        print_line(out, &prompt.text);
        return Some(prompt);
    }
    // A closed reply: the login stopped waiting (the browser callback
    // arrived first), and the line answers nothing.
    let _ = prompt.reply.send(Some(answer.to_owned()));
    None
}

/// `prompt` once stdin has ended: the manual paste (the muted prompt that
/// races the browser callback) stays pending, a prompt that takes a blank
/// answer gets it, any other prompt is cancelled.
fn at_end_of_input(prompt: Prompt) -> Option<Prompt> {
    let answer = match (prompt.tone, prompt.allow_empty) {
        (PastePromptTone::Muted, _) => return Some(prompt),
        (PastePromptTone::Text, true) => Some(String::new()),
        (PastePromptTone::Text, false) => None,
    };
    // A closed reply: the login no longer waits for this prompt.
    let _ = prompt.reply.send(answer);
    None
}

/// One line of the login's output. A failed write (stderr closed) leaves
/// the login running: its outcome is the exit code.
fn print_line(out: &mut impl Write, text: &str) {
    let _ = writeln!(out, "{text}");
}

/// One line typed on the terminal without echo (the API-key prompt);
/// `None` on Esc, Ctrl-C or Ctrl-D.
pub(super) fn hidden_line(prompt: &str) -> std::io::Result<Option<String>> {
    eprint!("{prompt}");
    crossterm::terminal::enable_raw_mode()?;
    let typed = typed_line();
    let restored = crossterm::terminal::disable_raw_mode();
    eprintln!();
    restored?;
    typed
}

/// The keys typed up to Enter, in raw mode.
fn typed_line() -> std::io::Result<Option<String>> {
    use crossterm::event::{read, Event, KeyCode, KeyEventKind, KeyModifiers};
    let mut line = String::new();
    loop {
        let Event::Key(key) = read()? else { continue };
        if key.kind == KeyEventKind::Release {
            continue;
        }
        match key.code {
            KeyCode::Enter => return Ok(Some(line)),
            KeyCode::Esc => return Ok(None),
            KeyCode::Char('c' | 'd') if key.modifiers.contains(KeyModifiers::CONTROL) => {
                return Ok(None);
            }
            KeyCode::Char(typed) => line.push(typed),
            KeyCode::Backspace => {
                line.pop();
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests;
