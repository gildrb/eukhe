use eukhe_tui::auth_panel::{AuthPanelHandle, PasteStyle};
use tokio::sync::oneshot::error::TryRecvError;

use super::*;

fn prompt(tone: PastePromptTone, allow_empty: bool) -> (Prompt, oneshot::Receiver<Option<String>>) {
    let (reply, answer) = oneshot::channel();
    (
        Prompt {
            text: "Enter:".to_string(),
            tone,
            allow_empty,
            reply,
        },
        answer,
    )
}

/// At the end of stdin the manual paste stays open (the browser callback
/// ends the login), a blank-allowed prompt gets the blank answer, and any
/// other prompt is cancelled.
#[test]
fn the_end_of_input_keeps_the_manual_paste_open() {
    let (muted, mut muted_answer) = prompt(PastePromptTone::Muted, false);
    let kept = at_end_of_input(muted);
    assert!(kept.is_some());
    assert_eq!(muted_answer.try_recv(), Err(TryRecvError::Empty));
    let (blank, mut blank_answer) = prompt(PastePromptTone::Text, true);
    assert!(at_end_of_input(blank).is_none());
    assert_eq!(blank_answer.try_recv(), Ok(Some(String::new())));
    let (required, mut required_answer) = prompt(PastePromptTone::Text, false);
    assert!(at_end_of_input(required).is_none());
    assert_eq!(required_answer.try_recv(), Ok(None));
}

/// A blank line asks a prompt that needs an answer again; a line answers
/// it trimmed.
#[test]
fn a_blank_line_asks_again_and_a_line_answers_trimmed() {
    let (required, mut answer) = prompt(PastePromptTone::Text, false);
    let mut out = Vec::new();
    let again = answered(required, "  ", &mut out).expect("asked again");
    assert_eq!(answer.try_recv(), Err(TryRecvError::Empty));
    assert!(answered(again, "  code=abc&state=st \n", &mut out).is_none());
    assert_eq!(answer.try_recv(), Ok(Some("code=abc&state=st".to_string())));
    assert_eq!(String::from_utf8(out).unwrap(), "Enter:\n");
}

/// The URL, its instructions and the progress print in order; the
/// prompt takes the next stdin line; the loop ends with the login.
#[tokio::test]
async fn serve_prints_the_url_and_answers_the_prompt_from_stdin() {
    let (requests_tx, requests) = mpsc::unbounded_channel();
    let (lines_tx, lines) = mpsc::unbounded_channel();
    let panel = AuthPanelHandle::new(requests_tx);
    let login = async move {
        panel.auth_url("https://auth.example/authorize?state=st", None);
        panel.progress("Waiting for the browser...");
        let answer = panel
            .paste_prompt("Paste:", PastePromptTone::Muted, PasteStyle::Visible)
            .await;
        panel.auth_url("https://auth.example/device", Some("Enter code: AB-12"));
        answer
    };
    lines_tx.send("pasted".to_string()).unwrap();
    let (answer, out) = tokio::join!(login, serve(requests, lines, Vec::new()));
    assert_eq!(answer, Some("pasted".to_string()));
    assert_eq!(
        String::from_utf8(out).unwrap(),
        "https://auth.example/authorize?state=st\n\
         Open the URL above in a browser to sign in.\n\
         Waiting for the browser...\n\
         Paste:\n\
         https://auth.example/device\n\
         Enter code: AB-12\n"
    );
}
