//! The Directors at a candidate stop (laws/stop.bend): a reply with no
//! tool call that hit the output limit in the middle of its text, or that
//! has no text, never ends the run as its answer; any other reply stands,
//! whatever it says, as does one that stops while the session owns
//! running work. Each test is a faux script whose stop ended the run before
//! the Directors and now goes on to its end. The round cap's note tells the
//! model the tool rounds left once few remain.

use std::sync::Arc;

use eukhe_ai::providers::faux::{faux_text, faux_thinking, RegisterFauxProviderOptions};
use eukhe_chord::json::JsonValue;
use eukhe_types::pi_ai::StopReason;
use futures::FutureExt;

use super::recoveries::{reply, seen, settle, tick, user, Seen, ASK, THINKING};
use super::run_bounds::tool;
use crate::harness::tests::chat_support::{chat_setup, ChatSetup};
use crate::harness::tests::support::{add_hooks, add_tool, generation_task};
use crate::harness::types::GenerationHooks;
use crate::types::SubmissionStatus;

/// Final answers that hand the next step to the user.
const HAND_OFFS: [&str; 2] = [
    "Done in my local copy; checks pass.\n\nNext: say \"ship it\" and I will commit, push and \
     deploy the change.",
    "Next: check the page in your browser, then tell me if I should commit.",
];

/// A session whose `pending_work` hook answers `pending`, and that offers
/// the tool `tick`.
fn setup_with_pending(pending: bool) -> ChatSetup {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_tool(&setup.registry, tool("tick", |n| format!("tick {n}")), None).unwrap();
    add_hooks(
        &setup.registry,
        generation_task(),
        GenerationHooks {
            pending_work: Some(Arc::new(move |_, _| async move { Ok(pending) }.boxed())),
            ..GenerationHooks::default()
        },
        None,
    )
    .unwrap();
    setup
}

#[tokio::test]
async fn an_answer_that_hands_off_to_the_user_ends_the_run_after_one_request() {
    for answer in HAND_OFFS {
        let setup = setup_with_pending(false);
        let requests = Seen::default();
        setup.faux.set_responses(vec![
            reply(&requests, vec![faux_text(answer)], StopReason::Stop),
            reply(&requests, vec![faux_text("unused")], StopReason::Stop),
        ]);
        assert_eq!(
            (
                settle(&setup).await,
                seen(&requests),
                setup.faux.get_pending_response_count()
            ),
            (
                (
                    (SubmissionStatus::Done, None, None),
                    vec![user(ASK), format!("assistant:{answer}")]
                ),
                vec![user(ASK)],
                1
            ),
            "{answer}"
        );
    }
}

#[tokio::test]
async fn an_answer_while_work_runs_is_a_pause_that_stands() {
    let setup = setup_with_pending(true);
    let requests = Seen::default();
    let answer = "The full test suite is running now.";
    setup.faux.set_responses(vec![
        reply(&requests, vec![faux_text(answer)], StopReason::Stop),
        reply(&requests, vec![faux_text("unused")], StopReason::Stop),
    ]);
    assert_eq!(
        (settle(&setup).await, seen(&requests)),
        (
            (
                (SubmissionStatus::Done, None, None),
                vec![user(ASK), format!("assistant:{answer}")]
            ),
            vec![user(ASK)]
        )
    );
    assert_eq!(setup.faux.get_pending_response_count(), 1);
}

/// The length note of `attempt` for a reply whose text the 8-token limit
/// cut (the faux provider counts a token per 4 chars), the `row`th in a
/// row.
fn cut_note(attempt: u64, row: u32) -> String {
    user(&format!(
        "Harness note, attempt {attempt}: your previous reply hit the 8-token output limit \
         before it finished, so the harness did not take its cut text as your answer. Reason \
         only about the next step, then call its tool. For a large answer (a file, a document, \
         a long text), write a minimal working version first, then extend it with further \
         edits in this turn. Length note {row} of 3."
    ))
}

#[tokio::test]
async fn a_reply_cut_at_the_output_limit_is_not_the_answer_and_the_run_goes_on() {
    let setup = setup_with_pending(false);
    let requests = Seen::default();
    let cut = "Here is the whole plan: first";
    setup.faux.set_responses(vec![
        reply(&requests, vec![faux_text(cut)], StopReason::Length),
        reply(&requests, vec![faux_text("Done.")], StopReason::Stop),
    ]);
    assert_eq!(
        (settle(&setup).await, seen(&requests)),
        (
            (
                (SubmissionStatus::Done, None, None),
                vec![
                    user(ASK),
                    format!("assistant:{cut}"),
                    "assistant:Done.".to_owned()
                ]
            ),
            vec![user(ASK), cut_note(2, 1)]
        )
    );
}

#[tokio::test]
async fn a_reply_of_only_thinking_is_no_answer_and_the_run_goes_on() {
    let setup = setup_with_pending(true);
    let requests = Seen::default();
    setup.faux.set_responses(vec![
        reply(&requests, vec![faux_thinking(THINKING)], StopReason::Stop),
        reply(&requests, vec![faux_text("Done.")], StopReason::Stop),
    ]);
    let note = user(
        "Harness note, attempt 2: your previous reply gave no text and no tool call. Give the \
         answer again, as text or as a tool call.",
    );
    assert_eq!(
        (settle(&setup).await, seen(&requests)),
        (
            (
                (SubmissionStatus::Done, None, None),
                vec![
                    user(ASK),
                    "assistant:".to_owned(),
                    "assistant:Done.".to_owned()
                ]
            ),
            vec![user(ASK), note]
        )
    );
}

/// The round note of a run capped at 3 rounds, `left` rounds left.
fn round_note(left: u32) -> String {
    let rounds =
        match left {
            0 => return user(
                "Harness note: no tool round remains in this turn (maxToolRounds 3): a tool call \
                 now ends the turn unfinished at the cap. End with a final answer that states \
                 what is done and exactly what remains.",
            ),
            1 => "1 tool round remains in this turn (maxToolRounds 3). Use it for the remaining \
              work; if the work cannot finish in it"
                .to_owned(),
            2..=u32::MAX => format!(
                "{left} tool rounds remain in this turn (maxToolRounds 3). Use them for the \
             remaining work; if the work cannot finish in them"
            ),
        };
    user(&format!(
        "Harness note: {rounds}, end with a final answer that states what is done and exactly \
         what remains."
    ))
}

#[tokio::test]
async fn each_request_near_the_round_cap_tells_the_model_the_rounds_left() {
    let setup = setup_with_pending(false);
    setup
        .settings
        .update(|settings| settings.max_tool_rounds = Some(3));
    let requests = Seen::default();
    setup.faux.set_responses(vec![
        reply(&requests, vec![tick("c0")], StopReason::ToolUse),
        reply(&requests, vec![tick("c1")], StopReason::ToolUse),
        reply(&requests, vec![faux_text("Done.")], StopReason::Stop),
    ]);
    let ((status, reason, detail), _) = settle(&setup).await;
    assert_eq!(
        ((status, reason, detail), seen(&requests)),
        (
            (SubmissionStatus::Done, None, None::<JsonValue>),
            vec![round_note(2), round_note(1), round_note(0)]
        )
    );
}
