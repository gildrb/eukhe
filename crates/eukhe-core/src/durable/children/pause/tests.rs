//! The run pause on a real session: a pause lets the running tool call
//! finish and holds the next model request; messages that arrive while it
//! holds are kept and placed once, in arrival order, when a user's message
//! wakes the run, which goes on with its whole context.

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_durable::harness::types::{InputSubmissionDraft, WhenBusy};
use eukhe_durable::types::{EntryRecord, SubmissionStatus};
use eukhe_types::input_origin::InputOrigin;
use eukhe_types::pi_ai::{Message, UserContent, UserContentBlock};

use super::{PauseView, Wake};
use crate::durable::children::PauseAction;
use crate::durable::rlm::kernel_test_lock;
use crate::durable::rlm::tests::{
    entries, gated_cell, ipython, live_output, result_text, results, settle, submit, text,
    wait_for_live_output, Fixture,
};
use crate::durable::EukheSession;

/// The text of each user entry, in transcript order.
fn user_texts(all: &[EntryRecord]) -> Vec<String> {
    all.iter()
        .filter(|entry| entry.kind == "pi.user")
        .filter_map(|entry| {
            let Message::User(user) = entry.model.as_ref()?.first()? else {
                return None;
            };
            Some(match &user.content {
                UserContent::Text(text) => text.clone(),
                UserContent::Blocks(blocks) => blocks
                    .iter()
                    .filter_map(|block| match block {
                        UserContentBlock::Text(text) => Some(text.text.as_str()),
                        UserContentBlock::Image(_) => None,
                    })
                    .collect::<String>(),
            })
        })
        .collect()
}

/// Queue `text` as a steer of `origin` while the run is busy, then tell
/// the run pause it arrived.
async fn deliver(session: &EukheSession, text: &str, origin: InputOrigin, wake: Wake) {
    session
        .root()
        .submit(
            InputSubmissionDraft {
                when_busy: Some(WhenBusy::Steer),
                origin,
                ..InputSubmissionDraft::new(text)
            },
            &BACKGROUND_CONTEXT,
        )
        .await
        .expect("queued");
    session
        .deps()
        .run_pause
        .message(wake, &BACKGROUND_CONTEXT)
        .await
        .expect("the pause hears the message");
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_pause_finishes_the_running_call_holds_the_next_request_and_keeps_messages_in_order() {
    let _kernel = kernel_test_lock().await;
    let fixture = Fixture::new();
    let gate = fixture.dir.path().join("gate");
    fixture.faux.set_responses(vec![
        ipython("c1", &gated_cell(&gate, "6 * 7")),
        text("done"),
    ]);
    let session = fixture.open_configured(|_| {}).await;
    let pause = std::sync::Arc::clone(&session.deps().run_pause);
    let live = live_output(&session).await;
    let id = submit(&session, "go").await;
    wait_for_live_output(&live, "started\n").await;

    // Paused while the cell runs: the cell is not cancelled, it finishes.
    pause
        .set(PauseAction::Pause, &BACKGROUND_CONTEXT)
        .await
        .expect("paused");
    std::fs::write(&gate, "").expect("open the gate");
    let held = pause
        .subscribe()
        .wait_for(|view| view.held)
        .await
        .map(|view| *view)
        .expect("the run parks");
    assert_eq!(
        held,
        PauseView {
            paused: true,
            held: true
        }
    );
    // No new model request started.
    assert_eq!(fixture.faux.state().call_count, 1);

    // A note waits; the user's words wake the run.
    deliver(
        &session,
        "a note from a sibling",
        InputOrigin::User,
        Wake::Waits,
    )
    .await;
    assert_eq!(pause.view(), held);
    assert_eq!(fixture.faux.state().call_count, 1);
    deliver(&session, "the user's words", InputOrigin::User, Wake::Wakes).await;

    assert_eq!(settle(&session, id).await, SubmissionStatus::Done);
    let all = entries(&session).await;
    let results = results(&all);
    assert_eq!(
        results
            .iter()
            .map(|result| (result.is_error, result_text(result)))
            .collect::<Vec<_>>(),
        [(false, "started\n42".to_owned())]
    );
    // The run went on where it parked: one more request, which read the
    // kept messages once, in arrival order, after the call's result.
    assert_eq!(
        user_texts(&all),
        ["go", "a note from a sibling", "the user's words"]
    );
    assert_eq!(fixture.faux.state().call_count, 2);
    assert_eq!(pause.view(), PauseView::default());
    session.close(&BACKGROUND_CONTEXT).await.expect("close");
}
