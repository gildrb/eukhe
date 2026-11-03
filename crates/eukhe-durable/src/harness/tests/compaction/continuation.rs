//! `Conversation::continuation` after a compaction: the side request's
//! prefix is the request the next turn sends.

use super::{
    compact, history, kinds, open, result, submission, submission_id, summary, turn, user_text,
    OpenOptions,
};
use crate::harness::tests::support::context;
use crate::types::{SubmissionStatus, TaskOutcome};

/// After an idle compaction the next turn writes the baseline system entry
/// under the new head. The continuation appends it first, so its messages
/// are the next turn's request up to the turn's input, and its options are
/// the turn's: the provider sees one prefix.
#[tokio::test]
async fn a_continuation_after_a_compaction_is_the_next_turns_prefix() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    chat.faux.summary(summary("SUMMARY"));
    let id = compact(&chat, None).await;
    let outcome = result(&chat, id).await;
    assert!(matches!(outcome, TaskOutcome::Completed { .. }));
    let placed = submission(&chat, submission_id(&outcome))
        .await
        .wait(context())
        .await
        .unwrap();
    assert_eq!(placed.state.status(), SubmissionStatus::Done);

    let continuation = chat
        .root
        .continuation(context())
        .await
        .unwrap()
        .expect("the conversation has a model");
    turn(&chat, "u4", "a4").await;

    let requests = chat.faux.agent_requests();
    let next = requests.last().expect("the turn's request");
    let prefix = continuation.messages.len();
    assert_eq!(next.messages[..prefix], continuation.messages[..]);
    assert_eq!(next.messages.len(), prefix + 1);
    assert_eq!(user_text(next.messages.last()), "u4");
    let options = next.options.as_ref().expect("the turn's options");
    assert_eq!(
        (
            &options.stream.session_id,
            options.reasoning,
            &options.stream.system_cache_breakpoint,
            options.stream.cache_retention,
        ),
        (
            &continuation.options.stream.session_id,
            continuation.options.reasoning,
            &continuation.options.stream.system_cache_breakpoint,
            continuation.options.stream.cache_retention,
        )
    );
    // The turn found the baseline the continuation wrote and wrote none.
    let kinds = kinds(&chat.root).await;
    let after_marker = kinds
        .iter()
        .rposition(|kind| kind == "pi.compaction")
        .expect("the summary entry");
    assert_eq!(
        kinds[after_marker..]
            .iter()
            .filter(|kind| *kind == "pi.system")
            .count(),
        1
    );
}
