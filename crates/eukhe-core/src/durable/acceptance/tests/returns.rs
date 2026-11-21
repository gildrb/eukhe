//! Returns: a refuted claim goes back to the worker while returns remain,
//! then ends failed, and the closing line counts the returns it made.

use super::*;
use crate::durable::acceptance::format_acceptance_status;

/// V7, V10: a refuted claim takes its evidence back to the worker while
/// returns remain, then ends failed; the run never ends as success. A
/// check that judged the state is not run again while the state stands.
#[tokio::test]
async fn a_refuted_claim_returns_its_evidence_then_ends_failed() {
    let setup = setup();
    let (harness, root) = setup.memory().await;
    setup
        .accept(&harness, &root, vec![command("cargo test")], Some(2))
        .await;
    setup.runner.script(vec![exited(1, "2 tests failed")]);
    setup.faux.set_responses(vec![
        answer("done"),
        answer("it is done, really"),
        answer("nothing to fix"),
    ]);

    run(&harness, &root, "do it").await;

    let entries = entries(&root).await;
    let texts = user_texts(&entries);
    assert_eq!(texts.len(), 3, "{texts:?}");
    assert_eq!(
        texts[1],
        "[acceptance: not verified] The harness checked your claim that the task is done: an acceptance check failed or could not judge the current state (return 1 of 2).\n\n1. command `cargo test` (expect exit 0): refuted: exited with code 1\n\n<evidence>\n2 tests failed\n</evidence>\n\nFix the work so that every check passes (a check that could not judge, e.g. a timeout, runs again too), then finish again. Every check runs again on the final state; only the task's owner sets checks."
    );
    assert!(texts[2].contains("(return 2 of 2)"), "{}", texts[2]);
    assert_eq!(
        user_origins(&entries),
        vec![
            InputOrigin::User,
            InputOrigin::Director,
            InputOrigin::Director
        ]
    );
    let rows: Vec<String> = verdict_rows(&entries)
        .into_iter()
        .map(|(text, _, _)| text)
        .collect();
    assert_eq!(
        rows,
        vec![
            "Acceptance not verified: check 1 refuted (exited with code 1). Returned to the worker (1 of 2).".to_owned(),
            "Acceptance not verified: check 1 refuted (exited with code 1). Returned to the worker (2 of 2).".to_owned(),
            "Acceptance failed: check 1 refuted (exited with code 1).".to_owned(),
        ]
    );
    let got = state(&harness, &root).await;
    assert_eq!(
        (
            got.label,
            got.claimed,
            got.tries,
            got.last_end.map(|end| end.label)
        ),
        (
            AcceptanceLabel::Failed,
            false,
            0,
            Some(AcceptanceLabel::Failed)
        )
    );
    // The state never moved: the check ran once.
    assert_eq!(setup.runner.commands(), vec!["cargo test".to_owned()]);
    assert_eq!(
        acceptance_exit_code(&harness, root.id(), 0, cx())
            .await
            .expect("exit"),
        1
    );
    // A new message of the user moves the state: the next final answer is
    // a new claim, judged again on that state.
    setup.runner.script(vec![exited(1, "2 tests failed")]);
    setup.faux.set_responses(vec![
        answer("you are welcome"),
        answer("still nothing to fix"),
        answer("still nothing to fix"),
    ]);
    run(&harness, &root, "thanks anyway").await;
    let texts = user_texts(&self::entries(&root).await);
    assert_eq!(texts[3], "thanks anyway");
    assert_eq!(state(&harness, &root).await.label, AcceptanceLabel::Failed);
    assert_eq!(
        setup.runner.commands(),
        vec!["cargo test".to_owned(), "cargo test".to_owned()]
    );
    harness.close(cx()).await.expect("close");
}

/// The closing line counts the returns the ended claim made: a claim that
/// went back 3 times, then ended failed, says 3 of 3, though the end
/// clears the count the state carries.
#[tokio::test]
async fn the_closing_line_counts_the_returns_a_failed_claim_made() {
    let setup = setup();
    let (harness, root) = setup.memory().await;
    setup
        .accept(&harness, &root, vec![command("cargo test")], None)
        .await;
    setup.runner.script(vec![exited(1, "2 tests failed")]);
    setup.faux.set_responses(vec![
        answer("done"),
        answer("done"),
        answer("done"),
        answer("done"),
    ]);

    run(&harness, &root, "do it").await;

    let got = state(&harness, &root).await;
    assert_eq!(
        (
            got.tries,
            got.last_end.as_ref().map(|end| (end.label, end.returns))
        ),
        (0, Some((AcceptanceLabel::Failed, 3)))
    );
    let status = format_acceptance_status(&got).expect("the status");
    assert_eq!(
        status.lines().next(),
        Some("Acceptance: failed (revision 1, returns 3 of 3).")
    );
    harness.close(cx()).await.expect("close");
}
