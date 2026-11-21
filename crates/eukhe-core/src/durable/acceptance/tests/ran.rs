//! The intent judge reads the commands the run executed, as the harness
//! recorded them: a final answer that says the tests ran stands only when
//! that record shows them run and ending as required.

use super::*;

/// A response that runs `script` with the `bash` stand-in: it exits with
/// `status` and prints `output`.
fn bash(id: &str, script: &str, status: i64, output: &str) -> FauxResponseStep {
    let mut args = JsonObject::new();
    args.insert("script".to_owned(), json!(script));
    args.insert("status".to_owned(), json!(status));
    args.insert("output".to_owned(), json!(output));
    faux_assistant_message(
        faux_tool_call("bash", args, Some(id.to_owned())),
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )
    .into()
}

/// What the judge needs to see to hold that the tests ran green.
const TESTS_RAN: &str = "step 1 `pytest -q` exited 0";

/// The header of the commands the judge reads.
const RAN: &str = "Commands the worker ran with the `bash` tool, as the harness recorded them (oldest first; each step with its exit status):";

/// V6: a task whose answer says the tests ran passes its intent check when
/// the record shows them run with exit 0: the judge reads each step with
/// its exit status and the output's tail, never the worker's answer.
#[tokio::test]
async fn a_task_whose_tests_ran_passes_its_intent_check() {
    let setup = setup();
    let (harness, root) = setup.memory().await;
    setup
        .accept(&harness, &root, vec![CheckSpec::intent()], Some(1))
        .await;
    *setup.judge.reads_for.lock().expect("the judge") = Some(TESTS_RAN.to_owned());
    setup.faux.set_responses(vec![
        bash("b1", "pytest -q", 0, "3 passed in 0.02s"),
        answer("WORKER-SUMMARY: pytest ran, 3 passed"),
    ]);

    run(&harness, &root, "run the tests with pytest").await;

    let requests = judge_requests(&setup);
    let evidence = &requests[0].evidence;
    assert!(
        evidence.contains(&format!(
            "{RAN}\n--- bash run\nstep 1 `pytest -q` exited 0\nthe script ended with status 0\noutput:\n3 passed in 0.02s"
        )),
        "{evidence}"
    );
    assert!(
        !judge_prompt(&requests[0]).contains("WORKER-SUMMARY"),
        "{evidence}"
    );
    let got = state(&harness, &root).await;
    assert_eq!(
        (
            got.label,
            got.checks[0].result.as_ref().map(|result| result.verdict),
            requests.len()
        ),
        (
            AcceptanceLabel::ChecksPassedNotCertified,
            Some(CheckVerdict::Confirmed),
            1
        )
    );
    harness.close(cx()).await.expect("close");
}

/// V6: a task whose answer says the tests ran fails its intent check when
/// the record shows they did not run (only `ls` ran), and still when they
/// ran and failed: the answer's word never stands in for the record.
#[tokio::test]
async fn a_task_whose_tests_did_not_run_fails_its_intent_check() {
    let setup = setup();
    let (harness, root) = setup.memory().await;
    setup
        .accept(&harness, &root, vec![CheckSpec::intent()], Some(1))
        .await;
    *setup.judge.reads_for.lock().expect("the judge") = Some(TESTS_RAN.to_owned());
    setup.faux.set_responses(vec![
        bash("b1", "ls", 0, "parser.py"),
        answer("pytest ran, 3 passed"),
        bash("b2", "pytest -q", 1, "1 failed, 2 passed"),
        answer("pytest ran, all green"),
    ]);

    run(&harness, &root, "run the tests with pytest").await;

    let requests = judge_requests(&setup);
    assert_eq!(requests.len(), 2);
    let first = &requests[0].evidence;
    assert!(
        first.contains(&format!(
            "{RAN}\n--- bash run\nstep 1 `ls` exited 0\nthe script ended with status 0\noutput:\nparser.py"
        )),
        "{first}"
    );
    assert!(!first.contains("pytest"), "{first}");
    let second = &requests[1].evidence;
    assert!(
        second.contains("--- bash run\nstep 1 `ls` exited 0\nthe script ended with status 0\noutput:\nparser.py\n--- bash run\nstep 1 `pytest -q` exited 1\nthe script ended with status 1\noutput:\n1 failed, 2 passed"),
        "{second}"
    );
    let got = state(&harness, &root).await;
    assert_eq!(
        (got.label, got.last_end.map(|end| end.label)),
        (AcceptanceLabel::Failed, Some(AcceptanceLabel::Failed))
    );
    harness.close(cx()).await.expect("close");
}
