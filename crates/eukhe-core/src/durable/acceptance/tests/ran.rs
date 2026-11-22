//! The intent judge reads the commands the run executed, as the harness
//! recorded them: a final answer that says the tests ran stands only when
//! that record shows them run and ending as required, whether the `bash`
//! tool ran them or a python cell's `bash()`.

use super::*;

/// A response that calls the stand-in `tool` with `args`.
fn call_with(tool: &str, id: &str, args: Value) -> FauxResponseStep {
    let Value::Object(args) = args else {
        panic!("tool args are an object")
    };
    faux_assistant_message(
        faux_tool_call(tool, args, Some(id.to_owned())),
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )
    .into()
}

/// A response that runs `script` with the `bash` stand-in: it exits with
/// `status` and prints `output`.
fn bash(id: &str, script: &str, status: i64, output: &str) -> FauxResponseStep {
    call_with(
        "bash",
        id,
        json!({ "script": script, "status": status, "output": output }),
    )
}

/// A response that runs a python cell whose `await bash(command)` exits
/// with `exit_code` and prints `output`.
fn cell_bash(id: &str, command: &str, exit_code: i64, output: &str) -> FauxResponseStep {
    call_with(
        "python",
        id,
        json!({ "command": command, "exit_code": exit_code, "output": output }),
    )
}

/// What the judge needs to see to hold that the tests ran green.
const TESTS_RAN: &str = "`pytest -q` exited 0";

/// The header of the commands the judge reads.
const RAN: &str = "Commands the worker ran, as the harness recorded them (oldest first; each with its exit status):";

/// The intent check of a task that asks for the tests, with the judge
/// passing exactly when the evidence shows them run green.
async fn tests_task(setup: &Setup, harness: &Harness, root: &Conversation) {
    setup
        .accept(harness, root, vec![CheckSpec::intent()], Some(1))
        .await;
    *setup.judge.reads_for.lock().expect("the judge") = Some(TESTS_RAN.to_owned());
}

/// The label and verdict the intent check ended with, and how many times
/// the judge was asked.
async fn outcome(
    setup: &Setup,
    harness: &Harness,
    root: &Conversation,
) -> (AcceptanceLabel, Option<CheckVerdict>, usize) {
    let got = state(harness, root).await;
    (
        got.label,
        got.checks[0].result.as_ref().map(|result| result.verdict),
        judge_requests(setup).len(),
    )
}

/// V6: a task whose answer says the tests ran passes its intent check when
/// the record shows the `bash` tool ran them with exit 0: the judge reads
/// each step with its exit status and the output's tail, never the
/// worker's answer.
#[tokio::test]
async fn a_task_whose_tests_ran_passes_its_intent_check() {
    let setup = setup();
    let (harness, root) = setup.memory().await;
    tests_task(&setup, &harness, &root).await;
    setup.faux.set_responses(vec![
        bash("b1", "pytest -q", 0, "3 passed in 0.02s"),
        answer("WORKER-SUMMARY: pytest ran, 3 passed"),
    ]);

    run(&harness, &root, "run the tests with pytest").await;

    let requests = judge_requests(&setup);
    let evidence = &requests[0].evidence;
    assert!(
        evidence.contains(&format!(
            "{RAN}\n--- `bash` tool run\nstep 1 `pytest -q` exited 0\nthe script ended with status 0\noutput:\n3 passed in 0.02s"
        )),
        "{evidence}"
    );
    assert!(
        !judge_prompt(&requests[0]).contains("WORKER-SUMMARY"),
        "{evidence}"
    );
    assert_eq!(
        outcome(&setup, &harness, &root).await,
        (
            AcceptanceLabel::ChecksPassedNotCertified,
            Some(CheckVerdict::Confirmed),
            1
        )
    );
    harness.close(cx()).await.expect("close");
}

/// V6: a task whose tests ran in a python cell (`await bash("pytest -q")`)
/// with exit 0 passes its intent check: the cell's result records the
/// process with its exit code and output tail, and the judge reads it.
#[tokio::test]
async fn a_task_whose_tests_ran_in_a_python_cell_passes_its_intent_check() {
    let setup = setup();
    let (harness, root) = setup.memory().await;
    tests_task(&setup, &harness, &root).await;
    setup.faux.set_responses(vec![
        cell_bash("p1", "pytest -q", 0, "4 passed in 0.03s"),
        answer("WORKER-SUMMARY: pytest ran, 4 passed"),
    ]);

    run(&harness, &root, "run the tests with pytest").await;

    let evidence = &judge_requests(&setup)[0].evidence;
    assert!(
        evidence.contains(&format!(
            "{RAN}\n--- `bash()` in a python cell\n`pytest -q` exited 0\noutput:\n4 passed in 0.03s"
        )),
        "{evidence}"
    );
    assert_eq!(
        outcome(&setup, &harness, &root).await,
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
    tests_task(&setup, &harness, &root).await;
    setup.faux.set_responses(vec![
        bash("b1", "ls", 0, "parser.py"),
        answer("pytest ran, 3 passed"),
        cell_bash("p1", "pytest -q", 1, "1 failed, 2 passed"),
        answer("pytest ran, all green"),
    ]);

    run(&harness, &root, "run the tests with pytest").await;

    let requests = judge_requests(&setup);
    assert_eq!(requests.len(), 2);
    let first = &requests[0].evidence;
    assert!(
        first.contains(&format!(
            "{RAN}\n--- `bash` tool run\nstep 1 `ls` exited 0\nthe script ended with status 0\noutput:\nparser.py"
        )),
        "{first}"
    );
    assert!(!first.contains("pytest"), "{first}");
    let second = &requests[1].evidence;
    assert!(
        second.contains("--- `bash` tool run\nstep 1 `ls` exited 0\nthe script ended with status 0\noutput:\nparser.py\n--- `bash()` in a python cell\n`pytest -q` exited 1\noutput:\n1 failed, 2 passed"),
        "{second}"
    );
    let got = state(&harness, &root).await;
    assert_eq!(
        (got.label, got.last_end.map(|end| end.label)),
        (AcceptanceLabel::Failed, Some(AcceptanceLabel::Failed))
    );
    harness.close(cx()).await.expect("close");
}
