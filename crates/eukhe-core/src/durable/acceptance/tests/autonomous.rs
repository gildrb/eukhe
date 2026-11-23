//! An autonomous run's checks on a real Harness with faux models: the
//! claim the checks end stops the run with its label, unless it passed
//! and the final answer states work left.

use eukhe_types::budget::BudgetLimits;

use super::*;
use crate::autonomous::{AgentAutonomousConfig, AgentAutonomousGateConfig, AutonomousStop};
use crate::durable::autonomous::{autonomous_state, set_autonomous, AutonomousChange};
use crate::durable::budget::wrap_models_with_budget;
use crate::durable::directors::{left_continuation, run_left, DIRECTOR_NOTICE_CUSTOM_TYPE};

/// AU1, AU2: the commands of an autonomous run's removed gates are command
/// checks beside the intent check; a refuted claim goes back to the worker
/// with its evidence (the checks' return: no continuation of the run's
/// own), and the claim the checks end stops the run with its label.
#[tokio::test]
async fn an_autonomous_run_stops_when_its_checks_end_the_claim() {
    let setup = setup();
    let (harness, root) = setup.memory().await;
    set_autonomous(
        &harness,
        &setup.budget,
        root.id(),
        AutonomousChange::On(AgentAutonomousConfig {
            gates: Some(AgentAutonomousGateConfig {
                commands: Some(vec!["make test".to_owned()]),
                ..AgentAutonomousGateConfig::default()
            }),
            ..AgentAutonomousConfig::default()
        }),
        setup.cwd(),
        cx(),
    )
    .await
    .expect("autonomous on");
    let specs: Vec<CheckSpec> = state(&harness, &root)
        .await
        .checks
        .into_iter()
        .map(|check| check.spec)
        .collect();
    assert_eq!(specs, vec![command("make test"), CheckSpec::intent()]);
    setup
        .runner
        .script(vec![exited(1, "1 failed"), exited(0, "ok")]);
    setup.judge.replies.lock().expect("replies").extend([
        JudgeReply::Text("PASS\n1. the tests: make test".to_owned()),
        JudgeReply::Text("PASS\n1. the tests: make test".to_owned()),
    ]);
    setup.faux.set_responses(vec![
        answer("done"),
        call("work", "w1"),
        answer("fixed"),
        answer("unused"),
    ]);

    run(&harness, &root, "make the tests pass").await;

    let entries = entries(&root).await;
    assert_eq!(
        user_origins(&entries),
        vec![InputOrigin::User, InputOrigin::Director]
    );
    assert!(
        user_texts(&entries)[1].contains("1. command `make test` (expect exit 0): refuted"),
        "{:?}",
        user_texts(&entries)
    );
    assert_eq!(
        setup.runner.commands(),
        vec!["make test".to_owned(), "make test".to_owned()]
    );
    assert_eq!(
        state(&harness, &root).await.label,
        AcceptanceLabel::ChecksPassedUnconfined
    );
    let run = autonomous_state(&harness, root.id(), cx())
        .await
        .expect("the run reads");
    assert_eq!(
        (run.enabled, run.continuations_used, run.last_stop),
        (
            true,
            0,
            Some(AutonomousStop::Checks(
                AcceptanceLabel::ChecksPassedUnconfined
            ))
        )
    );
    assert_eq!(setup.faux.get_pending_response_count(), 1);
    harness.close(cx()).await.expect("close");
}

/// AU7: a passed intent check does not end an autonomous run whose final
/// answer names a failing test: the final-answer judge reads the answer,
/// and the run goes on with one Director step that lists the work left;
/// once the answer states no work left, the claim stops the run with its
/// label.
#[tokio::test]
async fn a_passing_claim_whose_answer_states_work_left_goes_on() {
    let setup = setup();
    let (harness, root) = setup.memory().await;
    set_autonomous(
        &harness,
        &setup.budget,
        root.id(),
        AutonomousChange::On(AgentAutonomousConfig::default()),
        setup.cwd(),
        cx(),
    )
    .await
    .expect("autonomous on");
    let left = "Six tests pass, but one currently fails: test_cli. The implementation still needs a fix and a passing `python -m pytest` run.";
    let done = "Fixed test_cli; `python -m pytest` passes all seven tests.";
    setup.judge.replies.lock().expect("replies").extend([
        JudgeReply::Text("PASS\n1. a todo CLI: todo/".to_owned()),
        JudgeReply::Text("FAIL\n- test_cli fails".to_owned()),
        JudgeReply::Text("PASS\n1. a todo CLI: todo/".to_owned()),
        JudgeReply::Text("PASS".to_owned()),
    ]);
    setup.faux.set_responses(vec![
        answer(left),
        call("work", "w1"),
        answer(done),
        answer("unused"),
    ]);

    run(&harness, &root, "build the todo CLI").await;

    let entries = entries(&root).await;
    assert_eq!(
        user_origins(&entries),
        vec![InputOrigin::User, InputOrigin::Director]
    );
    assert_eq!(
        user_texts(&entries)[1],
        left_continuation(&["test_cli fails".to_owned()])
    );
    // One display row tells the user the run went on; the model never sees it.
    assert_eq!(
        custom_rows(&entries, DIRECTOR_NOTICE_CUSTOM_TYPE),
        vec![(
            "The final answer left task work undone (test_cli fails); the run went on.".to_owned(),
            false,
            json!({ "workLeft": ["test_cli fails"] })
        )]
    );
    let requests = judge_requests(&setup);
    let intent = JudgeQuestion::Intent(vec!["build the todo CLI".to_owned()]);
    assert_eq!(
        requests
            .iter()
            .map(|request| request.question.clone())
            .collect::<Vec<_>>(),
        vec![
            intent.clone(),
            JudgeQuestion::WorkLeft,
            intent,
            JudgeQuestion::WorkLeft
        ]
    );
    assert_eq!(
        requests
            .iter()
            .filter(|request| request.question == JudgeQuestion::WorkLeft)
            .map(|request| request.evidence.as_str())
            .collect::<Vec<_>>(),
        vec![left, done]
    );
    let label = state(&harness, &root).await.label;
    let run = autonomous_state(&harness, root.id(), cx())
        .await
        .expect("the run reads");
    assert_eq!(
        (run.enabled, run.continuations_used, run.last_stop),
        (true, 1, Some(AutonomousStop::Checks(label)))
    );
    assert_eq!(setup.faux.get_pending_response_count(), 1);
    harness.close(cx()).await.expect("close");
}

/// AU7 and the run's report: the work a passing claim's answer states left
/// is what the run found left of its task, and the next answer, which the
/// used-up budget leaves unread, keeps it: the run that ends on its budget
/// reports that work at its end.
#[tokio::test]
async fn a_run_that_ends_on_its_budget_reports_the_work_its_answer_left() {
    let setup = setup();
    wrap_models_with_budget(&setup.models, &setup.budget);
    let (harness, root) = setup.memory().await;
    set_autonomous(
        &harness,
        &setup.budget,
        root.id(),
        AutonomousChange::On(AgentAutonomousConfig::default()),
        setup.cwd(),
        cx(),
    )
    .await
    .expect("autonomous on");
    // Three model requests: the answer, the work, the next answer.
    setup
        .budget
        .set(BudgetLimits {
            requests: Some(3),
            ..BudgetLimits::default()
        })
        .expect("the budget is set");
    setup.judge.replies.lock().expect("replies").extend([
        JudgeReply::Text("PASS\n1. a todo CLI: todo/".to_owned()),
        JudgeReply::Text("FAIL\n- test_cli fails\n- the README".to_owned()),
        JudgeReply::Text("PASS\n1. a todo CLI: todo/".to_owned()),
    ]);
    setup.faux.set_responses(vec![
        answer("Six tests pass; test_cli fails and the README is not written."),
        call("work", "w1"),
        answer("test_cli is half fixed."),
        answer("unused"),
    ]);

    run(&harness, &root, "build the todo CLI").await;

    let run = autonomous_state(&harness, root.id(), cx())
        .await
        .expect("the run reads");
    assert_eq!(
        (
            user_origins(&entries(&root).await),
            judge_requests(&setup)
                .iter()
                .filter(|request| request.question == JudgeQuestion::WorkLeft)
                .count(),
            setup
                .budget
                .report()
                .and_then(|report| report.short)
                .is_some(),
            run.continuations_used,
            run_left(&harness, &root, cx()).await.expect("read"),
        ),
        (
            vec![InputOrigin::User, InputOrigin::Director],
            1,
            true,
            1,
            Some(vec!["test_cli fails".to_owned(), "the README".to_owned()]),
        )
    );
    assert_eq!(setup.faux.get_pending_response_count(), 1);
    harness.close(cx()).await.expect("close");
}
