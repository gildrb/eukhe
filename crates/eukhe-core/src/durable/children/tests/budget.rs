//! A child's budget (spec/README.md B4): a child spawned without a budget
//! carves nothing and draws from its parent's account as a shared member;
//! a spawn batch that names budgets is carved all or none before a child
//! starts; a child that ended gives its budget back (an allotment returns
//! what it left and its spend, a shared member leaves the account); a
//! child tasked again joins again; a parent that opens gives back what no
//! task serves; and a parent with no budget spawns as before.

use eukhe_budget::{CarveOutcome, Ledger, Member, Reserved, Use, REQUEST_MIN_MS};
use eukhe_types::budget::{BudgetAmounts, BudgetLimits, BudgetPhase, BudgetReport};

use super::worker::{call_tool, say};
use super::*;
use crate::durable::children::budget::named_budget;
use crate::durable::children::reconcile;

/// A session whose budget gate keeps its ledgers under `agent_dir`.
fn setup_in(agent_dir: &std::path::Path) -> Setup {
    Setup {
        budget: BudgetGate::open(agent_dir, PARENT_SESSION_ID, None, default_settings()),
        ..setup()
    }
}

fn cost(cost_micros: u64) -> BudgetAmounts {
    BudgetAmounts {
        cost_micros,
        ..BudgetAmounts::default()
    }
}

fn cost_limit(cost_micros: u64) -> BudgetLimits {
    BudgetLimits {
        cost_micros: Some(cost_micros),
        ..BudgetLimits::default()
    }
}

/// The ledger of `session_id` under `agent_dir`.
fn ledger(agent_dir: &std::path::Path, session_id: &str) -> Ledger {
    Ledger::of(&agent_dir.join("budgets"), session_id)
}

/// The budget of `session_id` as its ledger under `agent_dir` shows it to
/// that agent.
fn ledger_report(agent_dir: &std::path::Path, session_id: &str) -> Option<BudgetReport> {
    ledger(agent_dir, session_id).report(session_id).unwrap()
}

/// The parent's report: its account limited to `limits` in cost.
fn parent_report(limit: u64, free: u64, spent: u64, lent: u64) -> BudgetReport {
    BudgetReport {
        session_id: PARENT_SESSION_ID.to_owned(),
        agent_session_id: PARENT_SESSION_ID.to_owned(),
        limits: cost_limit(limit),
        free: cost(free),
        spent: cost(spent),
        lent: cost(lent),
        ..BudgetReport::default()
    }
}

/// The parent account's shared members other than the parent.
fn shared(agent_dir: &std::path::Path) -> Vec<String> {
    ledger(agent_dir, PARENT_SESSION_ID)
        .members()
        .unwrap()
        .into_iter()
        .filter(|(_, member)| member.parent.as_deref() == Some(PARENT_SESSION_ID))
        .map(|(child, _)| child)
        .collect()
}

fn answered() -> RlmChildRunState {
    RlmChildRunState::Answered {
        answer_preview: Some("done".to_owned()),
    }
}

/// B4: children spawned without a budget carve nothing: the parent lends
/// nothing, no child gets an account of its own, and a child's session
/// joins the parent's account when it opens (it sees the account's free
/// amount as its own).
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn children_without_a_budget_draw_from_the_parents_account() {
    let agent_dir = tempfile::tempdir().unwrap();
    let setup = setup_in(agent_dir.path());
    setup.budget.set(cost_limit(1_000_000)).unwrap();
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let task = |name: &str| json!({ "prompt": format!("do {name}"), "kwargs": { "name": name, "why": "parallel" } });

    spawn_batch_turn(&opened, &setup, json!([task("a"), task("b")])).await;

    let rows: Vec<ChildRow> = read_children(&opened.harness, ROOT_CONVERSATION_ID, cx())
        .await
        .unwrap()
        .children
        .into_values()
        .collect();
    let first = &rows[0].session_id;
    let child = BudgetGate::open(
        agent_dir.path(),
        first,
        Some(PARENT_SESSION_ID),
        default_settings(),
    );
    assert_eq!(
        (
            rows.iter()
                .map(|row| row.session_name.as_str())
                .collect::<Vec<_>>(),
            ledger_report(agent_dir.path(), PARENT_SESSION_ID),
            ledger(agent_dir.path(), first).is_owner(),
            child.report(),
        ),
        (
            vec!["a", "b"],
            Some(parent_report(1_000_000, 1_000_000, 0, 0)),
            false,
            Some(BudgetReport {
                session_id: PARENT_SESSION_ID.to_owned(),
                agent_session_id: first.clone(),
                limits: cost_limit(1_000_000),
                free: cost(1_000_000),
                ..BudgetReport::default()
            }),
        )
    );
    opened.root.wait_for_idle(cx()).await.unwrap();
    opened.harness.close(cx()).await.unwrap();
}

/// B4: a spawn that names a budget carves exactly that allotment for its
/// child out of the parent's account: the parent lends it, the child's
/// own account holds it.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_named_budget_is_carved_for_its_child() {
    let agent_dir = tempfile::tempdir().unwrap();
    let setup = setup_in(agent_dir.path());
    setup.budget.set(cost_limit(1_000_000)).unwrap();
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let task = json!({ "prompt": "do a", "kwargs": { "name": "a", "why": "parallel", "budget": { "cost_usd": 0.25 } } });

    spawn_batch_turn(&opened, &setup, json!([task])).await;

    let row = read_children(&opened.harness, ROOT_CONVERSATION_ID, cx())
        .await
        .unwrap()
        .children
        .into_values()
        .next()
        .expect("the child");
    assert_eq!(
        (
            ledger_report(agent_dir.path(), PARENT_SESSION_ID),
            ledger_report(agent_dir.path(), &row.session_id),
        ),
        (
            Some(parent_report(1_000_000, 750_000, 0, 250_000)),
            Some(BudgetReport {
                session_id: row.session_id.clone(),
                agent_session_id: row.session_id.clone(),
                limits: cost_limit(250_000),
                free: cost(250_000),
                parent_session_id: Some(PARENT_SESSION_ID.to_owned()),
                ..BudgetReport::default()
            }),
        )
    );
    opened.root.wait_for_idle(cx()).await.unwrap();
    opened.harness.close(cx()).await.unwrap();
}

/// B4: a batch whose named allotments do not fit is refused with the
/// budget text; nothing stays carved and no child is admitted.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_batch_that_does_not_fit_carves_nothing_and_is_refused() {
    let agent_dir = tempfile::tempdir().unwrap();
    let setup = setup_in(agent_dir.path());
    let set = setup.budget.set(cost_limit(1_000_000)).unwrap();
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    // Each names 0.60 dollars of the parent's 1.00: the first fits, the
    // second does not, so the first goes back.
    let task = |name: &str| json!({ "prompt": format!("do {name}"), "kwargs": { "name": name, "why": "parallel", "budget": { "cost_usd": 0.6 } } });

    let reply = spawn_batch_turn(&opened, &setup, json!([task("a"), task("b")])).await;

    let admitted: Vec<String> = read_children(&opened.harness, ROOT_CONVERSATION_ID, cx())
        .await
        .unwrap()
        .children
        .values()
        .map(|row| row.session_name.clone())
        .collect();
    assert_eq!(
        (
            reply,
            admitted,
            host.spawn_keys(),
            ledger_report(agent_dir.path(), PARENT_SESSION_ID),
        ),
        (
            "error: Budget: the children's allotments do not fit what is left (cost)".to_owned(),
            Vec::new(),
            Vec::new(),
            Some(set),
        )
    );
    opened.root.wait_for_idle(cx()).await.unwrap();
    opened.harness.close(cx()).await.unwrap();
}

/// B4: when a carved child's task reaches its report, what the child has
/// free returns to the parent and the child's spend is the parent's.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_carved_child_that_ended_returns_what_it_left_and_its_spend() {
    let agent_dir = tempfile::tempdir().unwrap();
    let setup = setup_in(agent_dir.path());
    setup.budget.set(cost_limit(1_000_000)).unwrap();
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let task = json!({ "prompt": "do a", "kwargs": { "name": "a", "why": "parallel", "budget": { "cost_usd": 0.5 } } });
    spawn_batch_turn(&opened, &setup, json!([task])).await;
    let row = read_children(&opened.harness, ROOT_CONVERSATION_ID, cx())
        .await
        .unwrap()
        .children
        .into_values()
        .next()
        .expect("the child");
    eventually(|| async { !host.prompt_keys().is_empty() }).await;
    // The child spends 120_000 of the 500_000 it was carved.
    let child = ledger(agent_dir.path(), &row.session_id);
    let Reserved::Granted { reservation, .. } = child
        .reserve(
            &row.session_id,
            Use::Work,
            "model:test/m",
            BudgetAmounts::default(),
            BudgetAmounts::default(),
            &[cost(300_000)],
            REQUEST_MIN_MS,
        )
        .unwrap()
    else {
        panic!("the child's request fits its allotment");
    };
    child.settle(reservation.id, cost(120_000)).unwrap();

    setup.faux.append_responses(vec![answer("noted")]);
    host.settle(&row.session_id, answered(), None);
    opened
        .harness
        .wait_for_task(TaskId::<Value>::from_number(row.task_id), cx())
        .await
        .unwrap();
    opened.root.wait_for_idle(cx()).await.unwrap();

    assert_eq!(
        ledger_report(agent_dir.path(), PARENT_SESSION_ID),
        Some(parent_report(1_000_000, 880_000, 120_000, 0))
    );
    assert!(lock(&setup.reports).is_empty());
    opened.harness.close(cx()).await.unwrap();
}

/// B4: a shared child is in the account from its prompt on; when its task
/// ends it leaves the account (what it spent stays spent), and a child
/// tasked again joins again before the prompt goes out.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_shared_child_leaves_at_its_end_and_joins_again_when_tasked() {
    let agent_dir = tempfile::tempdir().unwrap();
    let setup = setup_in(agent_dir.path());
    setup.budget.set(cost_limit(1_000_000)).unwrap();
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    setup
        .faux
        .append_responses(vec![call_tool("worker_assign"), answer("handed")]);
    say(&opened, "build it").await;
    let worker = read_children(&opened.harness, ROOT_CONVERSATION_ID, cx())
        .await
        .unwrap()
        .children
        .values()
        .last()
        .cloned()
        .expect("the worker");
    eventually(|| async { host.prompt_keys().len() == 1 }).await;
    let prompted = shared(agent_dir.path());
    // The worker spends 120_000 from the shared account.
    let child = ledger(agent_dir.path(), &worker.session_id);
    let Reserved::Granted { reservation, .. } = child
        .reserve(
            &worker.session_id,
            Use::Work,
            "model:test/m",
            BudgetAmounts::default(),
            BudgetAmounts::default(),
            &[cost(300_000)],
            REQUEST_MIN_MS,
        )
        .unwrap()
    else {
        panic!("the worker's request fits the account");
    };
    child.settle(reservation.id, cost(120_000)).unwrap();
    setup.faux.append_responses(vec![answer("noted")]);
    host.settle(&worker.session_id, answered(), None);
    eventually(|| async {
        row_of(&opened.harness, worker.task_id)
            .await
            .is_some_and(|row| row.settled)
    })
    .await;
    opened.root.wait_for_idle(cx()).await.unwrap();
    let ended = (
        shared(agent_dir.path()),
        ledger_report(agent_dir.path(), PARENT_SESSION_ID),
    );

    host.settle(&worker.session_id, RlmChildRunState::Running, None);
    setup
        .faux
        .append_responses(vec![call_tool("worker_assign"), answer("handed again")]);
    say(&opened, "now the docs").await;
    eventually(|| async { host.prompt_keys().len() == 2 }).await;

    assert_eq!(
        (prompted, ended, shared(agent_dir.path())),
        (
            vec![worker.session_id.clone()],
            (
                Vec::new(),
                Some(parent_report(1_000_000, 880_000, 120_000, 0))
            ),
            vec![worker.session_id.clone()],
        )
    );
    opened.root.wait_for_idle(cx()).await.unwrap();
    opened.harness.close(cx()).await.unwrap();
}

/// B4: a carve whose spawn never committed and a shared member whose end
/// was never recorded (crashes in between) belong to children no task
/// serves: the parent's open gives their budget back, and leaves a
/// running child its own.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn an_open_gives_back_what_children_no_task_serves_hold() {
    let agent_dir = tempfile::tempdir().unwrap();
    let setup = setup_in(agent_dir.path());
    setup.budget.set(cost_limit(1_000_000)).unwrap();
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let task = json!({ "prompt": "do a", "kwargs": { "name": "a", "why": "parallel", "budget": { "cost_usd": 0.5 } } });
    spawn_batch_turn(&opened, &setup, json!([task])).await;
    let row = read_children(&opened.harness, ROOT_CONVERSATION_ID, cx())
        .await
        .unwrap()
        .children
        .into_values()
        .next()
        .expect("the child");
    eventually(|| async { !host.prompt_keys().is_empty() }).await;
    assert!(matches!(
        setup
            .budget
            .carve("lost-child", cost_limit(100_000))
            .unwrap(),
        CarveOutcome::Carved { .. }
    ));
    setup.budget.admit_child("lost-member").unwrap();

    reconcile(&setup.budget, &opened.harness, cx())
        .await
        .unwrap();

    assert_eq!(
        (
            ledger_report(agent_dir.path(), PARENT_SESSION_ID),
            setup.budget.lent_children().unwrap(),
            shared(agent_dir.path()),
        ),
        (
            Some(parent_report(1_000_000, 500_000, 0, 500_000)),
            vec![row.session_id],
            Vec::<String>::new(),
        )
    );
    opened.root.wait_for_idle(cx()).await.unwrap();
    opened.harness.close(cx()).await.unwrap();
}

/// B4: a parent with no budget spawns exactly as before: no ledger file
/// appears for it or its child, and the child's end reports nothing.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_parent_with_no_budget_spawns_without_a_ledger() {
    let agent_dir = tempfile::tempdir().unwrap();
    let setup = setup_in(agent_dir.path());
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let row = spawn_child(&opened, &setup).await;
    eventually(|| async { !host.prompt_keys().is_empty() }).await;
    setup.faux.append_responses(vec![answer("noted")]);
    host.settle(&row.session_id, answered(), None);
    opened
        .harness
        .wait_for_task(TaskId::<Value>::from_number(row.task_id), cx())
        .await
        .unwrap();
    opened.root.wait_for_idle(cx()).await.unwrap();

    assert_eq!(
        (
            row_of(&opened.harness, row.task_id)
                .await
                .map(|row| row.status),
            host.spawn_keys().len(),
            setup.budget.report(),
            ledger(agent_dir.path(), PARENT_SESSION_ID).exists(),
            ledger(agent_dir.path(), &row.session_id).exists(),
        ),
        (Some(ChildStatus::Done), 1, None, false, false)
    );
    assert!(lock(&setup.reports).is_empty());
    opened.harness.close(cx()).await.unwrap();
}

/// A shared member is a member of the parent's account with the parent
/// above it, working.
#[test]
fn a_joined_child_is_a_member_below_its_parent() {
    let agent_dir = tempfile::tempdir().unwrap();
    let parent = BudgetGate::open(
        agent_dir.path(),
        PARENT_SESSION_ID,
        None,
        default_settings(),
    );
    parent.set(cost_limit(1_000_000)).unwrap();
    parent.admit_child("child").unwrap();
    assert_eq!(
        parent.members().unwrap().get("child").cloned(),
        Some(Member {
            parent: Some(PARENT_SESSION_ID.to_owned()),
            keep: BudgetAmounts::default(),
            phase: BudgetPhase::Working,
            short: None,
        })
    );
}

/// The `budget` argument of a spawn reads dollars, tokens, seconds, tool
/// calls and requests, and refuses what is no amount.
#[test]
fn a_spawn_names_its_childs_budget_in_the_callers_units() {
    let named = |budget: Value| {
        let kwargs = json!({ "budget": budget });
        named_budget(kwargs.as_object().unwrap(), "rlm.spawn").map_err(|error| error.to_string())
    };
    assert_eq!(
        [
            named(
                json!({ "cost_usd": 1.25, "tokens": 2000, "time_s": 90, "tool_calls": 7, "requests": 12 })
            ),
            named(json!({})),
            named(json!({ "cost_usd": -1 })),
            named(json!({ "tokens": 1.5 })),
            named(json!({ "dollars": 1 })),
            named(json!("one dollar")),
        ],
        [
            Ok(Some(BudgetLimits {
                cost_micros: Some(1_250_000),
                tokens: Some(2000),
                time_ms: Some(90_000),
                tool_calls: Some(7),
                requests: Some(12),
            })),
            Ok(None),
            Err("rlm.spawn budget cost_usd must be a non-negative number".to_owned()),
            Err("rlm.spawn budget tokens must be a non-negative integer".to_owned()),
            Err("Unsupported rlm.spawn budget keys: dollars".to_owned()),
            Err(
                "rlm.spawn budget must be an object {cost_usd?, tokens?, time_s?, tool_calls?, requests?}"
                    .to_owned()
            ),
        ]
    );
}
