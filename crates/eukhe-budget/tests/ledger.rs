//! The ledger against the requirements of spec/README.md B1-B11: nothing
//! is spent past a budget, a tree spends within its root's budget whether
//! its children share the root's account or are given their own, no child
//! takes the final-answer reserve of an agent above it, the deadline holds
//! across restarts, a crash neither doubles nor loses a spend, the
//! ledger's total is the sum of its settled spends.

use std::collections::BTreeMap;
use std::io::Write;
use std::path::Path;
use std::sync::atomic::{AtomicU64, Ordering};

use eukhe_budget::{
    Audit, CarveOutcome, Ledger, LedgerError, Member, ReclaimOutcome, Refusal, Reservation,
    Reserved, Use, REQUEST_MIN_MS, TOOL_MIN_MS,
};
use eukhe_types::budget::{
    BudgetAmounts, BudgetDimension, BudgetLimits, BudgetPhase, BudgetReport,
};

/// The time every ledger of these tests reads, unless a test moves its
/// own clock.
const T0: u64 = 1_800_000_000_000;

fn fixed() -> u64 {
    T0
}

fn at(dir: &Path, session_id: &str) -> Ledger {
    Ledger::of(dir, session_id).with_clock(fixed)
}

fn amounts(cost_micros: u64, tokens: u64, tool_calls: u64, requests: u64) -> BudgetAmounts {
    BudgetAmounts {
        cost_micros,
        tokens,
        time_ms: 0,
        tool_calls,
        requests,
    }
}

fn cost(cost_micros: u64) -> BudgetAmounts {
    amounts(cost_micros, 0, 0, 0)
}

fn timed(amounts: BudgetAmounts, time_ms: u64) -> BudgetAmounts {
    BudgetAmounts { time_ms, ..amounts }
}

fn cost_only(cost_micros: u64) -> BudgetLimits {
    BudgetLimits {
        cost_micros: Some(cost_micros),
        ..BudgetLimits::default()
    }
}

/// The report of a budget nothing was spent from, as `agent` sees it.
fn fresh(owner: &str, agent: &str, limits: BudgetLimits, free: BudgetAmounts) -> BudgetReport {
    BudgetReport {
        session_id: owner.to_owned(),
        agent_session_id: agent.to_owned(),
        limits,
        free,
        ..BudgetReport::default()
    }
}

fn granted(reserved: Reserved) -> Reservation {
    match reserved {
        Reserved::Granted { reservation, .. } => reservation,
        Reserved::Refused { refusal, .. } => panic!("refused: {refusal:?}"),
    }
}

fn refused(reserved: Reserved) -> (Refusal, BudgetReport) {
    match reserved {
        Reserved::Refused { refusal, report } => (refusal, report),
        Reserved::Granted { reservation, .. } => panic!("granted: {reservation:?}"),
    }
}

/// A final answer of `amount` (no time asked for) by `agent`.
fn try_final(ledger: &Ledger, agent: &str, amount: BudgetAmounts) -> Result<Reserved, LedgerError> {
    ledger.reserve(
        agent,
        Use::Final,
        "model:test/m",
        BudgetAmounts::default(),
        BudgetAmounts::default(),
        &[amount],
        0,
    )
}

fn final_answer(ledger: &Ledger, agent: &str, amount: BudgetAmounts) -> Reserved {
    try_final(ledger, agent, amount).unwrap()
}

/// free + held + spent + lent == limit + over in every limited spent
/// dimension (time is a deadline).
fn assert_balanced(report: &BudgetReport) {
    for dimension in BudgetDimension::ALL {
        let Some(limit) = report.limits.get(dimension) else {
            continue;
        };
        if dimension == BudgetDimension::Time {
            continue;
        }
        assert_eq!(
            report.free.get(dimension)
                + report.held.get(dimension)
                + report.spent.get(dimension)
                + report.lent.get(dimension),
            limit + report.over.get(dimension),
            "{dimension:?} of {report:?}"
        );
    }
}

/// The file replays to its states and its settled spends are its total.
fn assert_exact(ledger: &Ledger, records: u64, settled: BudgetAmounts) {
    assert_eq!(
        ledger.audit().unwrap(),
        Audit {
            records,
            settled,
            spent: settled,
            first_mismatch: None,
        }
    );
}

#[test]
fn a_request_is_reserved_before_it_spends_and_settles_at_its_actual_cost() {
    let dir = tempfile::tempdir().unwrap();
    let ledger = at(dir.path(), "root");
    assert!(!ledger.exists());
    assert_eq!(ledger.report("root").unwrap(), None);
    let limits = BudgetLimits {
        cost_micros: Some(1_000),
        tokens: Some(500),
        time_ms: Some(60_000),
        tool_calls: Some(3),
        requests: Some(10),
    };
    let open = BudgetReport {
        deadline_ms: Some(T0 + 60_000),
        ..fresh(
            "root",
            "root",
            limits,
            timed(amounts(1_000, 500, 3, 10), 60_000),
        )
    };
    assert_eq!(ledger.open_root(limits).unwrap(), open);

    let held = BudgetReport {
        free: timed(amounts(600, 300, 3, 9), 60_000),
        held: amounts(400, 200, 0, 1),
        ..open.clone()
    };
    assert_eq!(
        ledger
            .reserve(
                "root",
                Use::Work,
                "model:test/m",
                timed(amounts(100, 50, 0, 1), 1_000),
                BudgetAmounts::default(),
                &[timed(amounts(400, 200, 0, 1), 10_000)],
                REQUEST_MIN_MS,
            )
            .unwrap(),
        Reserved::Granted {
            reservation: Reservation {
                id: 0,
                index: 0,
                amount: timed(amounts(400, 200, 0, 1), 10_000),
                low: false,
            },
            report: held.clone(),
        }
    );
    assert_eq!(ledger.report("root").unwrap(), Some(held.clone()));
    assert_balanced(&held);

    let settled = BudgetReport {
        free: timed(amounts(880, 420, 3, 9), 60_000),
        spent: amounts(120, 80, 0, 1),
        ..open
    };
    assert_eq!(ledger.settle(0, amounts(120, 80, 0, 1)).unwrap(), settled);
    assert_balanced(&settled);
    // a settlement settles once
    assert_eq!(ledger.settle(0, amounts(120, 80, 0, 1)).unwrap(), settled);
    assert_exact(&ledger, 4, amounts(120, 80, 0, 1));
}

#[test]
fn a_request_past_the_remainder_goes_out_with_a_reduced_cap_or_not_at_all() {
    let dir = tempfile::tempdir().unwrap();
    let ledger = at(dir.path(), "root");
    ledger.open_root(cost_only(1_000)).unwrap();
    // the wanted cap costs too much; the reduced one fits with the reserve
    let reservation = granted(
        ledger
            .reserve(
                "root",
                Use::Work,
                "model:test/m",
                cost(200),
                BudgetAmounts::default(),
                &[cost(900), cost(800)],
                REQUEST_MIN_MS,
            )
            .unwrap(),
    );
    assert_eq!(
        reservation,
        Reservation {
            id: 0,
            index: 1,
            amount: cost(800),
            low: false,
        }
    );
    ledger.settle(0, cost(800)).unwrap();
    // 200 left, all of it the final-answer reserve: no work fits
    assert_eq!(
        ledger
            .reserve(
                "root",
                Use::Work,
                "model:test/m",
                cost(200),
                BudgetAmounts::default(),
                &[cost(100), cost(1)],
                REQUEST_MIN_MS,
            )
            .unwrap(),
        Reserved::Refused {
            refusal: Refusal::Short(BudgetDimension::Cost),
            report: BudgetReport {
                spent: cost(800),
                phase: BudgetPhase::WrapUp,
                short: Some(BudgetDimension::Cost),
                ..fresh("root", "root", cost_only(1_000), cost(200))
            },
        }
    );
}

/// A grant says the budget runs low when two steps of what the agent actually spent per
/// step, with its final-answer reserve, no longer fit what was free; the
/// size of the hold (the largest offer that fits) plays no part.
#[test]
fn a_grant_is_low_by_the_agents_steps_not_by_its_hold() {
    let dir = tempfile::tempdir().unwrap();
    let ledger = at(dir.path(), "root");
    ledger.open_root(cost_only(1_000)).unwrap();
    let work = |step, offer| {
        granted(
            ledger
                .reserve(
                    "root",
                    Use::Work,
                    "model:test/m",
                    cost(200),
                    step,
                    &[offer],
                    REQUEST_MIN_MS,
                )
                .unwrap(),
        )
    };
    // the hold takes all but the reserve; two steps of 400 and the reserve
    // fit the 1000 that were free
    let first = work(cost(400), cost(800));
    ledger.settle(first.id, cost(300)).unwrap();
    // 700 free: two steps of 300 and the reserve do not fit
    let second = work(cost(300), cost(100));
    assert_eq!((first.low, second.low), (false, true));
}

#[test]
fn at_exhaustion_only_the_final_answer_is_admitted_and_added_budget_resumes_work() {
    let dir = tempfile::tempdir().unwrap();
    let ledger = at(dir.path(), "root");
    ledger.open_root(cost_only(300)).unwrap();
    let keep = cost(200);
    let work = |amount| {
        ledger
            .reserve(
                "root",
                Use::Work,
                "tool:bash",
                keep,
                BudgetAmounts::default(),
                &[amount],
                TOOL_MIN_MS,
            )
            .unwrap()
    };
    assert_eq!(
        refused(work(cost(150))).0,
        Refusal::Short(BudgetDimension::Cost)
    );
    // told to wrap up: work is refused whatever its size
    assert_eq!(refused(work(cost(1))).0, Refusal::Stopped);
    // the reserve pays the final answer
    let id = granted(final_answer(&ledger, "root", cost(200))).id;
    ledger.settle(id, cost(180)).unwrap();
    // a final answer that fits nowhere exhausts the agent
    assert_eq!(
        refused(final_answer(&ledger, "root", cost(200))),
        (
            Refusal::Short(BudgetDimension::Cost),
            BudgetReport {
                spent: cost(180),
                phase: BudgetPhase::Exhausted,
                short: Some(BudgetDimension::Cost),
                ..fresh("root", "root", cost_only(300), cost(120))
            }
        )
    );
    assert_eq!(
        refused(final_answer(&ledger, "root", cost(1))).0,
        Refusal::Stopped
    );
    // adding budget resumes
    assert_eq!(
        ledger.fund(cost(1_000)).unwrap(),
        BudgetReport {
            spent: cost(180),
            ..fresh("root", "root", cost_only(1_300), cost(1_120))
        }
    );
    granted(work(cost(150)));
    assert_exact(&ledger, 9, cost(180));
}

#[test]
fn a_dimension_without_a_limit_is_never_short_and_never_counted() {
    let dir = tempfile::tempdir().unwrap();
    let ledger = at(dir.path(), "root");
    ledger.open_root(cost_only(100)).unwrap();
    let reservation = granted(
        ledger
            .reserve(
                "root",
                Use::Work,
                "model:test/m",
                BudgetAmounts::default(),
                BudgetAmounts::default(),
                &[timed(
                    amounts(10, 1_000_000, 1_000_000, 1_000_000),
                    1_000_000,
                )],
                REQUEST_MIN_MS,
            )
            .unwrap(),
    );
    assert_eq!(reservation.amount, cost(10));
    let settled = ledger
        .settle(reservation.id, amounts(5, 999, 999, 999))
        .unwrap();
    assert_eq!(settled.spent, cost(5));
    // a new dimension can be limited by added budget
    assert_eq!(
        ledger.fund(amounts(0, 0, 2, 0)).unwrap(),
        BudgetReport {
            spent: cost(5),
            ..fresh(
                "root",
                "root",
                BudgetLimits {
                    cost_micros: Some(100),
                    tool_calls: Some(2),
                    ..BudgetLimits::default()
                },
                amounts(95, 0, 2, 0),
            )
        }
    );
}

#[test]
fn a_limit_is_added_to_an_unlimited_dimension_and_model_requests_are_counted() {
    let dir = tempfile::tempdir().unwrap();
    let ledger = at(dir.path(), "root");
    ledger.open_root(cost_only(100)).unwrap();
    // the cost already has a limit: it keeps it
    let limits = BudgetLimits {
        cost_micros: Some(100),
        time_ms: Some(60_000),
        requests: Some(2),
        ..BudgetLimits::default()
    };
    let limited = BudgetReport {
        deadline_ms: Some(T0 + 60_000),
        ..fresh("root", "root", limits, timed(amounts(100, 0, 0, 2), 60_000))
    };
    assert_eq!(
        ledger
            .limit(BudgetLimits {
                cost_micros: Some(5),
                ..limits
            })
            .unwrap(),
        limited
    );
    let request = timed(amounts(1, 0, 0, 1), 10_000);
    for _ in 0..2 {
        let reservation = granted(final_answer(&ledger, "root", request));
        ledger.settle(reservation.id, amounts(1, 0, 0, 1)).unwrap();
    }
    assert_eq!(
        refused(final_answer(&ledger, "root", request)),
        (
            Refusal::Short(BudgetDimension::Requests),
            BudgetReport {
                free: timed(amounts(98, 0, 0, 0), 60_000),
                spent: amounts(2, 0, 0, 2),
                phase: BudgetPhase::Exhausted,
                short: Some(BudgetDimension::Requests),
                ..limited
            }
        )
    );
    // limiting dimensions that have a limit writes nothing
    ledger.limit(limits).unwrap();
    assert_exact(&ledger, 7, amounts(2, 0, 0, 2));
}

#[test]
fn a_crash_charges_what_was_in_flight_in_full_once_and_loses_nothing_settled() {
    let dir = tempfile::tempdir().unwrap();
    let ledger = at(dir.path(), "root");
    ledger.open_root(cost_only(1_000)).unwrap();
    let first = granted(final_answer(&ledger, "root", cost(300))).id;
    ledger.settle(first, cost(100)).unwrap();
    let in_flight = granted(final_answer(&ledger, "root", cost(250))).id;
    // the process dies here: a record cut short is left at the file's end
    let mut file = std::fs::OpenOptions::new()
        .append(true)
        .open(ledger.path())
        .unwrap();
    file.write_all(br#"{"seq":4,"atMs":1,"op":{"kind":"settle","id":1,"act"#)
        .unwrap();
    drop(file);

    // a new process: a new handle on the same file
    let restarted = at(dir.path(), "root");
    assert_eq!(
        restarted.report("root").unwrap(),
        Some(BudgetReport {
            held: cost(250),
            spent: cost(100),
            ..fresh("root", "root", cost_only(1_000), cost(650))
        })
    );
    let recovered = BudgetReport {
        spent: cost(350),
        ..fresh("root", "root", cost_only(1_000), cost(650))
    };
    assert_eq!(restarted.recover("root").unwrap(), recovered);
    assert_balanced(&recovered);
    // recovering again, or the lost request's late settlement, changes nothing
    assert_eq!(restarted.recover("root").unwrap(), recovered);
    assert_eq!(restarted.settle(in_flight, cost(10)).unwrap(), recovered);
    assert_exact(&restarted, 6, cost(350));
}

#[test]
fn a_recovery_charges_only_the_crashed_agents_holds_in_full() {
    let dir = tempfile::tempdir().unwrap();
    let root = at(dir.path(), "root");
    root.open_root(cost_only(1_000)).unwrap();
    let kid = at(dir.path(), "kid");
    assert_eq!(
        kid.join("root").unwrap(),
        fresh("root", "kid", cost_only(1_000), cost(1_000))
    );
    let root_request = granted(final_answer(&root, "root", cost(300))).id;
    granted(final_answer(&kid, "kid", cost(200)));
    // the child's process dies with its request in flight and starts again
    let restarted = at(dir.path(), "kid");
    assert_eq!(
        restarted.recover("kid").unwrap(),
        BudgetReport {
            held: cost(300),
            spent: cost(200),
            ..fresh("root", "kid", cost_only(1_000), cost(500))
        }
    );
    // the parent's request, live in another process, settles as it spent
    assert_eq!(
        root.settle(root_request, cost(120)).unwrap(),
        BudgetReport {
            spent: cost(320),
            ..fresh("root", "root", cost_only(1_000), cost(680))
        }
    );
    assert_exact(&root, 6, cost(320));
}

#[test]
fn a_released_child_is_charged_what_it_left_in_flight_and_draws_no_more() {
    let dir = tempfile::tempdir().unwrap();
    let root = at(dir.path(), "root");
    root.open_root(cost_only(1_000)).unwrap();
    let kid = at(dir.path(), "kid");
    kid.join("root").unwrap();
    at(dir.path(), "kid.1").join("kid").unwrap();
    granted(
        kid.reserve(
            "kid",
            Use::Work,
            "model:test/m",
            cost(50),
            BudgetAmounts::default(),
            &[cost(100)],
            REQUEST_MIN_MS,
        )
        .unwrap(),
    );
    root.release("kid").unwrap();
    assert_eq!(
        root.report("root").unwrap(),
        Some(BudgetReport {
            spent: cost(100),
            ..fresh("root", "root", cost_only(1_000), cost(900))
        })
    );
    // its own child now draws below the root
    assert_eq!(
        root.members().unwrap(),
        BTreeMap::from([
            (
                "kid.1".to_owned(),
                Member {
                    parent: Some("root".to_owned()),
                    ..Member::default()
                }
            ),
            ("root".to_owned(), Member::default()),
        ])
    );
    assert!(!kid.exists());
    assert!(matches!(
        try_final(&kid, "kid", cost(1)),
        Err(LedgerError::NoBudget(session)) if session == "kid"
    ));
    assert!(matches!(
        try_final(&root, "kid", cost(1)),
        Err(LedgerError::NotMember(session)) if session == "kid"
    ));
    // released again: nothing more happens; joined again: it draws again
    root.release("kid").unwrap();
    kid.join("root").unwrap();
    granted(final_answer(&kid, "kid", cost(10)));
    assert_exact(&root, 7, cost(100));
}

#[test]
fn a_shared_childs_work_never_takes_its_parents_final_answer_reserve() {
    let dir = tempfile::tempdir().unwrap();
    let root = at(dir.path(), "root");
    root.open_root(cost_only(1_000)).unwrap();
    // the parent works, keeping 300 for its final answer
    let id = granted(
        root.reserve(
            "root",
            Use::Work,
            "model:test/m",
            cost(300),
            BudgetAmounts::default(),
            &[cost(100)],
            REQUEST_MIN_MS,
        )
        .unwrap(),
    )
    .id;
    root.settle(id, cost(100)).unwrap();
    let kid = at(dir.path(), "kid");
    kid.join("root").unwrap();
    // 900 free: 560 + the parent's 300 + its own 50 do not fit, 550 does
    let reservation = granted(
        kid.reserve(
            "kid",
            Use::Work,
            "model:test/m",
            cost(50),
            BudgetAmounts::default(),
            &[cost(560), cost(550)],
            REQUEST_MIN_MS,
        )
        .unwrap(),
    );
    assert_eq!(
        reservation,
        Reservation {
            id: 1,
            index: 1,
            amount: cost(550),
            low: false,
        }
    );
    kid.settle(reservation.id, cost(550)).unwrap();
    // the child's own final answer must leave the parent's reserve too
    assert_eq!(
        refused(final_answer(&kid, "kid", cost(100))),
        (
            Refusal::Short(BudgetDimension::Cost),
            BudgetReport {
                spent: cost(650),
                phase: BudgetPhase::Exhausted,
                short: Some(BudgetDimension::Cost),
                ..fresh("root", "kid", cost_only(1_000), cost(350))
            }
        )
    );
    // the parent's final answer still fits
    let last = granted(final_answer(&root, "root", cost(300)));
    root.settle(last.id, cost(300)).unwrap();
    assert_exact(&root, 9, cost(950));
}

#[test]
fn each_agent_has_its_own_phase() {
    let dir = tempfile::tempdir().unwrap();
    let root = at(dir.path(), "root");
    root.open_root(cost_only(100)).unwrap();
    let kid = at(dir.path(), "kid");
    kid.join("root").unwrap();
    assert_eq!(
        refused(final_answer(&kid, "kid", cost(101))),
        (
            Refusal::Short(BudgetDimension::Cost),
            BudgetReport {
                phase: BudgetPhase::Exhausted,
                short: Some(BudgetDimension::Cost),
                ..fresh("root", "kid", cost_only(100), cost(100))
            }
        )
    );
    // the parent still works; the child stays stopped
    assert_eq!(
        root.report("root").unwrap(),
        Some(fresh("root", "root", cost_only(100), cost(100)))
    );
    granted(
        root.reserve(
            "root",
            Use::Work,
            "tool:bash",
            cost(10),
            BudgetAmounts::default(),
            &[cost(10)],
            TOOL_MIN_MS,
        )
        .unwrap(),
    );
    assert_eq!(
        refused(final_answer(&kid, "kid", cost(1))).0,
        Refusal::Stopped
    );
}

/// A side request of `amount` by `agent` (a title, a classifier, a
/// compaction): it leaves the agent's final-answer reserve `keep`.
fn side(ledger: &Ledger, agent: &str, keep: BudgetAmounts, amount: BudgetAmounts) -> Reserved {
    ledger
        .reserve(
            agent,
            Use::Side,
            "model:test/title",
            keep,
            BudgetAmounts::default(),
            &[amount],
            REQUEST_MIN_MS,
        )
        .unwrap()
}

#[test]
fn a_side_request_that_does_not_fit_changes_nothing_and_the_work_goes_on() {
    let dir = tempfile::tempdir().unwrap();
    let ledger = at(dir.path(), "root");
    ledger.open_root(cost_only(300)).unwrap();
    let keep = cost(200);
    // 150 and the reserve of 200 are past 300: not sent, and the agent
    // still works
    assert_eq!(
        refused(side(&ledger, "root", keep, cost(150))),
        (
            Refusal::Short(BudgetDimension::Cost),
            fresh("root", "root", cost_only(300), cost(300))
        )
    );
    let id = granted(
        ledger
            .reserve(
                "root",
                Use::Work,
                "tool:bash",
                keep,
                BudgetAmounts::default(),
                &[cost(100)],
                TOOL_MIN_MS,
            )
            .unwrap(),
    )
    .id;
    ledger.settle(id, cost(100)).unwrap();
    assert_eq!(
        ledger.report("root").unwrap(),
        Some(BudgetReport {
            spent: cost(100),
            ..fresh("root", "root", cost_only(300), cost(200))
        })
    );
    assert_exact(&ledger, 4, cost(100));
}

#[test]
fn side_requests_go_on_while_the_agent_wraps_up_leave_its_final_answer_and_stop_when_exhausted() {
    let dir = tempfile::tempdir().unwrap();
    let ledger = at(dir.path(), "root");
    ledger.open_root(cost_only(300)).unwrap();
    let keep = cost(200);
    // work that does not fit wraps the agent up
    assert_eq!(
        refused(
            ledger
                .reserve(
                    "root",
                    Use::Work,
                    "tool:bash",
                    keep,
                    BudgetAmounts::default(),
                    &[cost(150)],
                    TOOL_MIN_MS
                )
                .unwrap()
        )
        .0,
        Refusal::Short(BudgetDimension::Cost)
    );
    let wrapping = BudgetReport {
        phase: BudgetPhase::WrapUp,
        short: Some(BudgetDimension::Cost),
        ..fresh("root", "root", cost_only(300), cost(300))
    };
    // a side request that fits with the reserve is granted in WrapUp, and
    // the phase stays
    let Reserved::Granted {
        reservation,
        report,
    } = side(&ledger, "root", keep, cost(50))
    else {
        panic!("a side request that fits was refused in WrapUp");
    };
    assert_eq!(
        report,
        BudgetReport {
            free: cost(250),
            held: cost(50),
            ..wrapping.clone()
        }
    );
    ledger.settle(reservation.id, cost(50)).unwrap();
    // one that does not fit is not sent and changes nothing: still WrapUp,
    // for the work's reason
    assert_eq!(
        refused(side(&ledger, "root", keep, cost(100))),
        (
            Refusal::Short(BudgetDimension::Cost),
            BudgetReport {
                free: cost(250),
                spent: cost(50),
                ..wrapping
            }
        )
    );
    // the side request left the reserve: the final answer is granted
    let id = granted(final_answer(&ledger, "root", cost(200))).id;
    ledger.settle(id, cost(200)).unwrap();
    // a final answer that fits nowhere exhausts the agent, and an
    // exhausted agent is refused side requests too
    assert_eq!(
        refused(final_answer(&ledger, "root", cost(100))).0,
        Refusal::Short(BudgetDimension::Cost)
    );
    assert_eq!(
        refused(side(&ledger, "root", BudgetAmounts::default(), cost(1))),
        (
            Refusal::Stopped,
            BudgetReport {
                spent: cost(250),
                phase: BudgetPhase::Exhausted,
                short: Some(BudgetDimension::Cost),
                ..fresh("root", "root", cost_only(300), cost(50))
            }
        )
    );
    // the file records the side requests and replays exactly
    assert!(std::fs::read_to_string(ledger.path())
        .unwrap()
        .contains("\"use\":\"side\""));
    assert_exact(&ledger, 9, cost(250));
}

#[test]
fn a_side_request_is_clipped_to_leave_the_final_answers_time() {
    let dir = tempfile::tempdir().unwrap();
    let ledger = at(dir.path(), "root");
    ledger
        .open_root(BudgetLimits {
            cost_micros: Some(1_000),
            time_ms: Some(100_000),
            ..BudgetLimits::default()
        })
        .unwrap();
    // 100 s left, 20 s of them the final answer's: it may run 80 s
    assert_eq!(
        granted(side(
            &ledger,
            "root",
            timed(cost(10), 20_000),
            timed(cost(100), 600_000)
        )),
        Reservation {
            id: 0,
            index: 0,
            amount: timed(cost(100), 80_000),
            low: false,
        }
    );
}

static DEADLINE_CLOCK: AtomicU64 = AtomicU64::new(T0);

fn deadline_clock() -> u64 {
    DEADLINE_CLOCK.load(Ordering::SeqCst)
}

#[test]
#[allow(clippy::too_many_lines)] // One deadline across a restart, step by step.
fn the_deadline_clips_or_refuses_what_would_run_past_it_and_survives_a_restart() {
    let dir = tempfile::tempdir().unwrap();
    let ledger = Ledger::of(dir.path(), "root").with_clock(deadline_clock);
    let limits = BudgetLimits {
        cost_micros: Some(1_000),
        time_ms: Some(100_000),
        ..BudgetLimits::default()
    };
    let open = BudgetReport {
        deadline_ms: Some(T0 + 100_000),
        ..fresh("root", "root", limits, timed(cost(1_000), 100_000))
    };
    assert_eq!(ledger.open_root(limits).unwrap(), open);
    let keep = timed(cost(10), 20_000);
    let work = |ledger: &Ledger| {
        ledger
            .reserve(
                "root",
                Use::Work,
                "model:test/m",
                keep,
                BudgetAmounts::default(),
                &[timed(cost(100), 600_000)],
                REQUEST_MIN_MS,
            )
            .unwrap()
    };
    // 100 s left, 20 s of them the final answer's: the request may run 80 s
    assert_eq!(
        granted(work(&ledger)),
        Reservation {
            id: 0,
            index: 0,
            amount: timed(cost(100), 80_000),
            low: false,
        }
    );
    ledger.settle(0, cost(40)).unwrap();
    // 60 s later 20 s are left for work, less than a request's floor
    DEADLINE_CLOCK.store(T0 + 60_000, Ordering::SeqCst);
    assert_eq!(
        refused(work(&ledger)),
        (
            Refusal::Short(BudgetDimension::Time),
            BudgetReport {
                free: timed(cost(960), 40_000),
                spent: cost(40),
                phase: BudgetPhase::WrapUp,
                short: Some(BudgetDimension::Time),
                ..open.clone()
            }
        )
    );
    // the final answer takes what is left
    assert_eq!(
        granted(
            ledger
                .reserve(
                    "root",
                    Use::Final,
                    "model:test/m",
                    keep,
                    BudgetAmounts::default(),
                    &[timed(cost(100), 600_000)],
                    REQUEST_MIN_MS,
                )
                .unwrap()
        ),
        Reservation {
            id: 1,
            index: 0,
            amount: timed(cost(100), 40_000),
            low: false,
        }
    );
    // the process dies and starts again: the deadline is where it was
    let restarted = Ledger::of(dir.path(), "root").with_clock(deadline_clock);
    assert_eq!(
        restarted.recover("root").unwrap(),
        BudgetReport {
            free: timed(cost(860), 40_000),
            spent: cost(140),
            phase: BudgetPhase::WrapUp,
            short: Some(BudgetDimension::Time),
            ..open.clone()
        }
    );
    // past the deadline nothing is admitted, however short
    DEADLINE_CLOCK.store(T0 + 100_001, Ordering::SeqCst);
    assert_eq!(
        refused(
            restarted
                .reserve(
                    "root",
                    Use::Final,
                    "tool:bash",
                    BudgetAmounts::default(),
                    BudgetAmounts::default(),
                    &[timed(cost(1), 5_000)],
                    TOOL_MIN_MS,
                )
                .unwrap()
        ),
        (
            Refusal::Short(BudgetDimension::Time),
            BudgetReport {
                free: cost(860),
                spent: cost(140),
                phase: BudgetPhase::Exhausted,
                short: Some(BudgetDimension::Time),
                ..open.clone()
            }
        )
    );
    // added time extends the deadline and resumes work
    assert_eq!(
        restarted.fund(timed(cost(0), 50_000)).unwrap(),
        BudgetReport {
            limits: BudgetLimits {
                time_ms: Some(150_000),
                ..limits
            },
            free: timed(cost(860), 49_999),
            spent: cost(140),
            deadline_ms: Some(T0 + 150_000),
            ..open
        }
    );
    assert_exact(&restarted, 8, cost(140));
}

#[test]
fn added_budget_resumes_every_agent_of_the_account_and_extends_the_deadline() {
    let dir = tempfile::tempdir().unwrap();
    let root = at(dir.path(), "root");
    let limits = BudgetLimits {
        cost_micros: Some(300),
        time_ms: Some(60_000),
        ..BudgetLimits::default()
    };
    root.open_root(limits).unwrap();
    let kid = at(dir.path(), "kid");
    kid.join("root").unwrap();
    refused(
        root.reserve(
            "root",
            Use::Work,
            "tool:bash",
            cost(200),
            BudgetAmounts::default(),
            &[cost(150)],
            TOOL_MIN_MS,
        )
        .unwrap(),
    );
    refused(final_answer(&kid, "kid", cost(400)));
    let funded = BudgetReport {
        deadline_ms: Some(T0 + 90_000),
        ..fresh(
            "root",
            "root",
            BudgetLimits {
                cost_micros: Some(1_300),
                time_ms: Some(90_000),
                ..BudgetLimits::default()
            },
            timed(cost(1_300), 90_000),
        )
    };
    assert_eq!(
        kid.fund(timed(cost(1_000), 30_000)).unwrap(),
        BudgetReport {
            agent_session_id: "kid".to_owned(),
            ..funded.clone()
        }
    );
    assert_eq!(root.report("root").unwrap(), Some(funded));
    assert_eq!(
        root.members().unwrap(),
        BTreeMap::from([
            (
                "kid".to_owned(),
                Member {
                    parent: Some("root".to_owned()),
                    ..Member::default()
                }
            ),
            (
                "root".to_owned(),
                Member {
                    keep: cost(200),
                    ..Member::default()
                }
            ),
        ])
    );
}

#[test]
fn an_account_with_shared_members_audits_exactly_and_every_reserve_above_is_kept() {
    let dir = tempfile::tempdir().unwrap();
    let root = at(dir.path(), "root");
    root.open_root(cost_only(1_000)).unwrap();
    let kid = at(dir.path(), "kid");
    kid.join("root").unwrap();
    let grandkid = at(dir.path(), "kid.1");
    grandkid.join("kid").unwrap();
    for (ledger, agent) in [(&root, "root"), (&kid, "kid")] {
        let id = granted(
            ledger
                .reserve(
                    agent,
                    Use::Work,
                    "model:test/m",
                    cost(100),
                    BudgetAmounts::default(),
                    &[cost(10)],
                    REQUEST_MIN_MS,
                )
                .unwrap(),
        )
        .id;
        ledger.settle(id, cost(10)).unwrap();
    }
    // 980 free: the grandchild leaves the reserves of both agents above it
    assert_eq!(
        granted(
            grandkid
                .reserve(
                    "kid.1",
                    Use::Work,
                    "model:test/m",
                    BudgetAmounts::default(),
                    BudgetAmounts::default(),
                    &[cost(781), cost(780)],
                    REQUEST_MIN_MS,
                )
                .unwrap()
        ),
        Reservation {
            id: 2,
            index: 1,
            amount: cost(780),
            low: false,
        }
    );
    // the grandchild ends with its request in flight
    kid.release("kid.1").unwrap();
    assert_eq!(
        kid.members().unwrap(),
        BTreeMap::from([
            (
                "kid".to_owned(),
                Member {
                    parent: Some("root".to_owned()),
                    keep: cost(100),
                    ..Member::default()
                }
            ),
            (
                "root".to_owned(),
                Member {
                    keep: cost(100),
                    ..Member::default()
                }
            ),
        ])
    );
    // every member's view audits the one account
    assert_exact(&kid, 9, cost(800));
    assert_exact(&root, 9, cost(800));
}

#[test]
fn agents_that_reserve_at_once_never_hold_more_than_the_budget() {
    let dir = tempfile::tempdir().unwrap();
    let root = at(dir.path(), "root");
    root.open_root(cost_only(1_000)).unwrap();
    at(dir.path(), "kid").join("root").unwrap();
    let workers: Vec<_> = ["root", "kid", "root", "kid", "root", "kid", "root", "kid"]
        .into_iter()
        .map(|agent| {
            let ledger = at(dir.path(), agent);
            std::thread::spawn(move || {
                let mut spent = 0;
                for _ in 0..40 {
                    if let Reserved::Granted { reservation, .. } = ledger
                        .reserve(
                            agent,
                            Use::Final,
                            "model:test/m",
                            BudgetAmounts::default(),
                            BudgetAmounts::default(),
                            &[cost(30), cost(7)],
                            0,
                        )
                        .unwrap()
                    {
                        let report = ledger.report(agent).unwrap().unwrap();
                        assert!(report.held.cost_micros + report.spent.cost_micros <= 1_000);
                        let actual = reservation.amount.cost_micros - 1;
                        ledger.settle(reservation.id, cost(actual)).unwrap();
                        spent += actual;
                    }
                }
                spent
            })
        })
        .collect();
    let spent: u64 = workers
        .into_iter()
        .map(|worker| worker.join().unwrap())
        .sum();
    assert!(spent <= 1_000, "the tree spent {spent} of 1000");
    let report = root.report("root").unwrap().unwrap();
    assert_eq!(report.spent, cost(spent));
    assert_eq!(report.held, BudgetAmounts::default());
    assert_balanced(&report);
    let audit = root.audit().unwrap();
    assert!(audit.exact(), "{audit:?}");
    assert_eq!(audit.settled, cost(spent));
}

#[test]
#[allow(clippy::too_many_lines)] // One carve-spend-reclaim round trip, step by step.
fn a_childs_own_budget_is_carved_with_its_deadline_and_what_it_leaves_returns() {
    let dir = tempfile::tempdir().unwrap();
    let root = at(dir.path(), "root");
    let limits = BudgetLimits {
        cost_micros: Some(1_000),
        tokens: Some(1_000),
        time_ms: Some(100_000),
        tool_calls: Some(10),
        requests: Some(10),
    };
    root.open_root(limits).unwrap();
    // the parent's final-answer reserve: 100, 100 tokens, 10 s
    let id = granted(
        root.reserve(
            "root",
            Use::Work,
            "model:test/m",
            timed(amounts(100, 100, 0, 0), 10_000),
            BudgetAmounts::default(),
            &[amounts(0, 0, 0, 1)],
            REQUEST_MIN_MS,
        )
        .unwrap(),
    )
    .id;
    root.settle(id, amounts(0, 0, 0, 1)).unwrap();
    let allotment = |cost_micros, tokens, time_ms| BudgetLimits {
        cost_micros: Some(cost_micros),
        tokens: Some(tokens),
        time_ms,
        tool_calls: Some(4),
        requests: Some(4),
    };
    let root_open = BudgetReport {
        spent: amounts(0, 0, 0, 1),
        deadline_ms: Some(T0 + 100_000),
        ..fresh(
            "root",
            "root",
            limits,
            timed(amounts(1_000, 1_000, 10, 9), 100_000),
        )
    };
    // a child cannot be given what the parent does not have past its reserve
    assert_eq!(
        root.carve("root", "child", allotment(950, 10, None))
            .unwrap(),
        CarveOutcome::Refused {
            refusal: Refusal::Short(BudgetDimension::Cost),
            report: root_open.clone(),
        }
    );
    // nor a time that runs past the parent's deadline less its reserve
    assert_eq!(
        root.carve("root", "child", allotment(400, 300, Some(95_000)))
            .unwrap(),
        CarveOutcome::Refused {
            refusal: Refusal::Short(BudgetDimension::Time),
            report: root_open.clone(),
        }
    );
    assert!(!at(dir.path(), "child").exists());
    // nor without an allotment in a dimension the parent limits
    assert!(matches!(
        root.carve("root", "child", cost_only(10)),
        Err(LedgerError::NeedsAllotment(BudgetDimension::Tokens))
    ));

    let lent = BudgetReport {
        free: timed(amounts(600, 700, 6, 5), 100_000),
        lent: amounts(400, 300, 4, 4),
        ..root_open.clone()
    };
    assert_eq!(
        root.carve("root", "child", allotment(400, 300, Some(50_000)))
            .unwrap(),
        CarveOutcome::Carved {
            report: lent.clone()
        }
    );
    assert_balanced(&lent);
    let child = at(dir.path(), "child");
    assert_eq!(
        child.report("child").unwrap(),
        Some(BudgetReport {
            deadline_ms: Some(T0 + 50_000),
            parent_session_id: Some("root".to_owned()),
            ..fresh(
                "child",
                "child",
                allotment(400, 300, Some(50_000)),
                timed(amounts(400, 300, 4, 4), 50_000),
            )
        })
    );
    // the child cannot spend past its allotment, whatever the parent has
    refused(final_answer(&child, "child", amounts(401, 1, 0, 0)));
    // nor add budget to itself
    assert!(matches!(child.fund(cost(1)), Err(LedgerError::NotRoot(_))));
    // the parent's carve again funds the child, resumes it, and moves its
    // deadline to what the parent has left past its reserve
    assert!(matches!(
        root.carve(
            "root",
            "child",
            BudgetLimits {
                cost_micros: Some(100),
                tokens: Some(0),
                time_ms: None,
                tool_calls: Some(0),
                requests: Some(0),
            }
        )
        .unwrap(),
        CarveOutcome::Carved { .. }
    ));
    assert_eq!(
        child.report("child").unwrap(),
        Some(BudgetReport {
            deadline_ms: Some(T0 + 90_000),
            parent_session_id: Some("root".to_owned()),
            ..fresh(
                "child",
                "child",
                allotment(500, 300, Some(90_000)),
                timed(amounts(500, 300, 4, 4), 90_000),
            )
        })
    );
    let reservation = granted(
        child
            .reserve(
                "child",
                Use::Work,
                "model:test/m",
                BudgetAmounts::default(),
                BudgetAmounts::default(),
                &[timed(amounts(450, 100, 1, 1), 30_000)],
                REQUEST_MIN_MS,
            )
            .unwrap(),
    );
    // a child with a request in flight is not closed
    assert_eq!(root.reclaim("child", false).unwrap(), ReclaimOutcome::Busy);
    child
        .settle(reservation.id, amounts(430, 60, 1, 1))
        .unwrap();

    let back = BudgetReport {
        free: timed(amounts(570, 940, 9, 8), 100_000),
        spent: amounts(430, 60, 1, 2),
        ..root_open
    };
    assert_eq!(
        root.reclaim("child", false).unwrap(),
        ReclaimOutcome::Reclaimed {
            returned: amounts(70, 240, 3, 3),
            spent: amounts(430, 60, 1, 1),
            report: back.clone(),
        }
    );
    assert_balanced(&back);
    // reclaiming again returns nothing twice
    assert_eq!(
        root.reclaim("child", false).unwrap(),
        ReclaimOutcome::NotLent
    );
    // the closed child can spend nothing
    let closed = BudgetLimits {
        cost_micros: Some(0),
        tokens: Some(0),
        time_ms: Some(0),
        tool_calls: Some(0),
        requests: Some(0),
    };
    assert_eq!(
        refused(final_answer(&child, "child", cost(1))),
        (
            Refusal::Stopped,
            BudgetReport {
                phase: BudgetPhase::Exhausted,
                deadline_ms: Some(0),
                ..fresh("child", "child", closed, BudgetAmounts::default())
            }
        )
    );
    // lent again, the child starts a fresh budget of exactly the new carve
    assert!(matches!(
        root.carve("root", "child", allotment(50, 10, Some(20_000)))
            .unwrap(),
        CarveOutcome::Carved { .. }
    ));
    assert_eq!(
        child.report("child").unwrap(),
        Some(BudgetReport {
            deadline_ms: Some(T0 + 20_000),
            parent_session_id: Some("root".to_owned()),
            ..fresh(
                "child",
                "child",
                allotment(50, 10, Some(20_000)),
                timed(amounts(50, 10, 4, 4), 20_000),
            )
        })
    );
    let ReclaimOutcome::Reclaimed {
        returned, report, ..
    } = root.reclaim("child", false).unwrap()
    else {
        panic!("an idle child is reclaimed");
    };
    assert_eq!(returned, amounts(50, 10, 4, 4));
    assert_eq!(report, back);
    assert!(root.audit().unwrap().exact());
    assert!(child.audit().unwrap().exact());
}

#[test]
fn a_tree_never_spends_past_its_roots_budget() {
    let dir = tempfile::tempdir().unwrap();
    let root = at(dir.path(), "root");
    root.open_root(cost_only(1_000)).unwrap();
    for child in ["a", "b"] {
        assert!(matches!(
            root.carve("root", child, cost_only(400)).unwrap(),
            CarveOutcome::Carved { .. }
        ));
    }
    // the third child does not fit
    assert!(matches!(
        root.carve("root", "c", cost_only(400)).unwrap(),
        CarveOutcome::Refused { .. }
    ));
    let a = at(dir.path(), "a");
    let b = at(dir.path(), "b");
    // a grandchild is carved from its parent's allotment, another shares it
    assert!(matches!(
        a.carve("a", "a1", cost_only(300)).unwrap(),
        CarveOutcome::Carved { .. }
    ));
    let a1 = at(dir.path(), "a1");
    let s = at(dir.path(), "s");
    s.join("b").unwrap();
    // every agent spends everything it can, retrying until refused
    let mut total = 0;
    for (ledger, agent) in [
        (&root, "root"),
        (&a, "a"),
        (&b, "b"),
        (&s, "s"),
        (&a1, "a1"),
    ] {
        while let Reserved::Granted { reservation, .. } = final_answer(ledger, agent, cost(70)) {
            ledger.settle(reservation.id, cost(70)).unwrap();
            total += 70;
        }
    }
    assert_eq!(total, 840);
    // the root reclaims the whole tree: the grandchild through its parent
    for child in ["a", "b"] {
        assert!(matches!(
            root.reclaim(child, true).unwrap(),
            ReclaimOutcome::Reclaimed { .. }
        ));
    }
    // the root's last final answer did not fit: what came back does not
    // resume it (only added budget does)
    let report = root.report("root").unwrap().unwrap();
    assert_eq!(
        report,
        BudgetReport {
            spent: cost(total),
            phase: BudgetPhase::Exhausted,
            short: Some(BudgetDimension::Cost),
            ..fresh("root", "root", cost_only(1_000), cost(1_000 - total))
        }
    );
    for ledger in [&root, &a, &b, &s, &a1] {
        let audit = ledger.audit().unwrap();
        assert!(audit.exact(), "{}: {audit:?}", ledger.session_id());
    }
}

#[test]
fn a_child_that_crashed_mid_request_is_closed_with_the_request_charged_in_full() {
    let dir = tempfile::tempdir().unwrap();
    let root = at(dir.path(), "root");
    root.open_root(cost_only(1_000)).unwrap();
    root.carve("root", "child", cost_only(500)).unwrap();
    let child = at(dir.path(), "child");
    granted(final_answer(&child, "child", cost(200)));
    // the child's process is gone; the parent forces the close
    let ReclaimOutcome::Reclaimed {
        returned, spent, ..
    } = root.reclaim("child", true).unwrap()
    else {
        panic!("a forced reclaim closes the child");
    };
    assert_eq!((returned, spent), (cost(300), cost(200)));
}

#[test]
fn a_child_is_not_closed_while_its_grandchild_given_nothing_has_a_request_in_flight() {
    let dir = tempfile::tempdir().unwrap();
    let root = at(dir.path(), "root");
    root.open_root(cost_only(1_000)).unwrap();
    root.carve("root", "child", cost_only(500)).unwrap();
    let child = at(dir.path(), "child");
    // the grandchild is given a budget of nothing: the child lends nothing
    assert!(matches!(
        child.carve("child", "grandchild", cost_only(0)).unwrap(),
        CarveOutcome::Carved { .. }
    ));
    let grandchild = at(dir.path(), "grandchild");
    granted(final_answer(&grandchild, "grandchild", cost(0)));
    // still the child is not closed under its live grandchild
    assert!(matches!(
        root.reclaim("child", false).unwrap(),
        ReclaimOutcome::Busy
    ));
    // a forced close takes the grandchild first, then the child
    assert!(matches!(
        root.reclaim("child", true).unwrap(),
        ReclaimOutcome::Reclaimed { .. }
    ));
    assert!(matches!(
        child.reclaim("grandchild", false).unwrap(),
        ReclaimOutcome::NotLent
    ));
    for ledger in [&root, &child, &grandchild] {
        let audit = ledger.audit().unwrap();
        assert!(audit.exact(), "{}: {audit:?}", ledger.session_id());
    }
}

#[test]
fn a_carve_cut_between_its_two_records_is_neither_lost_nor_doubled() {
    let dir = tempfile::tempdir().unwrap();
    let root = at(dir.path(), "root");
    root.open_root(cost_only(1_000)).unwrap();
    root.carve("root", "child", cost_only(500)).unwrap();
    // as if the parent died after its record and before the child's
    let child = at(dir.path(), "child");
    std::fs::remove_file(child.path()).unwrap();
    // the child's start finds what it was lent
    let opened = BudgetReport {
        parent_session_id: Some("root".to_owned()),
        ..fresh("child", "child", cost_only(500), cost(500))
    };
    assert_eq!(child.ensure_child("root").unwrap(), Some(opened.clone()));
    assert_eq!(child.ensure_child("root").unwrap(), Some(opened));
    // and a child that never started returns everything
    std::fs::remove_file(child.path()).unwrap();
    let ReclaimOutcome::Reclaimed {
        returned, report, ..
    } = root.reclaim("child", true).unwrap()
    else {
        panic!("an unopened child is reclaimed");
    };
    assert_eq!(returned, cost(500));
    assert_eq!(report, fresh("root", "root", cost_only(1_000), cost(1_000)));
    // a session nothing was lent to has no budget to find
    assert_eq!(
        at(dir.path(), "stranger").ensure_child("root").unwrap(),
        None
    );
}

#[test]
fn a_shared_child_given_a_budget_and_a_reclaimed_child_that_joins_switch_accounts() {
    let dir = tempfile::tempdir().unwrap();
    let root = at(dir.path(), "root");
    root.open_root(cost_only(1_000)).unwrap();
    let kid = at(dir.path(), "kid");
    kid.join("root").unwrap();
    granted(final_answer(&kid, "kid", cost(100)));
    // a shared child given its own budget: released (its request charged),
    // then carved
    assert!(matches!(
        root.carve("root", "kid", cost_only(200)).unwrap(),
        CarveOutcome::Carved { .. }
    ));
    assert!(kid.is_owner());
    assert_eq!(
        root.members().unwrap(),
        BTreeMap::from([("root".to_owned(), Member::default())])
    );
    assert_eq!(
        root.report("root").unwrap(),
        Some(BudgetReport {
            spent: cost(100),
            lent: cost(200),
            ..fresh("root", "root", cost_only(1_000), cost(700))
        })
    );
    // a live budget of its own does not join
    assert!(matches!(kid.join("root"), Err(LedgerError::AlreadyOpen(_))));
    // reclaimed, it joins the parent's account again
    root.reclaim("kid", true).unwrap();
    assert_eq!(
        kid.join("root").unwrap(),
        BudgetReport {
            spent: cost(100),
            ..fresh("root", "kid", cost_only(1_000), cost(900))
        }
    );
    assert!(!kid.is_owner());
    assert!(kid.exists());
    assert!(std::fs::read_dir(dir.path()).unwrap().any(|entry| entry
        .unwrap()
        .file_name()
        .to_string_lossy()
        .starts_with("kid.jsonl.")));
    granted(final_answer(&kid, "kid", cost(10)));
    assert!(root.audit().unwrap().exact());
}

#[test]
fn a_provider_that_breaks_its_cap_is_charged_in_full_and_shown_as_an_overrun() {
    let dir = tempfile::tempdir().unwrap();
    let root = at(dir.path(), "root");
    root.open_root(cost_only(100)).unwrap();
    root.carve("root", "child", cost_only(60)).unwrap();
    let child = at(dir.path(), "child");
    let id = granted(final_answer(&child, "child", cost(60))).id;
    let settled = child.settle(id, cost(75)).unwrap();
    assert_eq!(
        settled,
        BudgetReport {
            spent: cost(75),
            over: cost(15),
            parent_session_id: Some("root".to_owned()),
            ..fresh("child", "child", cost_only(60), BudgetAmounts::default())
        }
    );
    assert_balanced(&settled);
    // the parent pays the child's overrun from what it has free
    let ReclaimOutcome::Reclaimed { report, .. } = root.reclaim("child", false).unwrap() else {
        panic!("an idle child is reclaimed");
    };
    assert_eq!(
        report,
        BudgetReport {
            spent: cost(75),
            ..fresh("root", "root", cost_only(100), cost(25))
        }
    );
    assert_balanced(&report);
    assert!(root.audit().unwrap().exact());
}

#[test]
fn a_changed_record_fails_the_audit() {
    let dir = tempfile::tempdir().unwrap();
    let ledger = at(dir.path(), "root");
    ledger.open_root(cost_only(1_000)).unwrap();
    let id = granted(final_answer(&ledger, "root", cost(300))).id;
    ledger.settle(id, cost(100)).unwrap();
    let text = std::fs::read_to_string(ledger.path()).unwrap();
    // the settlement rewritten to a smaller spend, its state left as it was
    let forged = text.replacen(
        r#""actual":{"costMicros":100"#,
        r#""actual":{"costMicros":1"#,
        1,
    );
    assert_ne!(forged, text);
    std::fs::write(ledger.path(), forged).unwrap();
    let audit = ledger.audit().unwrap();
    assert!(!audit.exact());
    assert_eq!(audit.first_mismatch, Some(2));
}

#[test]
fn a_session_without_a_budget_refuses_every_ledger_operation() {
    let dir = tempfile::tempdir().unwrap();
    let ledger = at(dir.path(), "nobody");
    assert!(matches!(
        try_final(&ledger, "nobody", cost(1)),
        Err(LedgerError::NoBudget(_))
    ));
    assert!(matches!(
        ledger.recover("nobody"),
        Err(LedgerError::NoBudget(_))
    ));
    assert!(matches!(
        ledger.join("root"),
        Err(LedgerError::NoBudget(session)) if session == "root"
    ));
    assert!(!ledger.exists());
    ledger.open_root(cost_only(1)).unwrap();
    assert!(matches!(
        ledger.open_root(cost_only(1)),
        Err(LedgerError::AlreadyOpen(_))
    ));
    assert!(matches!(
        ledger.reserve(
            "nobody",
            Use::Work,
            "tool:bash",
            BudgetAmounts::default(),
            BudgetAmounts::default(),
            &[],
            0
        ),
        Err(LedgerError::NoOffer)
    ));
    assert!(matches!(
        try_final(&ledger, "stranger", cost(1)),
        Err(LedgerError::NotMember(session)) if session == "stranger"
    ));
}
