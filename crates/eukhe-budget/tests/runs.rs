//! The runs of an account (spec/README.md B15-B21): a run opens the account
//! of a session that has none and renews it after; each run counts its
//! spend from zero, the dimensions without a limit included, keeps what is
//! still held out of what is free, and counts the tool calls that run a
//! program.

use std::path::Path;

use eukhe_budget::{Audit, Ledger, LedgerError, Reserved, RunRecord, Use};
use eukhe_types::budget::{
    BudgetAmounts, BudgetLimits, BudgetReport, BudgetSources, LimitSource, LimitValue, RunKind,
    RunLimits,
};

const T0: u64 = 1_800_000_000_000;

fn fixed() -> u64 {
    T0
}

fn at(dir: &Path, session_id: &str) -> Ledger {
    Ledger::of(dir, session_id).with_clock(fixed)
}

fn requests(requests: u64) -> BudgetLimits {
    BudgetLimits {
        requests: Some(requests),
        ..BudgetLimits::default()
    }
}

/// A run of `kind` whose requests the principal set, the rest until
/// finished.
fn run(kind: RunKind) -> RunRecord {
    RunRecord {
        kind,
        sources: BudgetSources {
            requests: LimitSource::Set,
            ..BudgetSources::default()
        },
        standing: RunLimits {
            cost_micros: Some(LimitValue::Unlimited),
            ..RunLimits::default()
        },
    }
}

fn reserve(ledger: &Ledger, label: &str, offer: BudgetAmounts) -> u64 {
    match ledger
        .reserve(
            "root",
            Use::Work,
            label,
            BudgetAmounts::default(),
            BudgetAmounts::default(),
            &[offer],
            0,
        )
        .unwrap()
    {
        Reserved::Granted { reservation, .. } => reservation.id,
        Reserved::Refused { refusal, .. } => panic!("refused: {refusal:?}"),
    }
}

fn one_request() -> BudgetAmounts {
    BudgetAmounts {
        cost_micros: 50,
        tokens: 1_000,
        requests: 1,
        ..BudgetAmounts::default()
    }
}

#[test]
fn a_run_opens_the_account_and_the_next_run_renews_it() {
    let dir = tempfile::tempdir().unwrap();
    let ledger = at(dir.path(), "root");
    let opened = ledger
        .start_run(requests(5), run(RunKind::Interactive))
        .unwrap();
    let id = reserve(&ledger, "model:test/m", one_request());
    let spent = BudgetAmounts {
        cost_micros: 7,
        tokens: 300,
        requests: 1,
        ..BudgetAmounts::default()
    };
    let first = ledger.settle(id, spent).unwrap();
    let renewed = ledger
        .start_run(requests(3), run(RunKind::Scheduled))
        .unwrap();
    let base = BudgetReport {
        session_id: "root".to_owned(),
        agent_session_id: "root".to_owned(),
        sources: run(RunKind::Interactive).sources,
        ..BudgetReport::default()
    };
    assert_eq!(
        [opened, first, renewed],
        [
            BudgetReport {
                limits: requests(5),
                free: BudgetAmounts {
                    requests: 5,
                    ..BudgetAmounts::default()
                },
                kind: Some(RunKind::Interactive),
                ..base.clone()
            },
            // Money and tokens have no limit: their spend is counted.
            BudgetReport {
                limits: requests(5),
                free: BudgetAmounts {
                    requests: 4,
                    ..BudgetAmounts::default()
                },
                spent,
                kind: Some(RunKind::Interactive),
                ..base.clone()
            },
            BudgetReport {
                limits: requests(3),
                free: BudgetAmounts {
                    requests: 3,
                    ..BudgetAmounts::default()
                },
                kind: Some(RunKind::Scheduled),
                ..base
            },
        ]
    );
    assert_eq!(
        ledger.run().unwrap(),
        Some(run(RunKind::Scheduled)),
        "the run and what the principal set for every run are recorded"
    );
    // The file replays; the new run's spend starts at zero.
    assert_eq!(
        ledger.audit().unwrap(),
        Audit {
            records: 4,
            settled: BudgetAmounts::default(),
            spent: BudgetAmounts::default(),
            first_mismatch: None,
        }
    );
}

#[test]
fn what_is_still_held_stays_out_of_the_renewed_run() {
    let dir = tempfile::tempdir().unwrap();
    let ledger = at(dir.path(), "root");
    ledger
        .start_run(requests(5), run(RunKind::Interactive))
        .unwrap();
    let id = reserve(&ledger, "model:test/m", one_request());
    let renewed = ledger
        .start_run(requests(2), run(RunKind::Interactive))
        .unwrap();
    let settled = ledger.settle(id, one_request()).unwrap();
    let request = |count| BudgetAmounts {
        requests: count,
        ..BudgetAmounts::default()
    };
    assert_eq!(
        [
            (renewed.free, renewed.held, renewed.spent),
            (settled.free, settled.held, settled.spent),
        ],
        [
            (request(1), request(1), BudgetAmounts::default()),
            (request(1), BudgetAmounts::default(), one_request()),
        ]
    );
}

#[test]
fn a_run_counts_its_tool_calls_that_run_a_program() {
    let dir = tempfile::tempdir().unwrap();
    let ledger = at(dir.path(), "root");
    ledger
        .start_run(BudgetLimits::default(), run(RunKind::Headless))
        .unwrap();
    let call = BudgetAmounts {
        tool_calls: 1,
        ..BudgetAmounts::default()
    };
    for label in ["program:bash", "tool:read", "program:python"] {
        let id = reserve(&ledger, label, call);
        ledger.settle(id, call).unwrap();
    }
    let report = ledger.report("root").unwrap().unwrap();
    assert_eq!(
        (report.program_runs, report.spent.tool_calls),
        (2, 3),
        "{report:?}"
    );
}

#[test]
fn a_session_that_draws_from_another_account_starts_no_run() {
    let dir = tempfile::tempdir().unwrap();
    at(dir.path(), "root")
        .start_run(requests(5), run(RunKind::Interactive))
        .unwrap();
    let child = at(dir.path(), "child");
    child.join("root").unwrap();
    assert!(matches!(
        child.start_run(requests(1), run(RunKind::Interactive)),
        Err(LedgerError::NotRoot(session)) if session == "child"
    ));
}
