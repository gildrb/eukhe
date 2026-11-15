//! Runs (spec/README.md B15-B23): each run's limits fill from what the
//! principal set, its `/b` presets and, with limits on, the profile; with
//! limits off an unset dimension goes until finished. A plan window past
//! its share wraps the run up (limits on) or is told once (limits off).

use std::path::Path;
use std::sync::Arc;

use eukhe_ai::quota::{CredentialId, PlanQuota, QuotaBoard, QuotaSource, QuotaWindow};
use eukhe_types::budget::{
    AuthClass, BudgetAmounts, BudgetLimits, BudgetPhase, BudgetSources, LimitSource, LimitValue,
    RunKind, RunLimits,
};
use serde_json::{json, Value};
use tempfile::TempDir;

use super::{BudgetGate, Checked, RunFacts, RunStart, SeenModel};
use crate::settings::BudgetLimitsMode;

const HOUR: u64 = 3_600_000;

/// A root session's gate whose runs fill with `limits`, paid by `auth`,
/// with the principal's `profile`.
fn gate(limits: BudgetLimitsMode, auth: AuthClass, profile: Value) -> (TempDir, Arc<BudgetGate>) {
    let dir = TempDir::new().unwrap();
    let gate = gate_at(dir.path(), limits, auth, profile);
    (dir, gate)
}

/// [`gate`] over the budgets of `dir`: a session opened again sees what
/// its ledger kept.
fn gate_at(
    dir: &Path,
    limits: BudgetLimitsMode,
    auth: AuthClass,
    profile: Value,
) -> Arc<BudgetGate> {
    let gate = BudgetGate::open(dir, "session", None);
    gate.fill_runs(
        RunKind::Interactive,
        Arc::new(move |_| RunFacts {
            auth,
            limits,
            plan_reserve: 20,
            profile: profile.clone(),
            presets: json!({ "tight": { "requests": 7 } }),
        }),
    );
    gate
}

fn start(
    gate: &BudgetGate,
    kind: RunKind,
    set: RunLimits,
    presets: &[&str],
) -> eukhe_types::budget::BudgetReport {
    gate.start_run(RunStart {
        kind,
        set,
        presets: presets.iter().map(|name| (*name).to_owned()).collect(),
        standing: None,
    })
    .unwrap()
    .expect("a root session's run")
}

fn every(source: LimitSource) -> BudgetSources {
    BudgetSources {
        cost_micros: source.clone(),
        tokens: source.clone(),
        time_ms: source.clone(),
        tool_calls: source.clone(),
        requests: source,
    }
}

/// With limits off (the default) a run the principal set nothing for has
/// no limit in any dimension, each recorded `until finished (default)`,
/// for every kind of run.
#[test]
fn with_limits_off_every_kind_of_run_goes_until_finished() {
    let (_dir, gate) = gate(BudgetLimitsMode::Off, AuthClass::Plan, Value::Null);
    for kind in RunKind::ALL {
        let report = start(&gate, kind, RunLimits::default(), &[]);
        assert_eq!(
            (report.kind, report.limits, report.sources),
            (
                Some(kind),
                BudgetLimits::default(),
                every(LimitSource::UntilFinished)
            ),
            "{kind:?}"
        );
    }
}

/// With limits on, each kind fills time, tool calls and requests from the
/// limits profile; money and tokens stay until finished.
#[test]
fn with_limits_on_each_kind_fills_the_limits_profile() {
    let (_dir, gate) = gate(BudgetLimitsMode::On, AuthClass::ApiKey, Value::Null);
    for (kind, hours, calls, requests) in [
        (RunKind::Interactive, 4, 4_000, 3_200),
        (RunKind::Headless, 4, 4_000, 3_200),
        (RunKind::Sdk, 4, 4_000, 3_200),
        (RunKind::Scheduled, 1, 4_000, 3_200),
        (RunKind::Loop, 8, 8_000, 6_400),
        (RunKind::Autoresearch, 12, 12_000, 9_600),
    ] {
        let report = start(&gate, kind, RunLimits::default(), &[]);
        assert_eq!(
            (report.limits, report.sources),
            (
                BudgetLimits {
                    time_ms: Some(hours * HOUR),
                    tool_calls: Some(calls),
                    requests: Some(requests),
                    ..BudgetLimits::default()
                },
                BudgetSources {
                    time_ms: LimitSource::LimitsProfile,
                    tool_calls: LimitSource::LimitsProfile,
                    requests: LimitSource::LimitsProfile,
                    ..every(LimitSource::UntilFinished)
                }
            ),
            "{kind:?}"
        );
    }
}

/// A limit the principal sets applies with limits off; `unlimited` set by
/// the principal is recorded as set, not as the default; the principal's
/// profile goes before the limits profile with limits on.
#[test]
fn a_set_limit_always_applies_and_the_profile_goes_first() {
    let (_dir, off) = gate(BudgetLimitsMode::Off, AuthClass::ApiKey, Value::Null);
    let set = RunLimits {
        requests: Some(LimitValue::At(5)),
        cost_micros: Some(LimitValue::Unlimited),
        ..RunLimits::default()
    };
    let report = start(&off, RunKind::Interactive, set, &[]);
    assert_eq!(
        (report.limits, report.sources),
        (
            BudgetLimits {
                requests: Some(5),
                ..BudgetLimits::default()
            },
            BudgetSources {
                requests: LimitSource::Set,
                cost_micros: LimitSource::Set,
                ..every(LimitSource::UntilFinished)
            }
        )
    );
    let (_dir, on) = gate(
        BudgetLimitsMode::On,
        AuthClass::ApiKey,
        json!({ "interactive": { "requests": 10, "time": "unlimited" } }),
    );
    let report = start(&on, RunKind::Interactive, RunLimits::default(), &[]);
    assert_eq!(
        (
            report.limits.requests,
            report.limits.time_ms,
            report.limits.tool_calls
        ),
        (Some(10), None, Some(4_000))
    );
    assert_eq!(
        (
            report.sources.requests,
            report.sources.time_ms,
            report.sources.tool_calls
        ),
        (
            LimitSource::Profile,
            LimitSource::Profile,
            LimitSource::LimitsProfile
        )
    );
}

/// `/b quick` is a quarter of the limits profile and `/b deep` four
/// times it, with limits off too; the principal's own preset reads from
/// `budget.presets`; an unknown preset starts no run.
#[test]
fn presets_fill_their_run_with_limits_off() {
    let (_dir, gate) = gate(BudgetLimitsMode::Off, AuthClass::ApiKey, Value::Null);
    let quick = start(
        &gate,
        RunKind::Interactive,
        RunLimits::default(),
        &["quick"],
    );
    let deep = start(&gate, RunKind::Loop, RunLimits::default(), &["deep"]);
    let own = start(
        &gate,
        RunKind::Interactive,
        RunLimits::default(),
        &["quick", "tight"],
    );
    assert_eq!(
        (
            quick.limits.time_ms,
            quick.limits.requests,
            quick.sources.requests
        ),
        (
            Some(HOUR),
            Some(800),
            LimitSource::Preset("quick".to_owned())
        )
    );
    assert_eq!(
        (deep.limits.time_ms, deep.limits.requests),
        (Some(32 * HOUR), Some(25_600))
    );
    assert_eq!(
        (
            own.limits.requests,
            own.sources.requests,
            own.limits.time_ms
        ),
        (Some(7), LimitSource::Preset("tight".to_owned()), Some(HOUR))
    );
    assert!(gate
        .start_run(RunStart {
            presets: vec!["nonesuch".to_owned()],
            ..RunStart::default()
        })
        .is_err());
}

/// `/budget set` replaces the current run's limits (its kind kept); the
/// standing limits (flags, the SDK) carry into every later run.
#[test]
fn set_replaces_the_current_run_and_standing_limits_carry_over() {
    let (_dir, gate) = gate(BudgetLimitsMode::Off, AuthClass::ApiKey, Value::Null);
    start(&gate, RunKind::Loop, RunLimits::default(), &[]);
    let set = gate
        .set(RunLimits {
            tool_calls: Some(LimitValue::At(9)),
            ..RunLimits::default()
        })
        .unwrap();
    assert_eq!(
        (set.kind, set.limits.tool_calls, set.sources.tool_calls),
        (Some(RunKind::Loop), Some(9), LimitSource::Set)
    );
    gate.set_standing(RunLimits {
        requests: Some(LimitValue::At(3)),
        ..RunLimits::default()
    })
    .unwrap();
    let next = start(&gate, RunKind::Interactive, RunLimits::default(), &[]);
    assert_eq!(
        (
            next.limits.requests,
            next.limits.tool_calls,
            next.sources.requests
        ),
        (Some(3), None, LimitSource::Set),
        "the next run keeps the standing limits, not the last run's set"
    );
}

/// B15: limits set or added while the session runs nothing are the next
/// run's: the report shows them as such, the next run starts with them (a
/// `/b` pair of its message over them; an amount added to a dimension the
/// run leaves unlimited is its limit), and the run after it is free of
/// them.
#[test]
fn limits_set_while_idle_apply_to_the_next_run_only() {
    let (_dir, gate) = gate(BudgetLimitsMode::Off, AuthClass::ApiKey, Value::Null);
    start(&gate, RunKind::Interactive, RunLimits::default(), &[]);
    let shown = gate
        .set_next(RunLimits {
            cost_micros: Some(LimitValue::At(5_000_000)),
            tool_calls: Some(LimitValue::At(9)),
            ..RunLimits::default()
        })
        .unwrap();
    gate.add_next(one_request()).unwrap();
    let next = start(
        &gate,
        RunKind::Interactive,
        RunLimits {
            tool_calls: Some(LimitValue::At(4)),
            ..RunLimits::default()
        },
        &[],
    );
    let after = start(&gate, RunKind::Interactive, RunLimits::default(), &[]);
    assert_eq!(
        (
            shown.limits,
            shown.next.map(|next| next.limits.cost_micros),
            next.limits,
            next.next,
            after.limits
        ),
        (
            BudgetLimits::default(),
            Some(Some(LimitValue::At(5_000_000))),
            BudgetLimits {
                cost_micros: Some(5_000_000),
                tool_calls: Some(4),
                requests: Some(1),
                ..BudgetLimits::default()
            },
            None,
            BudgetLimits::default()
        )
    );
}

/// B15, B5: limits set or added while the session runs nothing are in its
/// ledger once acknowledged: a session opened again (after a crash) shows
/// them and its next run starts with them, here a session that never ran
/// whose first effect starts that run; once taken they stay used up.
#[test]
fn limits_set_while_idle_survive_a_reopen() {
    let dir = TempDir::new().unwrap();
    let open = || {
        gate_at(
            dir.path(),
            BudgetLimitsMode::Off,
            AuthClass::ApiKey,
            Value::Null,
        )
    };
    let set = open();
    set.set_next(RunLimits {
        tool_calls: Some(LimitValue::At(9)),
        ..RunLimits::default()
    })
    .unwrap();
    set.add_next(one_request()).unwrap();
    drop(set);
    let reopened = open();
    let shown = reopened.report().and_then(|report| report.next);
    reopened.ensure_run().unwrap();
    let ran = reopened.report().expect("the run's budget");
    drop(reopened);
    let after = open().report().expect("the run's budget");
    assert_eq!(
        (
            shown.map(|next| (next.limits.tool_calls, next.added.requests)),
            ran.limits,
            (ran.sources.tool_calls, ran.sources.requests),
            after.next,
        ),
        (
            Some((Some(LimitValue::At(9)), 1)),
            BudgetLimits {
                tool_calls: Some(9),
                requests: Some(1),
                ..BudgetLimits::default()
            },
            (LimitSource::Set, LimitSource::Set),
            None,
        )
    );
}

fn one_request() -> BudgetAmounts {
    BudgetAmounts {
        requests: 1,
        ..BudgetAmounts::default()
    }
}

/// Limits that cannot hold the run's first request beside its final
/// answer: nothing is sent and the text states the arithmetic.
#[test]
fn a_run_below_its_floor_sends_nothing() {
    let (_dir, gate) = gate(BudgetLimitsMode::Off, AuthClass::ApiKey, Value::Null);
    start(
        &gate,
        RunKind::Interactive,
        RunLimits {
            requests: Some(LimitValue::At(1)),
            ..RunLimits::default()
        },
        &[],
    );
    let model = SeenModel {
        provider: "test-floor".to_owned(),
        priced: true,
    };
    match gate
        .check_work(&model, one_request(), one_request())
        .unwrap()
    {
        Checked::Floor(text) => assert!(
            text.contains("requests limit 1") && text.contains("Nothing was sent"),
            "{text}"
        ),
        Checked::Go | Checked::Plan(_) => panic!("the run started below its floor"),
    }
}

fn reading(provider: &str, used_permille: u32) {
    // Each reading newer than the last: the board keeps the newest.
    static AT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
    QuotaBoard::record(
        &CredentialId::of(provider),
        PlanQuota {
            provider: provider.to_owned(),
            plan: None,
            windows: vec![QuotaWindow {
                label: "5h".to_owned(),
                window_minutes: Some(300),
                used_permille,
                resets_at_ms: Some(1_900_000_000_000),
            }],
            read_at_ms: AT.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
            source: QuotaSource::Headers,
        },
    );
}

/// With limits off, a plan window past 80 % is told once, the run goes
/// on; a reading below the line arms it again.
#[test]
fn with_limits_off_a_plan_window_past_its_share_is_told_once() {
    let (_dir, gate) = gate(BudgetLimitsMode::Off, AuthClass::Plan, Value::Null);
    let mut notices = gate.plan_notices();
    let model = SeenModel {
        provider: "test-plan-off".to_owned(),
        priced: true,
    };
    let mut told = Vec::new();
    for used in [850, 900, 100, 820] {
        reading(&model.provider, used);
        assert!(matches!(
            gate.check_work(&model, one_request(), one_request())
                .unwrap(),
            Checked::Go
        ));
        while let Ok(notice) = notices.try_recv() {
            told.push((used, notice.window.label, notice.reserve_percent));
        }
    }
    assert_eq!(
        told,
        [(850, "5h".to_owned(), 20), (820, "5h".to_owned(), 20)]
    );
}

/// With limits on, a plan window past its share wraps the run up: its
/// final answer is due, nothing is refused.
#[test]
fn with_limits_on_a_plan_window_past_its_share_wraps_the_run_up() {
    let (_dir, gate) = gate(BudgetLimitsMode::On, AuthClass::Plan, Value::Null);
    start(&gate, RunKind::Interactive, RunLimits::default(), &[]);
    let model = SeenModel {
        provider: "test-plan-on".to_owned(),
        priced: true,
    };
    reading(&model.provider, 790);
    assert!(matches!(
        gate.check_work(&model, one_request(), one_request())
            .unwrap(),
        Checked::Go
    ));
    reading(&model.provider, 800);
    match gate
        .check_work(&model, one_request(), one_request())
        .unwrap()
    {
        Checked::Plan(plan) => assert_eq!((plan.reserve_percent, plan.wrapped_by), (20, 0)),
        Checked::Go | Checked::Floor(_) => panic!("the run did not wrap up at 80 %"),
    }
    assert_eq!(gate.report().unwrap().phase, BudgetPhase::WrapUp);
}
