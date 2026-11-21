//! Runs (spec/README.md B15-B23): each run's limits fill from what the
//! principal set, its `/b` presets and, with limits on, the profile; with
//! limits off an unset dimension goes until finished. A plan window past
//! its share wraps the run up (limits on) or is told once (limits off).

use std::path::Path;
use std::sync::Arc;

use eukhe_ai::quota::{CredentialId, PlanQuota, QuotaBoard, QuotaSource, QuotaWindow};
use eukhe_types::budget::{
    AuthClass, BudgetAmounts, BudgetDimension, BudgetLimits, BudgetPhase, BudgetSources,
    LimitSource, LimitValue, RunKind, RunLimits,
};
use serde_json::{json, Value};
use tempfile::TempDir;

use super::{BelowFloor, BudgetGate, Checked, RunError, RunFacts, RunStart, SeenModel};
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
            presets: json!({ "tight": { "requests": 7 }, "starved": { "time": 40 } }),
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
    gate.add_next(two_requests()).unwrap();
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
                requests: Some(2),
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
    set.add_next(two_requests()).unwrap();
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
            Some((Some(LimitValue::At(9)), 2)),
            BudgetLimits {
                tool_calls: Some(9),
                requests: Some(2),
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

fn two_requests() -> BudgetAmounts {
    BudgetAmounts {
        requests: 2,
        ..BudgetAmounts::default()
    }
}

/// The floor a setting was refused below, if it was.
fn below<T>(result: Result<T, RunError>) -> Option<BelowFloor> {
    match result {
        Err(RunError::Floor(below)) => Some(below),
        Ok(_)
        | Err(
            RunError::Ledger(_)
            | RunError::Core(_)
            | RunError::Settings { .. }
            | RunError::Preset(_),
        ) => None,
    }
}

fn floor(
    dimension: BudgetDimension,
    limit: u64,
    source: LimitSource,
    request: u64,
    keep: u64,
) -> BelowFloor {
    BelowFloor {
        dimension,
        limit,
        source,
        request,
        keep,
    }
}

/// B17: limits below the floor of one request (8,192 tokens, 2 model
/// requests, 50 s) are refused when they are set, by every setter, naming
/// the short dimension, its limit and source, and what the request and
/// the final answer ask in it; the budget stays as it was. Limits at the
/// floor are taken.
#[test]
fn limits_below_the_floor_of_one_request_are_refused_when_set() {
    let (_dir, gate) = gate(BudgetLimitsMode::Off, AuthClass::ApiKey, Value::Null);
    let before = start(&gate, RunKind::Interactive, RunLimits::default(), &[]);
    let only = |dimension, limit| RunLimits::default().with(dimension, Some(LimitValue::At(limit)));
    let refused = [
        below(gate.set(only(BudgetDimension::Tokens, 8_191))),
        below(gate.set_standing(only(BudgetDimension::Requests, 1))),
        below(gate.set_next(only(BudgetDimension::Time, 49_999))),
        below(gate.add_next(one_request())),
        below(gate.start_run(RunStart {
            set: only(BudgetDimension::Tokens, 50),
            ..RunStart::default()
        })),
        below(gate.start_run(RunStart {
            presets: vec!["starved".to_owned()],
            ..RunStart::default()
        })),
    ];
    let kept = gate.report().map(|report| (report.limits, report.next));
    let at_floor = gate
        .set(RunLimits {
            tokens: Some(LimitValue::At(8_192)),
            time_ms: Some(LimitValue::At(50_000)),
            requests: Some(LimitValue::At(2)),
            ..RunLimits::default()
        })
        .map(|report| report.limits)
        .map_err(|error| error.to_string());
    assert_eq!(
        (refused, kept, at_floor),
        (
            [
                Some(floor(
                    BudgetDimension::Tokens,
                    8_191,
                    LimitSource::Set,
                    1_024,
                    7_168
                )),
                Some(floor(BudgetDimension::Requests, 1, LimitSource::Set, 1, 1)),
                Some(floor(
                    BudgetDimension::Time,
                    49_999,
                    LimitSource::Set,
                    30_000,
                    20_000
                )),
                Some(floor(BudgetDimension::Requests, 1, LimitSource::Set, 1, 1)),
                Some(floor(
                    BudgetDimension::Tokens,
                    50,
                    LimitSource::Set,
                    1_024,
                    7_168
                )),
                Some(floor(
                    BudgetDimension::Time,
                    40_000,
                    LimitSource::Preset("starved".to_owned()),
                    30_000,
                    20_000
                )),
            ],
            Some((before.limits, before.next)),
            Ok(BudgetLimits {
                tokens: Some(8_192),
                time_ms: Some(50_000),
                requests: Some(2),
                ..BudgetLimits::default()
            }),
        )
    );
}

/// B17: the refusal is a report of the limit, its source and the floor.
#[test]
fn the_floor_refusal_names_the_limit_its_source_and_the_floor() {
    assert_eq!(
        [
            floor(BudgetDimension::Time, 40_000, LimitSource::Set, 30_000, 20_000).to_string(),
            floor(BudgetDimension::Tokens, 50, LimitSource::Profile, 1_024, 7_168).to_string(),
        ],
        [
            "Below the floor of one request: time limit 40s; the run's first request needs at least 30s and the final answer keeps 20s. The budget is as it was.",
            "Below the floor of one request: tokens limit 50 (budget.profile); the run's first request needs at least 1024 and the final answer keeps 7168. The budget is as it was.",
        ]
    );
}

/// B17: a `budget.profile` below the floor of one request is refused at
/// the start of the run it fills, naming it; the session's first effect,
/// which starts such a run, sends nothing and reports the same.
#[test]
fn a_profile_below_the_floor_is_refused_where_it_fills() {
    let (_dir, gate) = gate(
        BudgetLimitsMode::On,
        AuthClass::ApiKey,
        json!({ "interactive": { "tokens": 50 } }),
    );
    let model = SeenModel {
        provider: "test-floor-profile".to_owned(),
        priced: true,
    };
    let first_effect = match gate
        .check_work(&model, one_request(), one_request())
        .unwrap()
    {
        Checked::Floor(text) => Some(text),
        Checked::Go | Checked::Plan(_) => None,
    };
    let expected = floor(
        BudgetDimension::Tokens,
        50,
        LimitSource::Profile,
        1_024,
        7_168,
    );
    assert_eq!(
        (
            below(gate.start_run(RunStart::default())),
            first_effect,
            gate.report()
        ),
        (Some(expected.clone()), Some(expected.to_string()), None)
    );
}

/// B17: limits above the floor of one request that cannot hold the run's
/// first request as its model and context ask it send nothing; the
/// report states the arithmetic and that the run ended there.
#[test]
fn a_run_whose_first_request_does_not_fit_sends_nothing() {
    let (_dir, gate) = gate(BudgetLimitsMode::Off, AuthClass::ApiKey, Value::Null);
    start(
        &gate,
        RunKind::Interactive,
        RunLimits {
            tokens: Some(LimitValue::At(10_000)),
            ..RunLimits::default()
        },
        &[],
    );
    let model = SeenModel {
        provider: "test-floor".to_owned(),
        priced: true,
    };
    let ask = |tokens| BudgetAmounts {
        tokens,
        requests: 1,
        ..BudgetAmounts::default()
    };
    match gate.check_work(&model, ask(4_000), ask(7_000)).unwrap() {
        Checked::Floor(text) => assert_eq!(
            text,
            "Budget too small for the run's first request: tokens limit 10000; the request needs 4000 and the final answer keeps 7000. Nothing was sent: the run ended before its first request."
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

/// B21, B15: a message sent once a run reached its limit is never
/// refused: the run wrapped up and then had nothing left, and the next
/// message starts its own run, whose limits fill afresh and whose first
/// request goes on.
#[test]
fn a_message_after_a_reached_limit_starts_its_own_run() {
    let (_dir, gate) = gate(BudgetLimitsMode::Off, AuthClass::ApiKey, Value::Null);
    let limits = RunLimits {
        requests: Some(LimitValue::At(2)),
        ..RunLimits::default()
    };
    start(&gate, RunKind::Interactive, limits, &[]);
    let three = BudgetAmounts {
        requests: 3,
        ..BudgetAmounts::default()
    };
    let mut phases = Vec::new();
    for spend in [eukhe_budget::Use::Work, eukhe_budget::Use::Final] {
        let reserved = gate
            .ledger()
            .reserve(
                "session",
                spend,
                "model:turn",
                BudgetAmounts::default(),
                BudgetAmounts::default(),
                &[three],
                eukhe_budget::REQUEST_MIN_MS,
            )
            .unwrap();
        assert!(matches!(reserved, eukhe_budget::Reserved::Refused { .. }));
        phases.push(gate.report().unwrap().phase);
    }
    let next = start(&gate, RunKind::Interactive, limits, &[]);
    let model = SeenModel {
        provider: "test-after-limit".to_owned(),
        priced: true,
    };
    assert_eq!(
        (
            phases,
            next.phase,
            next.free.requests,
            matches!(
                gate.check_work(&model, one_request(), one_request())
                    .unwrap(),
                Checked::Go
            ),
        ),
        (
            vec![BudgetPhase::WrapUp, BudgetPhase::Exhausted],
            BudgetPhase::Working,
            2,
            true,
        )
    );
}
