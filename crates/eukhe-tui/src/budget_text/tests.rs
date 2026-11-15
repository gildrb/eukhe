use super::*;
use eukhe_types::budget::{BudgetSources, RunKind};

fn parse(dimension: BudgetDimension, text: &str) -> Result<u64, String> {
    parse_amount(dimension, "--flag", text).map_err(|error| error.to_string())
}

/// Every unit of the typed syntax reads as its stored amount.
#[test]
fn each_unit_reads_as_its_stored_amount() {
    let cases = [
        (BudgetDimension::Cost, "1.50"),
        (BudgetDimension::Cost, "$1.50"),
        (BudgetDimension::Cost, " 2 "),
        (BudgetDimension::Cost, "0.5"),
        (BudgetDimension::Tokens, "200000"),
        (BudgetDimension::Tokens, "200k"),
        (BudgetDimension::Tokens, "1.5m"),
        (BudgetDimension::Tokens, "1.5K"),
        (BudgetDimension::Time, "90s"),
        (BudgetDimension::Time, "10m"),
        (BudgetDimension::Time, "2h"),
        (BudgetDimension::Time, "1.5H"),
        (BudgetDimension::ToolCalls, "50"),
        (BudgetDimension::Requests, "30"),
    ];
    let got: Vec<Result<u64, String>> = cases
        .iter()
        .map(|(dimension, text)| parse(*dimension, text))
        .collect();
    let want: Vec<Result<u64, String>> = [
        1_500_000, 1_500_000, 2_000_000, 500_000, 200_000, 200_000, 1_500_000, 1_500, 90_000,
        600_000, 7_200_000, 5_400_000, 50, 30,
    ]
    .into_iter()
    .map(Ok)
    .collect();
    assert_eq!(got, want);
}

/// A fraction below the stored unit rounds up: a budget never reads as
/// less than what was typed, and never as zero.
#[test]
fn an_amount_below_the_stored_unit_rounds_up() {
    assert_eq!(
        [
            parse(BudgetDimension::Cost, "0.0000001"),
            parse(BudgetDimension::Cost, "1.0000005"),
            parse(BudgetDimension::Cost, "0.00000000000000000001"),
            parse(BudgetDimension::Tokens, "1.0001k"),
            parse(BudgetDimension::Time, "0.0004s"),
        ],
        [Ok(1), Ok(1_000_001), Ok(1), Ok(1_001), Ok(1)]
    );
}

/// The largest amount of each dimension is accepted; one unit more, and
/// any number of digits past it, is refused by name and value.
#[test]
fn each_dimension_holds_at_most_the_ledgers_maximum() {
    let nines = "9".repeat(60);
    assert_eq!(
        [
            parse(BudgetDimension::Cost, "9999999.999999"),
            parse(BudgetDimension::Cost, "9999999.9999991"),
            parse(BudgetDimension::Tokens, "9999999999999"),
            parse(BudgetDimension::Tokens, "10000000000000"),
            parse(BudgetDimension::Tokens, &nines),
            parse(BudgetDimension::Time, "2777777h"),
            parse(BudgetDimension::Time, "2777778h"),
            parse(BudgetDimension::ToolCalls, "9999999999999"),
            parse(BudgetDimension::ToolCalls, "10000000000000"),
            parse(BudgetDimension::Requests, "9999999999999"),
            parse(BudgetDimension::Requests, "10000000000000"),
        ],
        [
            Ok(BUDGET_AMOUNT_MAX),
            Err("--flag \"9999999.9999991\": a budget holds at most $9999999.999999".to_string()),
            Ok(BUDGET_AMOUNT_MAX),
            Err(
                "--flag \"10000000000000\": a budget holds at most 9999999999999 tokens"
                    .to_string()
            ),
            Err(format!(
                "--flag \"{nines}\": a budget holds at most 9999999999999 tokens"
            )),
            Ok(9_999_997_200_000),
            Err("--flag \"2777778h\": a budget holds at most 2777777h".to_string()),
            Ok(BUDGET_AMOUNT_MAX),
            Err(
                "--flag \"10000000000000\": a budget holds at most 9999999999999 tool calls"
                    .to_string()
            ),
            Ok(BUDGET_AMOUNT_MAX),
            Err(
                "--flag \"10000000000000\": a budget holds at most 9999999999999 requests"
                    .to_string()
            ),
        ]
    );
}

/// Text that is not an amount of its dimension, and zero, are refused
/// with the name and the value.
#[test]
fn bad_input_names_the_flag_and_the_value() {
    let cases = [
        (BudgetDimension::Cost, "abc"),
        (BudgetDimension::Cost, ""),
        (BudgetDimension::Cost, "-1"),
        (BudgetDimension::Cost, "1."),
        (BudgetDimension::Cost, ".50"),
        (BudgetDimension::Cost, "1.2.3"),
        (BudgetDimension::Cost, "0"),
        (BudgetDimension::Tokens, "12x"),
        (BudgetDimension::Tokens, "k"),
        (BudgetDimension::Tokens, "0k"),
        (BudgetDimension::Time, "90"),
        (BudgetDimension::Time, "10 m"),
        (BudgetDimension::Time, "0s"),
        (BudgetDimension::ToolCalls, "1.5"),
        (BudgetDimension::ToolCalls, "5k"),
        (BudgetDimension::ToolCalls, "0"),
        (BudgetDimension::Requests, "2.5"),
        (BudgetDimension::Requests, "0"),
    ];
    let got: Vec<String> = cases
        .iter()
        .map(|(dimension, text)| parse(*dimension, text).expect_err("refused"))
        .collect();
    assert_eq!(
        got,
        [
            "--flag \"abc\": expected dollars, like 1.50 or $1.50",
            "--flag \"\": expected dollars, like 1.50 or $1.50",
            "--flag \"-1\": expected dollars, like 1.50 or $1.50",
            "--flag \"1.\": expected dollars, like 1.50 or $1.50",
            "--flag \".50\": expected dollars, like 1.50 or $1.50",
            "--flag \"1.2.3\": expected dollars, like 1.50 or $1.50",
            "--flag \"0\": a budget amount is more than zero",
            "--flag \"12x\": expected a token count, like 200000, 200k or 1.5m",
            "--flag \"k\": expected a token count, like 200000, 200k or 1.5m",
            "--flag \"0k\": a budget amount is more than zero",
            "--flag \"90\": expected a duration, like 90s, 10m or 2h",
            "--flag \"10 m\": expected a duration, like 90s, 10m or 2h",
            "--flag \"0s\": a budget amount is more than zero",
            "--flag \"1.5\": expected a whole number of tool calls, like 50",
            "--flag \"5k\": expected a whole number of tool calls, like 50",
            "--flag \"0\": a budget amount is more than zero",
            "--flag \"2.5\": expected a whole number of model requests, like 30",
            "--flag \"0\": a budget amount is more than zero",
        ]
    );
}

/// `/budget set` and `/budget add` take any subset of the five keys.
#[test]
fn assignments_name_any_subset_of_the_dimensions() {
    let assignments = |text: &str| parse_assignments(text).map_err(|error| error.to_string());
    let keys = "cost=<dollars>, tokens=<n>, time=<duration>, calls=<n>, requests=<n>";
    assert_eq!(
        [
            assignments("cost=2 tokens=200k time=10m calls=50 requests=30"),
            assignments("  calls=3  "),
            assignments(""),
            assignments("cost=1 cost=2"),
            assignments("money=1"),
            assignments("2"),
            assignments("time=10"),
        ],
        [
            Ok(BudgetLimits {
                cost_micros: Some(2_000_000),
                tokens: Some(200_000),
                time_ms: Some(600_000),
                tool_calls: Some(50),
                requests: Some(30),
            }),
            Ok(BudgetLimits {
                tool_calls: Some(3),
                ..BudgetLimits::default()
            }),
            Err(format!("name at least one of {keys}")),
            Err("cost is given twice".to_string()),
            Err(format!("\"money=1\": expected one of {keys}")),
            Err(format!("\"2\": expected one of {keys}")),
            Err("time \"10\": expected a duration, like 90s, 10m or 2h".to_string()),
        ]
    );
}

/// When the reports below were read (Unix milliseconds): 2027-01-15
/// 07:53:10 UTC, 6m 50s before their deadline.
const NOW_MS: u64 = 1_800_000_000_000 - 410_000;

/// A report with every dimension limited: $0.42 of $2.00, 31.0k of 200k
/// tokens, 12 of 50 calls and 3 of 30 requests used (spent, held and lent
/// added up), a deadline 10 minutes after it was set, as its owner sees
/// it.
fn report(phase: BudgetPhase, short: Option<BudgetDimension>) -> BudgetReport {
    BudgetReport {
        session_id: "sess-1".to_string(),
        agent_session_id: "sess-1".to_string(),
        limits: BudgetLimits {
            cost_micros: Some(2_000_000),
            tokens: Some(200_000),
            time_ms: Some(600_000),
            tool_calls: Some(50),
            requests: Some(30),
        },
        free: BudgetAmounts {
            cost_micros: 1_580_000,
            tokens: 169_000,
            time_ms: 410_000,
            tool_calls: 38,
            requests: 27,
        },
        held: BudgetAmounts {
            cost_micros: 20_000,
            tokens: 1_000,
            tool_calls: 1,
            requests: 1,
            ..BudgetAmounts::default()
        },
        spent: BudgetAmounts {
            cost_micros: 300_000,
            tokens: 20_000,
            tool_calls: 9,
            requests: 2,
            ..BudgetAmounts::default()
        },
        lent: BudgetAmounts {
            cost_micros: 100_000,
            tokens: 10_000,
            tool_calls: 2,
            ..BudgetAmounts::default()
        },
        over: BudgetAmounts::default(),
        phase,
        short,
        deadline_ms: Some(1_800_000_000_000),
        parent_session_id: None,
        kind: None,
        sources: eukhe_types::budget::BudgetSources::default(),
        program_runs: 0,
        plan: None,
    }
}

/// The line in each phase, with and without an overrun, with only some
/// dimensions limited, and as time passes: time reads what is left until
/// the deadline at the moment the line is made, 0 once it passed. A
/// report of a ledger written before runs were recorded (no kind) reads
/// every limit as set.
#[test]
fn the_report_line_names_use_time_left_phase_and_overrun() {
    let overrun = BudgetReport {
        over: BudgetAmounts {
            cost_micros: 10_000,
            tokens: 1_200,
            ..BudgetAmounts::default()
        },
        ..report(BudgetPhase::Exhausted, Some(BudgetDimension::ToolCalls))
    };
    let tokens_only = BudgetReport {
        limits: BudgetLimits {
            tokens: Some(1_500_000),
            ..BudgetLimits::default()
        },
        over: BudgetAmounts {
            cost_micros: 300,
            ..BudgetAmounts::default()
        },
        deadline_ms: None,
        ..report(BudgetPhase::WrapUp, Some(BudgetDimension::Tokens))
    };
    let working = report(BudgetPhase::Working, None);
    let all = "3/30 requests, 12/50 tool calls, 6m 50s left, $0.42/$2.00, 31.0k/200k tok (set)";
    assert_eq!(
        [
            report_line(&working, NOW_MS),
            report_line(&working, NOW_MS + 400_000),
            report_line(&working, NOW_MS + 500_000),
            report_line(
                &report(BudgetPhase::WrapUp, Some(BudgetDimension::Cost)),
                NOW_MS
            ),
            report_line(
                &report(BudgetPhase::Exhausted, Some(BudgetDimension::Time)),
                NOW_MS
            ),
            report_line(&report(BudgetPhase::Exhausted, None), NOW_MS),
            report_line(&overrun, NOW_MS),
            report_line(&tokens_only, NOW_MS),
            report_line(&BudgetReport::default(), NOW_MS),
        ],
        [
            format!("budget: {all}"),
            "budget: 3/30 requests, 12/50 tool calls, 10s left, $0.42/$2.00, 31.0k/200k tok (set)"
                .to_string(),
            "budget: 3/30 requests, 12/50 tool calls, 0s left, $0.42/$2.00, 31.0k/200k tok (set)"
                .to_string(),
            format!("budget: {all}; wrap-up"),
            format!("budget: {all}; exhausted (time)"),
            format!("budget: {all}; exhausted"),
            format!("budget: {all}; exhausted (tool calls); over $0.01, 1.2k tok"),
            "budget: 31.0k/1.5M tok (set); $0.42, 3 requests, 12 tool calls; wrap-up; over $0.0003"
                .to_string(),
            "budget: until finished (default)".to_string(),
        ]
    );
}

/// What a run spent: $0.42, 31.0k tokens, 12 requests, 41 tool calls and
/// 3 programs, 2 minutes into a run of kind `kind` with `limits` decided
/// by `sources`.
fn run(kind: RunKind, limits: BudgetLimits, sources: BudgetSources) -> BudgetReport {
    BudgetReport {
        session_id: "sess-1".to_string(),
        agent_session_id: "sess-1".to_string(),
        limits,
        spent: BudgetAmounts {
            cost_micros: 420_000,
            tokens: 31_000,
            tool_calls: 41,
            requests: 12,
            ..BudgetAmounts::default()
        },
        deadline_ms: limits.time_ms.map(|_| NOW_MS + 14_280_000),
        kind: Some(kind),
        sources,
        program_runs: 3,
        ..BudgetReport::default()
    }
}

/// The limits profile's requests, tool calls and time (4 h) with money
/// declared unlimited by the principal.
fn limits_on() -> BudgetReport {
    run(
        RunKind::Interactive,
        BudgetLimits {
            time_ms: Some(14_400_000),
            tool_calls: Some(4_000),
            requests: Some(3_200),
            ..BudgetLimits::default()
        },
        BudgetSources {
            cost_micros: LimitSource::Set,
            time_ms: LimitSource::LimitsProfile,
            tool_calls: LimitSource::LimitsProfile,
            requests: LimitSource::LimitsProfile,
            ..BudgetSources::default()
        },
    )
}

/// The budget line groups dimensions by who decided their limit, in the
/// owner-approved wording, with limits on, without limits, and with a
/// `/b` preset; the status line shows only the limited dimensions.
#[test]
fn the_budget_line_groups_dimensions_by_source() {
    let until_finished = run(
        RunKind::Headless,
        BudgetLimits::default(),
        BudgetSources::default(),
    );
    let preset = run(
        RunKind::Interactive,
        BudgetLimits {
            requests: Some(800),
            ..BudgetLimits::default()
        },
        BudgetSources {
            requests: LimitSource::Preset("quick".to_string()),
            time_ms: LimitSource::Set,
            ..BudgetSources::default()
        },
    );
    assert_eq!(
        [
            report_line(&limits_on(), NOW_MS),
            report_line(&until_finished, NOW_MS),
            report_line(&preset, NOW_MS),
            status_text(&limits_on(), NOW_MS),
            status_text(&until_finished, NOW_MS),
            status_text(&preset, NOW_MS),
        ],
        [
            "budget: 12/3,200 requests, 41/4,000 tool calls, 3h 58m left (limits on); $0.42 spent, no money limit (set); 31.0k tok; 3 program runs (unconfined, a lower bound)",
            "budget: until finished (default); spent $0.42, 31.0k tok, 12 requests, 41 tool calls; 3 program runs (unconfined, a lower bound)",
            "budget: 12/800 requests (/b quick); no time limit (set); $0.42, 31.0k tok, 41 tool calls; 3 program runs (unconfined, a lower bound)",
            "12/3,200 req, 41/4,000 calls, 3h 58m left (limits on)",
            "until finished",
            "12/800 req (/b quick)",
        ]
    );
}

/// `--json` names each dimension's limit and its source in full.
#[test]
fn the_json_limits_name_each_source_in_full() {
    assert_eq!(
        limits_json(&limits_on()),
        serde_json::json!({
            "costMicros": { "limit": "unlimited", "source": "set by the principal" },
            "tokens": { "limit": "unlimited", "source": "until finished (default)" },
            "timeMs": { "limit": 14_400_000, "source": "limits profile" },
            "toolCalls": { "limit": 4_000, "source": "limits profile" },
            "requests": { "limit": 3_200, "source": "limits profile" },
        })
    );
}

/// `/budget set` takes `unlimited` as a limit; `/budget add` does not.
#[test]
fn set_takes_unlimited_and_add_takes_amounts() {
    assert_eq!(
        (
            parse_limits("cost=unlimited requests=30").map_err(|error| error.to_string()),
            parse_assignments("cost=unlimited").map_err(|error| error.to_string()),
        ),
        (
            Ok(RunLimits {
                cost_micros: Some(LimitValue::Unlimited),
                requests: Some(LimitValue::At(30)),
                ..RunLimits::default()
            }),
            Err("cost \"unlimited\": expected dollars, like 1.50 or $1.50".to_string()),
        )
    );
}

/// A message's `/b` prefix names presets and limits; a message without
/// one has none, and a value that does not read is refused by name.
#[test]
fn the_b_prefix_reads_presets_and_limits() {
    let read = |text: &str| {
        run_prefix(text, &["quick", "deep", "mine"]).map_err(|error| error.to_string())
    };
    let ask = |presets: &[&str], set: RunLimits, rest: &str| {
        Ok(Some(RunAsk {
            presets: presets.iter().map(|name| (*name).to_owned()).collect(),
            set,
            rest: rest.to_owned(),
        }))
    };
    assert_eq!(
        [
            read("fix the parser"),
            read("/budget"),
            read("/b quick fix the parser"),
            read("/b mine cost=2 time=unlimited fix it"),
            read("/b cost=abc fix it"),
            read("/b cost=1 cost=2 fix it"),
        ],
        [
            Ok(None),
            Ok(None),
            ask(&["quick"], RunLimits::default(), "fix the parser"),
            ask(
                &["mine"],
                RunLimits {
                    cost_micros: Some(LimitValue::At(2_000_000)),
                    time_ms: Some(LimitValue::Unlimited),
                    ..RunLimits::default()
                },
                "fix it"
            ),
            Err("cost \"abc\": expected dollars, like 1.50 or $1.50".to_string()),
            Err("cost is given twice".to_string()),
        ]
    );
}

/// The full answer adds the deadline, and the account's owner for an
/// agent that draws from another session's budget.
#[test]
fn the_report_detail_adds_the_deadline_and_the_owner() {
    let child = BudgetReport {
        agent_session_id: "sess-2".to_string(),
        limits: BudgetLimits {
            requests: Some(30),
            ..BudgetLimits::default()
        },
        deadline_ms: None,
        ..report(BudgetPhase::Working, None)
    };
    assert_eq!(
        [
            report_detail(&report(BudgetPhase::Working, None), NOW_MS),
            report_detail(&child, NOW_MS),
        ],
        [
            "budget: 3/30 requests, 12/50 tool calls, 6m 50s left, $0.42/$2.00, 31.0k/200k tok (set); deadline 2027-01-15 08:00:00 UTC",
            "budget: 3/30 requests (set); $0.42, 31.0k tok, 12 tool calls; from the budget of sess-1",
        ]
    );
}

/// The amount forms at their boundaries.
#[test]
fn amounts_read_in_the_units_of_their_size() {
    assert_eq!(
        [
            dollars(0),
            dollars(1),
            dollars(4_999),
            dollars(5_000),
            dollars(1_234_567),
            tokens(999),
            tokens(1_000),
            tokens(99_999),
            tokens(100_000),
            tokens(2_540_000),
            tokens(250_000_000),
            duration(999),
            duration(59_000),
            duration(60_000),
            duration(3_600_000),
            duration(7_530_000),
            utc_time(0),
            utc_time(951_782_400_000),
            utc_time(1_762_873_327_000),
        ],
        [
            "$0.00",
            "$0.0001",
            "$0.0050",
            "$0.01",
            "$1.23",
            "999",
            "1.0k",
            "99.9k",
            "100k",
            "2.5M",
            "250M",
            "0s",
            "59s",
            "1m",
            "1h",
            "2h 5m",
            "1970-01-01 00:00:00 UTC",
            "2000-02-29 00:00:00 UTC",
            "2025-11-11 15:02:07 UTC",
        ]
    );
}

/// The audit line: exact, a record the core does not reproduce, and
/// settled spends that do not add up to the reported total.
#[test]
fn the_audit_line_says_exact_or_where_it_breaks() {
    let settled = BudgetAmounts {
        cost_micros: 420_000,
        tokens: 31_000,
        tool_calls: 12,
        requests: 3,
        ..BudgetAmounts::default()
    };
    let audit = |spent: BudgetAmounts, exact: bool, first_mismatch: Option<u64>| BudgetAudit {
        records: 14,
        settled,
        spent,
        exact,
        first_mismatch,
    };
    assert_eq!(
        [
            audit_line(&audit(settled, true, None)),
            audit_line(&audit(settled, false, Some(7))),
            audit_line(&audit(BudgetAmounts::default(), false, None)),
        ],
        [
            "ledger exact: 14 records, settled $0.42, 31.0k tok, 12 calls, 3 req",
            "ledger MISMATCH at record 7",
            "ledger MISMATCH: 14 records, settled $0.42, 31.0k tok, 12 calls, 3 req but reports nothing spent",
        ]
    );
}
