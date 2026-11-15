use super::*;

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
