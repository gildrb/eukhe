use super::*;

fn parse(args: &[&str]) -> Result<BudgetCommand, String> {
    let args: Vec<String> = args.iter().map(ToString::to_string).collect();
    parse_budget_command(&args).map_err(|error| error.to_string())
}

fn command(verb: Verb, account: &str, amounts: BudgetLimits, output: Output) -> BudgetCommand {
    BudgetCommand {
        verb,
        account: account.to_owned(),
        amounts,
        output,
        daemon_socket: None,
    }
}

/// Each subcommand with its options: the daemon's account by default, the
/// amounts in their stored units (`--time` a duration), `--opt=value` and
/// `--opt value` alike.
#[test]
fn the_subcommands_read_their_account_and_amounts() {
    let none = BudgetLimits::default();
    assert_eq!(
        [
            parse(&["show"]),
            parse(&["show", "--account", "0192-sess", "--json"]),
            parse(&[
                "set",
                "--cost",
                "2",
                "--tokens=200k",
                "--time",
                "10m",
                "--tool-calls",
                "50",
                "--requests",
                "30",
            ]),
            parse(&["add", "--account=daemon", "--time", "90s"]),
            parse(&["audit"]),
        ],
        [
            Ok(command(Verb::Show, "daemon", none, Output::Text)),
            Ok(command(Verb::Show, "0192-sess", none, Output::Json)),
            Ok(command(
                Verb::Set,
                "daemon",
                BudgetLimits {
                    cost_micros: Some(2_000_000),
                    tokens: Some(200_000),
                    time_ms: Some(600_000),
                    tool_calls: Some(50),
                    requests: Some(30),
                },
                Output::Text,
            )),
            Ok(command(
                Verb::Add,
                "daemon",
                BudgetLimits {
                    time_ms: Some(90_000),
                    ..none
                },
                Output::Text,
            )),
            Ok(command(Verb::Audit, "daemon", none, Output::Text)),
        ]
    );
}

/// What does not parse names what is wrong.
#[test]
fn bad_invocations_name_what_is_wrong() {
    assert_eq!(
        [
            parse(&[]),
            parse(&["sett"]),
            parse(&["set"]),
            parse(&["show", "--tokens", "5"]),
            parse(&["add", "--tokens"]),
            parse(&["add", "--tokens", "5", "--tokens", "6"]),
            parse(&["add", "--cost", "abc"]),
            parse(&["show", "--verbose"]),
            parse(&["show", "extra"]),
        ],
        [
            Err("Missing budget command.".to_string()),
            Err("Unknown budget command: sett (did you mean \"set\"?)".to_string()),
            Err(
                "budget set needs at least one of --cost, --tokens, --time, --tool-calls, --requests"
                    .to_string()
            ),
            Err("budget show takes no amounts".to_string()),
            Err("--tokens requires a value".to_string()),
            Err("--tokens is given twice".to_string()),
            Err("--cost \"abc\": expected dollars, like 1.50 or $1.50".to_string()),
            Err("unknown option: --verbose".to_string()),
            Err("unexpected argument: extra".to_string()),
        ]
    );
}

/// On the ledger file: the daemon's account has no budget until `set`
/// gives it one; `add` raises it; `show` reads it; `audit` replays its
/// records exactly; a second `set` is refused with the ledger's message.
#[test]
fn the_daemon_account_is_set_added_to_shown_and_audited_on_its_ledger() {
    let dir = tempfile::tempdir().expect("tempdir");
    let tokens = |tokens| BudgetLimits {
        tokens: Some(tokens),
        ..BudgetLimits::default()
    };
    let run = |verb: Verb, amounts: BudgetLimits| {
        on_ledger(&command(verb, "daemon", amounts, Output::Text), dir.path())
            .map_err(|error| format!("{error:#}"))
    };
    let before = run(Verb::Show, BudgetLimits::default());
    let set = run(Verb::Set, tokens(100_000));
    let again = run(Verb::Set, tokens(5));
    let added = run(Verb::Add, tokens(25_000));
    let shown = run(Verb::Show, BudgetLimits::default());
    let audit = run(Verb::Audit, BudgetLimits::default());

    let report = |limit| BudgetReport {
        session_id: "daemon".to_string(),
        agent_session_id: "daemon".to_string(),
        limits: tokens(limit),
        free: BudgetAmounts {
            tokens: limit,
            ..BudgetAmounts::default()
        },
        ..BudgetReport::default()
    };
    assert_eq!(
        (before, set, again, added, shown, audit),
        (
            Ok(Answer::Report(None)),
            Ok(Answer::Report(Some(report(100_000)))),
            Err("budget account daemon: session daemon already has a budget".to_string()),
            Ok(Answer::Report(Some(report(125_000)))),
            Ok(Answer::Report(Some(report(125_000)))),
            Ok(Answer::Audit(BudgetAudit {
                records: 2,
                settled: BudgetAmounts::default(),
                spent: BudgetAmounts::default(),
                exact: true,
                first_mismatch: None,
            })),
        )
    );
}

/// The printed forms: the report's detail line or `no budget set` under
/// the account's name, and the JSON documents.
#[test]
fn answers_print_under_the_accounts_name() {
    let report = BudgetReport {
        session_id: "daemon".to_string(),
        agent_session_id: "daemon".to_string(),
        limits: BudgetLimits {
            requests: Some(30),
            ..BudgetLimits::default()
        },
        spent: BudgetAmounts {
            requests: 3,
            ..BudgetAmounts::default()
        },
        ..BudgetReport::default()
    };
    let show = |output| command(Verb::Show, "daemon", BudgetLimits::default(), output);
    assert_eq!(
        [
            render(&show(Output::Text), &Answer::Report(Some(report))),
            render(&show(Output::Text), &Answer::Report(None)),
            render(&show(Output::Json), &Answer::Report(None)),
        ],
        [
            "daemon: budget: 3/30 req".to_string(),
            "daemon: no budget set".to_string(),
            json!({ "account": "daemon", "budget": null }).to_string(),
        ]
    );
}
