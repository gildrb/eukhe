//! Examples 24–31: child tasks, compaction, and coding-agent setups. Each test
//! runs the example into a buffer and asserts what the TS example prints
//! (`test/examples/NN-*.ts`), with arrays and objects printed as JSON.

#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/24-child-tasks.rs"]
mod ex24_child_tasks;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/25-compaction.rs"]
mod ex25_compaction;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/26-coding-agent.rs"]
mod ex26_coding_agent;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/27-plan-mode.rs"]
mod ex27_plan_mode;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/28-reviewer.rs"]
mod ex28_reviewer;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/29-sandbox-per-conversation.rs"]
mod ex29_sandbox_per_conversation;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/30-tool-override.rs"]
mod ex30_tool_override;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/31-reload-and-restart.rs"]
mod ex31_reload_and_restart;

/// The printed text of an example's `run`.
macro_rules! printed {
    ($example:ident) => {{
        let mut out = Vec::new();
        $example::run(&mut out, &[], None)
            .await
            .expect("the example runs");
        String::from_utf8(out).expect("the example prints UTF-8")
    }};
}

/// `printed` with each run of consecutive `  payment ` lines sorted: sibling
/// payments abort in parallel invocations on the multi-thread runtime, so
/// their order varies (one JS event loop prints them in creation order).
fn sort_payment_aborts(printed: &str) -> String {
    let mut lines: Vec<&str> = printed.lines().collect();
    let mut start = 0;
    while start < lines.len() {
        let end = start
            + lines[start..]
                .iter()
                .take_while(|line| line.starts_with("  payment "))
                .count();
        lines[start..end].sort_unstable();
        start = end + 1;
    }
    lines.iter().fold(String::new(), |mut text, line| {
        text.push_str(line);
        text.push('\n');
        text
    })
}

/// `printed` without `, refunded` in the declined-card block. `failFast`
/// aborts the sibling payments when the expired card fails; whether a
/// sibling's charge phase had already run (and so refunds) depends on how its
/// invocation was scheduled against that failure. One JS event loop starts
/// every charge first; parallel invocations and the SQLite worker thread do
/// not guarantee it.
fn without_declined_refunds(printed: &str) -> String {
    let mut declined = false;
    printed.lines().fold(String::new(), |mut text, line| {
        match line {
            "One card is declined:" => declined = true,
            "The customer cancels:" => declined = false,
            _ => {}
        }
        let line = match line.strip_suffix(", refunded") {
            Some(stripped) if declined => stripped,
            _ => line,
        };
        text.push_str(line);
        text.push('\n');
        text
    })
}

#[tokio::test(flavor = "multi_thread")]
async fn child_tasks() {
    assert_eq!(
        without_declined_refunds(&sort_payment_aborts(&printed!(ex24_child_tasks))),
        "\
One card is declined:
  payment visa-1 aborted
  payment visa-3 aborted
  payment visa-4 aborted
  payments: aborted, failed, aborted, aborted
  checkout: failed
The customer cancels:
  example.checkout 12: waiting on 13, 14, 15, 16
    example.payment 13: running
    example.payment 14: running
    example.payment 15: running
    example.payment 16: running
  payment visa-5 aborted, refunded
  payment visa-6 aborted, refunded
  payment visa-7 aborted, refunded
  payment visa-8 aborted, refunded
  checkout aborted
  checkout: aborted
The process stops while the payments run, and a new one continues:
  payments: completed, completed, completed, completed
  checkout: completed
"
    );
}

// One thread, like the example's `main` and the JS event loop: the background compaction races the chat.
#[tokio::test(flavor = "current_thread")]
#[expect(
    clippy::too_many_lines,
    reason = "every context the TS example prints, in order"
)]
async fn compaction() {
    let details = |question: &str| {
        let line = format!(
            "A detailed answer to \"{question}\": {}",
            "details ".repeat(200)
        );
        format!("  assistant {}", &line[..70])
    };
    let summary =
        "  user      The conversation history before this point was compacted into the foll";
    let user = |question: &str| format!("  user      {question}");
    let system = "  system    (system prompt)";
    let block = |label: &str, head: Option<&str>, lines: &[String]| {
        let mut text = format!("\n{label}\n");
        if let Some(head) = head {
            text.push_str("  (");
            text.push_str(head);
            text.push_str(" compaction summary first)\n");
        }
        for line in lines {
            text.push_str(line);
            text.push('\n');
        }
        text
    };
    let mut expected = String::new();
    expected.push_str(&block(
        "after \"Where should we stay?\" (answered): 2 messages in context, 2 entries stored",
        None,
        &[
            user("Where should we stay?"),
            details("Where should we stay?"),
        ],
    ));
    expected.push_str(&block(
        "after \"What should we eat?\" (answered): 4 messages in context, 4 entries stored",
        None,
        &[
            user("Where should we stay?"),
            details("Where should we stay?"),
            user("What should we eat?"),
            details("What should we eat?"),
        ],
    ));
    expected.push_str(&block(
        "after \"Which day trips?\" (answered): 4 messages in context, 7 entries stored",
        Some("threshold"),
        &[
            summary.to_owned(),
            details("What should we eat?"),
            user("Which day trips?"),
            details("Which day trips?"),
        ],
    ));
    expected.push_str(&block(
        "after \"Any museums?\" (answered): 7 messages in context, 10 entries stored",
        Some("threshold"),
        &[
            summary.to_owned(),
            details("What should we eat?"),
            user("Which day trips?"),
            details("Which day trips?"),
            user("Any museums?"),
            system.to_owned(),
            details("Any museums?"),
        ],
    ));
    expected.push_str(&block(
        "after \"Nightlife?\" (answered): 5 messages in context, 14 entries stored",
        Some("threshold"),
        &[
            summary.to_owned(),
            details("Any museums?"),
            user("Nightlife?"),
            system.to_owned(),
            details("Nightlife?"),
        ],
    ));
    expected.push_str("\nmanual compaction finished; its summary is queued\n");
    expected.push_str("after the answer, the summary is done\n");
    expected.push_str(&block(
        "after compact(): 4 messages in context, 17 entries stored",
        Some("manual"),
        &[
            summary.to_owned(),
            details("Nightlife?"),
            user("How do we get around?"),
            details("How do we get around?"),
        ],
    ));
    expected.push_str(&block(
        "after \"What should we pack?\" (answered): 7 messages in context, 20 entries stored",
        Some("manual"),
        &[
            summary.to_owned(),
            details("Nightlife?"),
            user("How do we get around?"),
            details("How do we get around?"),
            user("What should we pack?"),
            system.to_owned(),
            details("What should we pack?"),
        ],
    ));
    expected.push_str(&block(
        "after \"Summarize the plan for my partner\" (model_error): 4 messages in context, 24 entries stored",
        Some("threshold"),
        &[
            summary.to_owned(),
            details("What should we pack?"),
            user("Summarize the plan for my partner"),
            system.to_owned(),
        ],
    ));
    assert_eq!(printed!(ex25_compaction), expected);
}

#[tokio::test(flavor = "multi_thread")]
async fn coding_agent() {
    let printed = printed!(ex26_coding_agent);
    let lines: Vec<&str> = printed.lines().collect();
    assert_eq!(lines.len(), 2, "{printed}");
    let workspace = lines[0]
        .strip_prefix("bash ran in: ")
        .expect("the first line names the directory");
    assert!(
        workspace.contains("/pi-durable-agent-"),
        "bash ran in the workspace: {workspace}"
    );
    assert_eq!(lines[1], format!("bash ran in: {workspace}/app"));
}

#[tokio::test(flavor = "multi_thread")]
async fn plan_mode() {
    assert_eq!(
        printed!(ex27_plan_mode),
        r#"tools: ["read","write","edit","bash"]
plan mode tools: ["read","submit_plan"]
plan: ["Read PORT from the environment","Default to 3000"]
tools again: ["read","write","edit","bash"]
system: {"sections":{"plan_mode":"<plan_mode>\nYou are in plan mode. Read the code, then call submit_plan. Change nothing.\n</plan_mode>"},"added":["read","submit_plan"]}
system: {"sections":{"plan_mode":null},"added":["write","edit","bash"],"removed":["submit_plan"]}
"#
    );
}

#[tokio::test(flavor = "multi_thread")]
async fn reviewer() {
    assert_eq!(
        printed!(ex28_reviewer),
        r#"reviewer: small ["coding-tools","reviewer"] ["read"] true
> Review user.ts.
reviewer: 1. `name` does not handle a missing user.
> Look again for anything you missed. Say "No further findings." when there is nothing left.
reviewer: 2. `user` has no type. No further findings.
"#
    );
}

#[tokio::test(flavor = "multi_thread")]
async fn sandbox_per_conversation() {
    assert_eq!(
        printed!(ex29_sandbox_per_conversation),
        "alice's sandbox: from alice\nbob's sandbox: from bob\n"
    );
}

#[tokio::test(flavor = "multi_thread")]
async fn tool_override() {
    assert_eq!(
        printed!(ex30_tool_override),
        "plain conversation: venv:\npython conversation: venv: <project>/.venv\ntimed bash calls: 2\n"
    );
}

#[tokio::test(flavor = "multi_thread")]
async fn reload_and_restart() {
    assert_eq!(
        printed!(ex31_reload_and_restart),
        "call running during the reload: v1\nnext call: v2\nafter restart, before install: []\nafter install: [\"version\"]\n"
    );
}
