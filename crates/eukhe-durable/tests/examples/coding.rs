//! Examples 24, 25, and 31: child tasks, compaction, and reload. Each test
//! runs the example into a buffer and asserts what the TS example prints
//! (`test/examples/NN-*.ts`), with arrays and objects printed as JSON.

#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/24-child-tasks.rs"]
mod ex24_child_tasks;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/25-compaction.rs"]
mod ex25_compaction;
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
/// every charge first; parallel invocations and async storage I/O do not
/// guarantee it.
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
            "details ".repeat(400)
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
    // A compaction keeps the most of the newest entries that stay within
    // keepRecentTokens (400) and leave the context within half the size
    // where compaction starts: here the newest turn alone.
    expected.push_str(&block(
        "after \"Which day trips?\" (answered): 3 messages in context, 7 entries stored",
        Some("threshold"),
        &[
            summary.to_owned(),
            user("Which day trips?"),
            details("Which day trips?"),
        ],
    ));
    expected.push_str(&block(
        "after \"Any museums?\" (answered): 6 messages in context, 10 entries stored",
        Some("threshold"),
        &[
            system.to_owned(),
            summary.to_owned(),
            user("Which day trips?"),
            details("Which day trips?"),
            user("Any museums?"),
            details("Any museums?"),
        ],
    ));
    expected.push_str(&block(
        "after \"Nightlife?\" (answered): 3 messages in context, 13 entries stored",
        Some("threshold"),
        &[
            summary.to_owned(),
            user("Nightlife?"),
            details("Nightlife?"),
        ],
    ));
    expected.push_str("\nmanual compaction finished; its summary is queued\n");
    expected.push_str("after the answer, the summary is done\n");
    expected.push_str(&block(
        "after compact(): 4 messages in context, 17 entries stored",
        Some("manual"),
        &[
            system.to_owned(),
            summary.to_owned(),
            user("How do we get around?"),
            details("How do we get around?"),
        ],
    ));
    expected.push_str(&block(
        "after \"What should we pack?\" (answered): 6 messages in context, 20 entries stored",
        Some("manual"),
        &[
            system.to_owned(),
            summary.to_owned(),
            user("How do we get around?"),
            details("How do we get around?"),
            user("What should we pack?"),
            details("What should we pack?"),
        ],
    ));
    // The compactions leave the context under the blocking threshold, so the
    // request the provider rejects as too long compacts (the overflow
    // summary) and is answered on its retry.
    expected.push_str(&block(
        "after \"Summarize the plan for my partner\" (answered): 4 messages in context, 25 entries stored",
        Some("overflow"),
        &[
            system.to_owned(),
            summary.to_owned(),
            user("Summarize the plan for my partner"),
            details("Summarize the plan for my partner"),
        ],
    ));
    assert_eq!(printed!(ex25_compaction), expected);
}

#[tokio::test(flavor = "multi_thread")]
async fn reload_and_restart() {
    assert_eq!(
        printed!(ex31_reload_and_restart),
        "call running during the reload: v1\nnext call: v2\nafter restart, before install: []\nafter install: [\"version\"]\n"
    );
}
