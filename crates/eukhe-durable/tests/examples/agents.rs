//! Examples 16 and 20–23: real models, the inbox, late joins, and
//! subagents. 16 needs `OPENAI_API_KEY` and is only compiled here; every
//! other example runs against the faux provider.

#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/16-real-model.rs"]
mod ex16_real_model;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/20-inbox.rs"]
mod ex20_inbox;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/21-late-join.rs"]
mod ex21_late_join;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/22-subagent-foreground.rs"]
mod ex22_subagent_foreground;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/23-subagent-background.rs"]
mod ex23_subagent_background;

fn text(out: Vec<u8>) -> String {
    String::from_utf8(out).expect("examples print UTF-8")
}

#[tokio::test]
async fn ex20_inbox_queues_steers_lands_display_writes_and_rejects_while_busy() {
    let mut out = Vec::new();
    ex20_inbox::run(&mut out, &[], None).await.unwrap();
    assert_eq!(
        text(out),
        r#"rejected: Conversation 1 is busy
withdraw: aborted
inbox: ["10 followUp","11 steer"]
first: done 
follow-up: done 
steer: done 
note: done 
withdrawn: unanswered aborted
transcript: ["pi.user","app.note","pi.assistant","pi.user","pi.user","pi.assistant"]
"#
    );
}

#[tokio::test]
async fn ex21_late_join_gets_the_state_first_and_then_changes() {
    let mut out = Vec::new();
    ex21_late_join::run(&mut out, &[], None).await.unwrap();
    let out = text(out);
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(
        lines[0],
        r#"view entries: ["pi.user","pi.system","pi.assistant"]"#
    );
    assert!(
        lines[1].starts_with(r#"view tool slot: running "1\n"#),
        "{out}"
    );
    assert!(lines[2].starts_with(r#"view output now: "1\n"#), "{out}");
    assert_eq!(lines[3], r#"snapshot tools: ["count running"]"#);
    let all = r#""1\n2\n3\n4\n5\n6\n7\n8\n9\n10\n""#;
    assert!(
        lines.contains(&format!("view output now: {all}").as_str()),
        "{out}"
    );
    assert!(
        lines.contains(&format!("event output now: {all}").as_str()),
        "{out}"
    );
    let end = lines
        .iter()
        .position(|line| *line == "event: tool_execution_end")
        .expect("tool end event");
    let rest: Vec<&str> = lines[end..]
        .iter()
        .copied()
        .filter(|line| !line.starts_with("event text delta: "))
        .collect();
    assert_eq!(
        rest,
        [
            "event: tool_execution_end",
            "event: message_start",
            "event: message_end",
            "event: turn_end",
            "event: turn_start",
            "event: message_start",
            "event: message_end",
            "event: turn_end",
            "event: run_end",
            "event: submission",
            "event: usage_changed",
        ]
    );
    let deltas: String = lines[end..]
        .iter()
        .filter_map(|line| line.strip_prefix("event text delta: "))
        .map(|delta| serde_json::from_str::<String>(delta).unwrap())
        .collect();
    assert!(
        "Counted to ten, and this answer streams slowly.".contains(&deltas),
        "{out}"
    );
}

#[tokio::test]
async fn ex22_subagent_foreground_shows_the_child_under_its_call() {
    let mut out = Vec::new();
    ex22_subagent_foreground::run(&mut out, &[], None)
        .await
        .unwrap();
    assert_eq!(
        text(out),
        r#"tool subagent({"task":"Name three prime numbers."})
  assistant: 2, 3, and 5.
assistant: The subagent says: 2, 3, and 5.
"#
    );
}

#[tokio::test]
async fn ex23_subagent_background_reports_across_a_restart() {
    let mut out = Vec::new();
    ex23_subagent_background::run(&mut out, &[], None)
        .await
        .unwrap();
    assert_eq!(
        text(out),
        r#"
> Start a subagent named reader that summarizes Moby Dick.
  subagent spawn reader "Summarize the plot of Moby Dick."
  → Started reader.
OK. Started reader.

> reader: A whale, a captain, an obsession.
Noted.

> Ask reader to summarize every chapter.
  subagent send reader "Now go through all chapters in detail."
  → Sent to reader.
OK. Sent to reader.

> Stop reader.
  subagent stop reader
  → Stopped reader.
OK. Stopped reader.

> What are my subagents doing?
  subagent status
  → reader: idle
OK. reader: idle

> Ask reader for the whale's name.
  subagent send reader "What is the whale called?"
  → Sent to reader.

  (process restarts)
OK. Sent to reader.

> reader: Moby Dick.
Noted.
"#
    );
}
