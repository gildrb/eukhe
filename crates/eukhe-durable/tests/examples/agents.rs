//! Examples 16–23: real models, coding tools, print and JSON modes, the inbox,
//! late joins, and subagents. 16 needs `OPENAI_API_KEY` and is only compiled
//! here; every other example runs against the faux provider.

#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/16-real-model.rs"]
mod ex16_real_model;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/17-coding-tools.rs"]
mod ex17_coding_tools;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/18-print.rs"]
mod ex18_print;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/19-json.rs"]
mod ex19_json;
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

use serde_json::Value;

fn args(values: &[&str]) -> Vec<String> {
    values.iter().map(|value| (*value).to_owned()).collect()
}

fn text(out: Vec<u8>) -> String {
    String::from_utf8(out).expect("examples print UTF-8")
}

#[tokio::test]
async fn ex17_coding_tools_reads_edits_and_runs_commands() {
    let mut out = Vec::new();
    ex17_coding_tools::run(&mut out, &[], None).await.unwrap();
    let out = text(out);
    let lines: Vec<&str> = out.lines().collect();
    assert!(
        lines[0].starts_with("cat /tmp/1gb.txt took ") && lines[0].ends_with(" ms"),
        "{out}"
    );
    let storage = lines
        .last()
        .and_then(|line| line.strip_prefix("storage: "))
        .expect("storage line");
    assert!(storage.contains("pi-durable-example-"), "{out}");
    let expected = [
        "status: done",
        "pi.user",
        "pi.system",
        "pi.assistant",
        r#"pi.tool-result read: "hello world\n""#,
        "pi.assistant",
        r#"pi.tool-result edit: "Successfully replaced 1 block(s) in notes.txt.""#,
        "pi.assistant",
        r#"pi.tool-result bash: "hello durable\n""#,
        "pi.assistant",
        r#"pi.tool-result bash: "cat: /tmp/1gb.txt: No such file or directory\n<harness>\n[error] Command exited with code 1\n</harness>""#,
        "pi.assistant",
        r#"answer: [{"type":"text","text":"The file now greets durable."}]"#,
        r#"file: "hello durable\n""#,
    ];
    let middle = &lines[1..lines.len() - 1];
    assert_eq!(middle.len(), expected.len(), "{out}");
    // With /tmp/1gb.txt present, the big `cat` result holds its (clipped) content instead.
    let big_cat_exists = std::path::Path::new("/tmp/1gb.txt").exists();
    for (index, (line, expected)) in middle.iter().zip(expected).enumerate() {
        if index == 10 && big_cat_exists {
            assert!(line.starts_with("pi.tool-result bash: "), "{out}");
        } else {
            assert_eq!(*line, expected, "{out}");
        }
    }
    std::fs::remove_dir_all(storage).unwrap();
}

#[tokio::test]
async fn ex18_print_prints_the_answer() {
    let mut out = Vec::new();
    ex18_print::run(&mut out, &[], None).await.unwrap();
    assert_eq!(
        text(out),
        "This directory holds the durable package sources, tests, and docs.\n"
    );
    let mut out = Vec::new();
    ex18_print::run(&mut out, &args(&["hi"]), None)
        .await
        .unwrap();
    assert_eq!(
        text(out),
        "This directory holds the durable package sources, tests, and docs.\n"
    );
}

fn json_lines(out: &str) -> Vec<Value> {
    out.lines()
        .map(|line| serde_json::from_str(line).expect("one JSON value per line"))
        .collect()
}

#[tokio::test]
async fn ex19_json_streams_events() {
    let mut out = Vec::new();
    ex19_json::run(&mut out, &args(&["--storage", "memory", "--events"]), None)
        .await
        .unwrap();
    let events = json_lines(&text(out));
    let types: Vec<&str> = events
        .iter()
        .map(|event| event["type"].as_str().unwrap())
        .collect();
    assert_eq!(
        types,
        [
            "snapshot",
            "message_start",
            "message_end",
            "submission",
            "run_start",
            "turn_start",
            "message_start",
            "message_end",
            "message_start",
            "message_end",
            "usage_changed",
            "tool_execution_start",
            "tool_execution_update",
            "tool_execution_end",
            "message_start",
            "message_end",
            "turn_end",
            "turn_start",
            "message_start",
            "message_end",
            "turn_end",
            "run_end",
            "submission",
            "usage_changed",
        ]
    );
    assert_eq!(
        events[0],
        serde_json::json!({
            "type": "snapshot",
            "entries": [],
            "tools": [],
            "compactions": [],
            "inbox": [],
            "agent": { "model": { "provider": "faux", "modelId": "faux-1" } },
            "usage": { "models": {}, "tools": {} }
        })
    );
    assert_eq!(
        events[1]["message"]["content"],
        "What is in this directory?"
    );
    assert_eq!(
        events[11],
        serde_json::json!({
            "type": "tool_execution_start",
            "toolCallId": "call-1",
            "toolName": "bash",
            "args": { "command": "ls" }
        })
    );
    assert_eq!(
        events[19]["entry"]["model"][0]["content"][0]["text"],
        "This directory holds the durable package sources, tests, and docs."
    );
    assert_eq!(
        events[22]["record"],
        serde_json::json!({
            "conversationId": 1, "type": "input", "status": "done", "entry": 7, "id": 8, "answer": 15
        })
    );
}

#[tokio::test]
async fn ex19_json_streams_ops_and_takes_the_prompt_argument() {
    let mut out = Vec::new();
    ex19_json::run(
        &mut out,
        &args(&["--ops", "--storage", "memory", "hi"]),
        None,
    )
    .await
    .unwrap();
    let frames = json_lines(&text(out));
    assert_eq!(frames.len(), 11);
    assert_eq!(
        frames[0]["view"]["docs"]["pi.agent"],
        serde_json::json!({ "model": { "provider": "faux", "modelId": "faux-1" } })
    );
    assert_eq!(frames[0]["view"]["entries"], serde_json::json!([]));
    assert!(frames[1..].iter().all(|frame| frame["ops"].is_array()));
    assert_eq!(
        frames[1]["ops"][0],
        serde_json::json!(["s", ["docs", "pi.live", "run"], { "taskId": 9, "inputs": [8] }])
    );
    assert_eq!(frames[1]["ops"][1][4][0]["model"][0]["content"], "hi");
    assert_eq!(
        frames[8]["ops"],
        serde_json::json!([
            ["d", ["docs", "pi.live", "tools"]],
            ["s", ["docs", "pi.live", "run", "taskId"], 14]
        ])
    );
}

#[tokio::test]
async fn ex19_json_rejects_an_unknown_storage() {
    let mut out = Vec::new();
    let error = ex19_json::run(&mut out, &args(&["--storage", "bogus"]), None)
        .await
        .unwrap_err();
    assert_eq!(
        error.to_string(),
        "Unknown --storage bogus; use sqlite, jsonl, or memory"
    );
    assert!(out.is_empty());
}

#[tokio::test]
async fn ex20_inbox_queues_steers_writes_and_rejects_while_busy() {
    let mut out = Vec::new();
    ex20_inbox::run(&mut out, &[], None).await.unwrap();
    assert_eq!(
        text(out),
        r#"rejected: Conversation 1 is busy
withdraw: aborted
inbox: ["10 followUp","11 steer","12 write"]
first: done 
follow-up: done 
steer: done 
note: done 
withdrawn: unanswered aborted
transcript: ["pi.user","pi.assistant","app.note","pi.user","pi.user","pi.assistant"]
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
