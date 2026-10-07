//! Examples owned by this module; see `main.rs`.

#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/08-harness-conversations.rs"]
mod ex08_harness_conversations;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/09-context.rs"]
mod ex09_context;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/10-registry-reload.rs"]
mod ex10_registry_reload;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/11-extension-state.rs"]
mod ex11_extension_state;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/12-tasks.rs"]
mod ex12_tasks;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/13-recovery.rs"]
mod ex13_recovery;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/14-chat.rs"]
mod ex14_chat;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/15-system-prompt.rs"]
mod ex15_system_prompt;

/// The printed lines of an example's output.
fn lines(out: &[u8]) -> Vec<&str> {
    std::str::from_utf8(out)
        .expect("UTF-8 output")
        .lines()
        .collect()
}

#[tokio::test]
async fn harness_conversations() {
    let mut out = Vec::new();
    ex08_harness_conversations::run(&mut out, &[], None)
        .await
        .unwrap();
    assert_eq!(
        lines(&out),
        [
            "typed entry: true example",
            "helper thinking: minimal",
            "fork thinking: high",
            "lookup: true",
        ]
    );
}

#[tokio::test]
async fn context() {
    let mut out = Vec::new();
    ex09_context::run(&mut out, &[], None).await.unwrap();
    assert_eq!(
        lines(&out),
        [
            r#"raw active entries: ["message","message","message","message","pi.system","message","message","edit","note"]"#,
            r#"request messages: ["user: read files a and b","assistant: reading call(a) call(b)","result(a)","result(b)","system: {\"cwd\":\"<cwd>/repo</cwd>\"}","assistant: a and b look fine"]"#,
            r#"fork messages: ["user: read a and b","assistant: reading call(a) call(b)","result(a) error","result(b) error"]"#,
            r#"after summary: summary ["user: Summary: a and b are fine."]"#,
            r#"newest stored entries: ["summary","note","edit"] more: true"#,
        ]
    );
}

#[tokio::test]
async fn registry_reload() {
    let mut out = Vec::new();
    ex10_registry_reload::run(&mut out, &[], None)
        .await
        .unwrap();
    assert_eq!(
        lines(&out),
        [
            r#"after reload: ["read: Read a file","grep: Search files, faster"]"#,
            r#"with audit: ["read: Read a file (audited)","grep: Search files, faster"]"#,
            r#"after uninstall: ["read: Read a file","grep: Search files, faster"]"#,
        ]
    );
}

#[tokio::test]
async fn extension_state() {
    let mut out = Vec::new();
    ex11_extension_state::run(&mut out, &[], None)
        .await
        .unwrap();
    assert_eq!(
        lines(&out),
        [
            r#"todos: {"items":["fix the build"]}"#,
            r#"system messages: [{"toolsAdded":["todo"]},{"sections":{"todos":"<todos>\nfix the build\n</todos>"}}]"#,
        ]
    );
}

#[tokio::test]
async fn tasks() {
    let mut out = Vec::new();
    ex12_tasks::run(&mut out, &[], None).await.unwrap();
    assert_eq!(
        lines(&out),
        [r#"payment outcome: {"status":"completed","result":{"receipt":500}}"#]
    );
}

#[tokio::test]
async fn recovery() {
    let mut out = Vec::new();
    ex13_recovery::run(&mut out, &[], None).await.unwrap();
    assert_eq!(
        lines(&out),
        [
            "tick 1",
            "tick 2",
            r#"closed; saved checkpoint: {"status":"pending","checkpoint":{"phase":"tick","n":2}} memos: {"printed-1":true,"printed-2":true}"#,
            "tick 3",
            "tick 4",
            "tick 5",
            r#"after reopen: {"status":"completed","result":"counted to 5"}"#,
        ]
    );
}

#[tokio::test]
async fn chat() {
    let mut out = Vec::new();
    ex14_chat::run(&mut out, &[], None).await.unwrap();
    assert_eq!(
        lines(&out),
        [
            r#"answer: [{"type":"text","text":"Paris."}]"#,
            r#"transcript: ["pi.user","pi.system","pi.assistant"]"#,
        ]
    );
}

/// The JSON after `label` with every message's wall-clock `timestamp`
/// removed, and those timestamps.
fn system_messages(line: &str, label: &str) -> (serde_json::Value, Vec<u64>) {
    let json = line
        .strip_prefix(label)
        .unwrap_or_else(|| panic!("{line:?} starts with {label:?}"));
    let mut value: serde_json::Value = serde_json::from_str(json).expect("JSON messages");
    let timestamps = value
        .as_array_mut()
        .expect("a message array")
        .iter_mut()
        .map(|message| {
            message
                .as_object_mut()
                .and_then(|message| message.remove("timestamp"))
                .and_then(|timestamp| timestamp.as_u64())
                .expect("a numeric timestamp")
        })
        .collect();
    (value, timestamps)
}

#[tokio::test]
async fn system_prompt() {
    let mut out = Vec::new();
    ex15_system_prompt::run(&mut out, &[], None).await.unwrap();
    let printed = lines(&out);
    assert_eq!(printed.len(), 3);
    let root_prompt = serde_json::json!({
        "role": "system",
        "content": "",
        "sections": {
            "preamble": "You are a coding agent. Be terse.",
            "cwd": "<cwd>\n/repo\n</cwd>",
            "agents_md": "<agents_md>\nRun npm run check after changes.\n</agents_md>",
        },
    });
    let (root, root_at) = system_messages(printed[0], "root system prompt: ");
    assert_eq!(root, serde_json::json!([root_prompt]));
    let (subagent, _) = system_messages(printed[1], "subagent system prompt: ");
    assert_eq!(
        subagent,
        serde_json::json!([{
            "role": "system",
            "content": "",
            "sections": {
                "preamble": "You are a coding agent. Be terse.",
                "cwd": "<cwd>\n/repo\n</cwd>",
                "instructions": "<instructions>\nOnly read; never edit files.\n</instructions>",
            },
        }])
    );
    let (after, after_at) = system_messages(printed[2], "root system entries after cwd change: ");
    assert_eq!(
        after,
        serde_json::json!([
            root_prompt,
            {
                "role": "system",
                "content": "",
                "sections": { "cwd": "<cwd>\n/repo/packages\n</cwd>" },
            },
        ])
    );
    // The first entry is the same stored message; the change came later.
    assert_eq!(after_at[0], root_at[0]);
    assert!(after_at[1] >= after_at[0]);
}
