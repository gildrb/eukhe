//! Examples 00–07: Session basics and Harness configuration; see `main.rs`.
//!
//! Each test runs the example into a buffer and asserts the lines the TS
//! example prints, with objects as compact JSON instead of `util.inspect`.

#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/00-conversation.rs"]
mod ex00_conversation;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/01-documents.rs"]
mod ex01_documents;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/02-forks.rs"]
mod ex02_forks;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/03-owned-conversations.rs"]
mod ex03_owned_conversations;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/04-chord-state.rs"]
mod ex04_chord_state;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/05-watches.rs"]
mod ex05_watches;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/06-harness.rs"]
mod ex06_harness;
#[expect(dead_code, reason = "`main` only serves `cargo run --example`")]
#[path = "../../examples/07-configuration.rs"]
mod ex07_configuration;

/// The example's output lines.
fn lines(out: &[u8]) -> Vec<&str> {
    std::str::from_utf8(out)
        .expect("UTF-8 output")
        .lines()
        .collect()
}

#[tokio::test]
async fn conversation() {
    let mut out = Vec::new();
    ex00_conversation::run(&mut out, &[], None).await.unwrap();
    assert_eq!(lines(&out), [r#"standalone conversation: {"id":2}"#]);
}

#[tokio::test]
async fn documents() {
    let mut out = Vec::new();
    ex01_documents::run(&mut out, &[], None).await.unwrap();
    assert_eq!(
        lines(&out),
        [
            r#"latest notes: {"text":"after goodbye"}"#,
            r#"notes at first entry: {"text":"after hello"}"#,
            r#"notes at second entry: {"text":"after goodbye"}"#,
        ]
    );
}

#[tokio::test]
async fn forks() {
    let mut out = Vec::new();
    ex02_forks::run(&mut out, &[], None).await.unwrap();
    assert_eq!(
        lines(&out),
        [
            r#"fork transcript: ["hello"]"#,
            r#"fork notes: {"text":"after hello"}"#,
            r#"fork notes after edit: {"text":"changed only in the fork"}"#,
            r#"parent notes after edit: {"text":"after goodbye"}"#,
        ]
    );
}

#[tokio::test]
async fn owned_conversations() {
    let mut out = Vec::new();
    ex03_owned_conversations::run(&mut out, &[], None)
        .await
        .unwrap();
    assert_eq!(
        lines(&out),
        [
            "supervisor task: 3",
            r#"child conversation: {"id":4,"owner":{"conversationId":2,"taskId":3}}"#,
            r#"registry: {"agents":{"researcher":{"conversationId":4,"requestId":"researcher:first-message:3"}}}"#,
        ]
    );
}

#[tokio::test]
async fn chord_state() {
    let mut out = Vec::new();
    ex04_chord_state::run(&mut out, &[], None).await.unwrap();
    assert_eq!(
        lines(&out),
        [
            r#"Chord notes: hydrate 0 {"text":"first"}"#,
            r#"Chord notes: update 1 {"text":"published through Chord"}"#,
        ]
    );
}

#[tokio::test]
async fn watches() {
    let mut out = Vec::new();
    ex05_watches::run(&mut out, &[], None).await.unwrap();
    assert_eq!(
        lines(&out),
        [
            r#"watch baseline: {"text":"first"}"#,
            r#"watch update: {"text":"observed asynchronously"}"#,
        ]
    );
}

#[tokio::test]
async fn harness() {
    let mut out = Vec::new();
    ex06_harness::run(&mut out, &[], None).await.unwrap();
    assert_eq!(
        lines(&out),
        [
            r#"root: 1 {"text":"root notes"}"#,
            r#"stored agent: {"thinkingLevel":"low"}"#,
            r#"resolved: low ["files"] ["read"]"#,
        ]
    );
}

#[tokio::test]
async fn configuration() {
    let mut out = Vec::new();
    ex07_configuration::run(&mut out, &[], None).await.unwrap();
    assert_eq!(
        lines(&out),
        [
            r#"default tools: ["read","write","grep"]"#,
            r#"stored: {"model":{"provider":"anthropic","modelId":"claude-sonnet-4-5"},"thinkingLevel":"high","tools":["write","read"]}"#,
            r#"model: {"provider":"anthropic","modelId":"claude-sonnet-4-5"} thinking: high tools: ["write","read"]"#,
            r#"without search: ["read","write"]"#,
            r#"files uninstalled: ["grep"]"#,
            r#"files reinstalled: ["read","write","grep"]"#,
        ]
    );
}
