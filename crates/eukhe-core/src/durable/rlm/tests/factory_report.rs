//! `factory.report`: a factory run's end reaches the agent that started
//! it as a settled-work input that starts its turn, once per milestone.

use eukhe_durable::types::EntryRecord;
use eukhe_types::pi_ai::{AssistantContentBlock, Message, UserContent, UserContentBlock};
use serde_json::json;

use super::{cx, entries, text, wait_for, Fixture};
use crate::durable::HostCall;

/// The texts of the conversation's user and assistant messages, in order.
fn transcript(all: &[EntryRecord]) -> Vec<String> {
    all.iter()
        .filter_map(|entry| entry.model.as_ref())
        .flatten()
        .filter_map(|message| match message {
            Message::User(user) => Some(match &user.content {
                UserContent::Text(text) => text.clone(),
                UserContent::Blocks(blocks) => blocks
                    .iter()
                    .filter_map(|block| match block {
                        UserContentBlock::Text(text) => Some(text.text.as_str()),
                        UserContentBlock::Image(_) => None,
                    })
                    .collect(),
            }),
            Message::Assistant(assistant) => Some(
                assistant
                    .content
                    .iter()
                    .filter_map(|block| match block {
                        AssistantContentBlock::Text(text) => Some(text.text.as_str()),
                        AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => {
                            None
                        }
                    })
                    .collect(),
            ),
            Message::System(_) | Message::ToolResult(_) => None,
        })
        .collect()
}

/// A run's control loop reports after the cell that started it ended: the
/// report goes to the main conversation and wakes the idle agent; the same
/// milestone reported again is admitted once.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_run_report_wakes_the_idle_agent_once() {
    let fixture = Fixture::new();
    fixture.faux.set_responses(vec![text("continuing")]);
    let session = fixture.open().await;
    let report = session
        .deps()
        .host_requests
        .get("factory.report")
        .expect("the factory.report handler");
    let body = "factory run r1 (builder): stopped: run budget_ms 10 reached after 12ms\ndone: scope\ncancelled: notes";
    for _ in 0..2 {
        let admitted = report(HostCall {
            data: json!({
                "run_id": "r1",
                "seq": 7,
                "state": "stopped",
                "kind": "budget_exceeded",
                "report": body,
            }),
            cell_source_code: None,
            call: None,
            signal: None,
        })
        .await
        .expect("the report is admitted");
        assert_eq!(admitted, json!({ "admitted": true }));
    }
    wait_for("the report's turn", || {
        let session = &session;
        async move { transcript(&entries(session).await).len() >= 2 }
    })
    .await;
    session
        .root()
        .wait_for_idle(cx())
        .await
        .expect("the conversation goes idle");
    assert_eq!(
        transcript(&entries(&session).await),
        vec![
            format!("[job-settled job:factory-r1 status:aborted]\n\nResume your work using the result below.\n\n{body}"),
            "continuing".to_owned(),
        ]
    );
    session.close(cx()).await.expect("close");
}
