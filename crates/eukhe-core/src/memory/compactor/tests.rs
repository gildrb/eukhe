use std::collections::VecDeque;
use std::fmt::Write as _;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use eukhe_types::pi_ai::{Tool, Usage};

use super::*;

/// A scripted summarizer: replies in order and records every request
/// with the (tokio) time it came.
#[derive(Default)]
pub(crate) struct Scripted {
    replies: Mutex<VecDeque<anyhow::Result<AssistantMessage>>>,
    requests: Mutex<Vec<Context>>,
    times: Mutex<Vec<tokio::time::Instant>>,
    asked: tokio::sync::Notify,
}

impl Scripted {
    pub(crate) fn with(replies: Vec<anyhow::Result<AssistantMessage>>) -> Arc<Scripted> {
        Arc::new(Scripted {
            replies: Mutex::new(replies.into()),
            ..Scripted::default()
        })
    }

    /// Every request so far, in order.
    pub(crate) fn requests(&self) -> Vec<Context> {
        locked(&self.requests).clone()
    }

    /// When each request came.
    pub(crate) fn times(&self) -> Vec<tokio::time::Instant> {
        locked(&self.times).clone()
    }

    /// Wait until `count` requests have come; returns them.
    pub(crate) async fn requested(&self, count: usize) -> Vec<Context> {
        loop {
            let asked = self.asked.notified();
            let requests = self.requests();
            if requests.len() >= count {
                return requests;
            }
            asked.await;
        }
    }
}

impl Summarizer for Scripted {
    /// A whole-reply model: its response starts when it is asked.
    fn complete(&self, context: Context, mut started: ResponseStarted) -> SummarizerFuture {
        locked(&self.requests).push(context);
        locked(&self.times).push(tokio::time::Instant::now());
        self.asked.notify_waiters();
        started.signal();
        let reply = locked(&self.replies)
            .pop_front()
            .unwrap_or_else(|| Err(anyhow::anyhow!("no scripted reply left")));
        Box::pin(async move { reply })
    }
}

fn locked<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

pub(crate) fn reply(text: &str) -> AssistantMessage {
    serde_json::from_value(serde_json::json!({
        "role": "assistant",
        "content": [{"type": "text", "text": text}],
        "api": "faux",
        "provider": "faux",
        "model": "faux",
        "usage": Usage::default(),
        "stopReason": "stop",
        "timestamp": 0,
    }))
    .expect("a faux reply")
}

const CONTEXT: &str = "<chat>\n0+1|user: hi\n</chat>";
const TASK: &str = "Compaction: compress message 1";

fn request() -> NodeRequest {
    NodeRequest {
        context: CONTEXT.to_string(),
        task: TASK.to_string(),
    }
}

fn prompt() -> CompactionPrompt {
    CompactionPrompt {
        system: "You are Eukhe. User instructions follow.".to_string(),
        tools: vec![serde_json::from_value::<Tool>(serde_json::json!({
            "name": "zoom",
            "description": "Open a line.",
            "parameters": {"type": "object", "properties": {}}
        }))
        .expect("a tool")],
    }
}

fn user(blocks: Vec<UserContentBlock>) -> Message {
    Message::User(UserMessage {
        content: UserContent::Blocks(blocks),
        timestamp: 7,
    })
}

/// The first request: the turns' system prompt and tools, then ONE user
/// message with the view and the task, the task marked as the request's
/// end (a view shorter than one block carries no mark of its own).
fn first_request() -> Context {
    Context {
        system_prompt: Some(prompt().system),
        messages: vec![user(vec![
            text_block(CONTEXT.to_string(), None),
            text_block(TASK.to_string(), Some(CacheBreakpoint::Ephemeral)),
        ])],
        tools: Some(prompt().tools),
    }
}

#[tokio::test]
async fn a_line_within_the_limit_is_taken_at_once() {
    let summarizer = Scripted::with(vec![Ok(reply("  user: hi  "))]);
    let line = build_line(
        summarizer.as_ref(),
        &prompt(),
        &request(),
        7,
        ResponseStarted::default(),
    )
    .await
    .unwrap();
    assert_eq!(
        (line, summarizer.requests()),
        ("user: hi".to_string(), vec![first_request()])
    );
}

/// An over-long line gets the cut follow-up in the SAME conversation (the
/// end mark moves to it); after [`TRIES`] lines the shortest wins.
#[tokio::test]
async fn over_long_lines_get_the_cut_and_the_shortest_of_five_wins() {
    let long = |n: usize| "x".repeat(n);
    let summarizer = Scripted::with(vec![
        Ok(reply(&long(530))),
        Ok(reply(&long(520))),
        Ok(reply(&long(525))),
        Ok(reply(&long(519))),
        Ok(reply(&long(521))),
        Ok(reply(&long(100))),
    ]);
    let line = build_line(
        summarizer.as_ref(),
        &prompt(),
        &request(),
        7,
        ResponseStarted::default(),
    )
    .await
    .unwrap();
    let requests = summarizer.requests();
    let follow_up = |n: usize| {
        user(vec![text_block(
            format!(
                "Too long: your line is {n} bytes, over the 512-byte limit. Write\nthe whole line again for the same <input>, cutting just enough of the\nleast valuable items to fit before this cut:\n{}| \u{2190} LIMIT",
                long(512)
            ),
            Some(CacheBreakpoint::Ephemeral),
        )])
    };
    let mut second = first_request();
    second.messages = vec![
        user(vec![
            text_block(CONTEXT.to_string(), None),
            text_block(TASK.to_string(), None),
        ]),
        Message::Assistant(reply(&long(530))),
        follow_up(530),
    ];
    assert_eq!(
        (line, requests.len(), requests[1].clone()),
        (long(519), TRIES, second)
    );
}

/// A line within [`NODE`] ends the retries.
#[tokio::test]
async fn a_line_at_the_limit_ends_the_retries() {
    let summarizer = Scripted::with(vec![
        Ok(reply(&"x".repeat(NODE + 1))),
        Ok(reply(&"y".repeat(NODE))),
    ]);
    let line = build_line(
        summarizer.as_ref(),
        &prompt(),
        &request(),
        7,
        ResponseStarted::default(),
    )
    .await
    .unwrap();
    assert_eq!((line, summarizer.requests().len()), ("y".repeat(NODE), 2));
}

#[tokio::test]
async fn empty_and_failed_replies_fail_the_node() {
    let mut failed = reply("partial");
    failed.stop_reason = StopReason::Error;
    for scripted in [
        Ok(reply("   ")),
        Ok(failed),
        Err(anyhow::anyhow!("overloaded")),
    ] {
        let summarizer = Scripted::with(vec![scripted]);
        assert!(build_line(
            summarizer.as_ref(),
            &prompt(),
            &request(),
            7,
            ResponseStarted::default()
        )
        .await
        .is_err());
    }
}

/// The view goes in blocks of four lines: the mark sits on the last whole
/// block, the rest follows unmarked, and the task ends the request marked.
#[tokio::test]
async fn the_view_is_marked_at_its_last_whole_block() {
    let mut context = String::from("<chat>\n");
    for at in 0..6 {
        let _ = writeln!(context, "{at}+1|l{at}");
    }
    context.push_str("</chat>");
    let summarizer = Scripted::with(vec![Ok(reply("done"))]);
    build_line(
        summarizer.as_ref(),
        &CompactionPrompt::memory_layer(),
        &NodeRequest {
            context,
            task: "task".to_string(),
        },
        7,
        ResponseStarted::default(),
    )
    .await
    .unwrap();
    assert_eq!(
        summarizer.requests(),
        vec![Context {
            system_prompt: Some(crate::memory::memory_system_layer()),
            messages: vec![user(vec![
                text_block(
                    "<chat>\n0+1|l0\n1+1|l1\n2+1|l2\n3+1|l3\n".to_string(),
                    Some(CacheBreakpoint::Ephemeral)
                ),
                text_block("4+1|l4\n5+1|l5\n</chat>".to_string(), None),
                text_block("task".to_string(), Some(CacheBreakpoint::Ephemeral)),
            ])],
            tools: None,
        }]
    );
}
