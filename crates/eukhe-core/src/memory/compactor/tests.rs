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

/// A reply with thinking only: no text.
pub(crate) fn thinking_only() -> AssistantMessage {
    let mut message = reply("");
    message.content = vec![AssistantContentBlock::Thinking(
        serde_json::from_value(serde_json::json!({"type": "thinking", "thinking": "count"}))
            .expect("a thinking block"),
    )];
    message
}

const CONTEXT: &str = "<chat>\n0+1|user: hi\n</chat>";
const TASK: &str = "Compaction: compress message 1";

/// A message input over [`NODE`] bytes, a 2-byte character across the
/// cut.
fn input() -> String {
    format!("user: {}é{}", "a".repeat(NODE - 7), "b".repeat(40))
}

fn request() -> NodeRequest {
    NodeRequest {
        context: CONTEXT.to_string(),
        task: TASK.to_string(),
        input: input(),
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

/// `build_line` on `summarizer` with the test's prompt and request.
async fn line_of(summarizer: &dyn Summarizer) -> anyhow::Result<String> {
    build_line(
        summarizer,
        &prompt(),
        &request(),
        7,
        ResponseStarted::default(),
    )
    .await
}

#[tokio::test]
async fn a_line_within_the_limit_is_taken_at_once() {
    let summarizer = Scripted::with(vec![Ok(reply("  user: hi  "))]);
    let line = line_of(summarizer.as_ref()).await.unwrap();
    assert_eq!(
        (line, summarizer.requests()),
        ("user: hi".to_string(), vec![first_request()])
    );
}

/// An over-long line gets the cut follow-up in the SAME conversation (the
/// end mark moves to it) while the lines get shorter; after [`TRIES`]
/// lines the shortest, cut to [`NODE`] bytes, wins.
#[tokio::test]
async fn over_long_lines_get_the_cut_and_the_shortest_cut_wins() {
    let long = |n: usize| "x".repeat(n);
    let summarizer = Scripted::with(vec![
        Ok(reply(&long(530))),
        Ok(reply(&long(520))),
        Ok(reply(&long(519))),
        Ok(reply(&long(518))),
        Ok(reply(&long(517))),
        Ok(reply(&long(100))),
    ]);
    let line = line_of(summarizer.as_ref()).await.unwrap();
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
        (long(NODE), TRIES, second)
    );
}

/// A follow-up not shorter than the best line ends the tries: the model
/// gets no closer (H1.2). The best line, cut, wins.
#[tokio::test]
async fn a_follow_up_not_shorter_ends_the_tries() {
    let summarizer = Scripted::with(vec![
        Ok(reply(&"x".repeat(1300))),
        Ok(reply(&"y".repeat(1290))),
        Ok(reply(&"z".repeat(1290))),
        Ok(reply("fits")),
    ]);
    let line = line_of(summarizer.as_ref()).await.unwrap();
    assert_eq!((line, summarizer.requests().len()), ("y".repeat(NODE), 3));
}

/// A line within [`NODE`] ends the retries.
#[tokio::test]
async fn a_line_at_the_limit_ends_the_retries() {
    let summarizer = Scripted::with(vec![
        Ok(reply(&"x".repeat(NODE + 1))),
        Ok(reply(&"y".repeat(NODE))),
    ]);
    let line = line_of(summarizer.as_ref()).await.unwrap();
    assert_eq!((line, summarizer.requests().len()), ("y".repeat(NODE), 2));
}

/// A failed reply fails the call; an empty or thinking-only reply is a
/// try that ends the call with the input, cut to [`NODE`] bytes (H1.4).
#[tokio::test]
async fn failed_replies_fail_and_empty_ones_give_the_input_cut() {
    let mut failed = reply("partial");
    failed.stop_reason = StopReason::Error;
    let mut outcomes = Vec::new();
    for scripted in [
        Ok(reply("   ")),
        Ok(thinking_only()),
        Ok(failed),
        Err(anyhow::anyhow!("overloaded")),
    ] {
        let summarizer = Scripted::with(vec![scripted, Ok(reply("never asked"))]);
        let line = line_of(summarizer.as_ref())
            .await
            .map_err(|error| format!("{error:#}"));
        outcomes.push((line, summarizer.requests().len()));
    }
    let cut = format!("user: {}", "a".repeat(NODE - 7));
    assert_eq!(
        outcomes,
        [
            (Ok(cut.clone()), 1),
            (Ok(cut), 1),
            (
                Err("the compactor model stopped with Error: no error message".to_string()),
                1
            ),
            (Err("overloaded".to_string()), 1),
        ]
    );
}

/// A compactor that never answers.
pub(crate) struct Silent;

impl Summarizer for Silent {
    fn complete(&self, _context: Context, _started: ResponseStarted) -> SummarizerFuture {
        Box::pin(std::future::pending())
    }
}

/// A model call that does not answer within [`CALL_DEADLINE`] fails the
/// call (H1.5): a call never waits forever.
#[tokio::test(start_paused = true)]
async fn a_model_call_past_its_deadline_fails() {
    let asked = tokio::time::Instant::now();
    let error = line_of(&Silent).await.unwrap_err();
    assert_eq!(
        (format!("{error:#}"), asked.elapsed()),
        (
            "the compactor model did not answer within 600 s".to_string(),
            CALL_DEADLINE
        )
    );
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
            input: input(),
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
