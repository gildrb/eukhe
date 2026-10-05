//! Building one node with the model (`OptChat` spec §4.2-4.3): the
//! COMPACT system prompt, the context block (the bare view lines up to the
//! node, cut into cache-marked pieces like the agent's view), then the
//! step; an over-long line gets the cut-at-limit feedback in the SAME
//! conversation, and the shortest of at most [`TRIES`] lines wins.

use std::future::Future;
use std::pin::Pin;

use eukhe_types::ai::{
    AssistantContentBlock, AssistantMessage, CacheBreakpoint, Context, Message, StopReason,
    TextContent, UserContent, UserContentBlock, UserMessage,
};

use super::prompts::{over_limit_feedback, COMPACT};
use super::{view, NODE, TRIES};

/// The future one summarizer call returns.
pub type SummarizerFuture =
    Pin<Box<dyn Future<Output = anyhow::Result<AssistantMessage>> + Send + 'static>>;

/// The model behind the compactor.
///
/// An implementation completes one conversation (system prompt plus
/// messages, no tools) on a cheap but competent model and returns the
/// model's message verbatim: the compactor replays it in the same
/// conversation when the line is over the size limit. Transport failures
/// return `Err`; a reply that stopped with an error is reported through its
/// `stop_reason`. Either fails the node, which the owner retries after
/// [`super::RETRY`].
pub trait Summarizer: Send + Sync {
    /// Complete `context` and return the model's message.
    fn complete(&self, context: Context) -> SummarizerFuture;
}

/// The inputs of one model-built node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct NodeRequest {
    /// The bare view lines up to the node, wrapped in `<chat>`.
    pub context: String,
    /// The step: SCALE, the instruction, and the input whole.
    pub step: String,
}

/// Build one line: ask, check the size, give the cut-at-limit feedback,
/// and keep the shortest try.
///
/// # Errors
///
/// Returns an error when the summarizer fails, a reply stops with an error,
/// or a reply is empty after trimming.
pub(crate) async fn build_line(
    summarizer: &dyn Summarizer,
    request: &NodeRequest,
    timestamp: u64,
) -> anyhow::Result<String> {
    let mut blocks: Vec<UserContentBlock> = Vec::new();
    let pieces = view::pieces(&request.context);
    let marked = pieces.len() - 1;
    for (at, piece) in pieces.into_iter().enumerate() {
        blocks.push(text_block(
            piece,
            (at < marked).then_some(CacheBreakpoint::Ephemeral),
        ));
    }
    blocks.push(text_block(request.step.clone(), None));
    let mut context = Context {
        system_prompt: Some(COMPACT.to_string()),
        messages: vec![Message::User(UserMessage {
            content: UserContent::Blocks(blocks),
            timestamp,
            rest: serde_json::Map::default(),
        })],
        tools: None,
    };
    let mut tries: Vec<String> = Vec::new();
    loop {
        let reply = summarizer.complete(context.clone()).await?;
        if matches!(reply.stop_reason, StopReason::Error | StopReason::Aborted) {
            anyhow::bail!(
                "the compactor model stopped with {:?}: {}",
                reply.stop_reason,
                reply.error_message.as_deref().unwrap_or("no error message")
            );
        }
        let line = reply_text(&reply).trim().to_string();
        if line.is_empty() {
            anyhow::bail!("the compactor model returned an empty line");
        }
        let fits = line.len() <= NODE;
        let feedback = over_limit_feedback(&line);
        tries.push(line);
        if fits || tries.len() >= TRIES {
            break;
        }
        context.messages.push(Message::Assistant(reply));
        context.messages.push(Message::User(UserMessage {
            content: UserContent::Blocks(vec![text_block(feedback, None)]),
            timestamp,
            rest: serde_json::Map::default(),
        }));
    }
    // The shortest try wins; the first among equals.
    let mut best = tries.swap_remove(0);
    for line in tries {
        if line.len() < best.len() {
            best = line;
        }
    }
    Ok(best)
}

fn text_block(text: String, cache_breakpoint: Option<CacheBreakpoint>) -> UserContentBlock {
    UserContentBlock::Text(TextContent {
        text,
        text_signature: None,
        cache_breakpoint,
        rest: serde_json::Map::default(),
    })
}

/// The reply's text blocks, concatenated (thinking is never part of a line).
fn reply_text(reply: &AssistantMessage) -> String {
    reply
        .content
        .iter()
        .filter_map(|block| match block {
            AssistantContentBlock::Text(text) => Some(text.text.as_str()),
            AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => None,
        })
        .collect()
}

#[cfg(test)]
pub(crate) mod tests {
    use std::collections::VecDeque;
    use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

    use eukhe_types::ai::Usage;

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
        fn complete(&self, context: Context) -> SummarizerFuture {
            locked(&self.requests).push(context);
            locked(&self.times).push(tokio::time::Instant::now());
            self.asked.notify_waiters();
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
        AssistantMessage {
            content: vec![AssistantContentBlock::Text(TextContent {
                text: text.to_string(),
                text_signature: None,
                cache_breakpoint: None,
                rest: serde_json::Map::default(),
            })],
            api: "faux".to_string(),
            provider: "faux".to_string(),
            model: "faux".to_string(),
            response_model: None,
            response_id: None,
            diagnostics: None,
            usage: Usage::default(),
            stop_reason: StopReason::Stop,
            stop_reason_raw: None,
            error_message: None,
            timestamp: 0,
            rest: serde_json::Map::default(),
        }
    }

    const CONTEXT: &str = "<chat>\nuser: hi\n</chat>";
    const STEP: &str = "Compress this message";

    fn request() -> NodeRequest {
        NodeRequest {
            context: CONTEXT.to_string(),
            step: STEP.to_string(),
        }
    }

    fn user(blocks: Vec<UserContentBlock>) -> Message {
        Message::User(UserMessage {
            content: UserContent::Blocks(blocks),
            timestamp: 7,
            rest: serde_json::Map::default(),
        })
    }

    /// The first request: COMPACT, then ONE user message with the context
    /// and the step as two text blocks, no tools.
    fn first_request() -> Context {
        Context {
            system_prompt: Some(COMPACT.to_string()),
            messages: vec![user(vec![
                text_block(CONTEXT.to_string(), None),
                text_block(STEP.to_string(), None),
            ])],
            tools: None,
        }
    }

    #[tokio::test]
    async fn a_line_within_the_limit_is_taken_at_once() {
        let summarizer = Scripted::with(vec![Ok(reply("  user: hi  "))]);
        let line = build_line(summarizer.as_ref(), &request(), 7)
            .await
            .unwrap();
        assert_eq!(
            (line, summarizer.requests()),
            ("user: hi".to_string(), vec![first_request()])
        );
    }

    /// An over-long line gets the cut-at-limit feedback in the SAME
    /// conversation; after [`TRIES`] lines the shortest wins.
    #[tokio::test]
    async fn over_long_lines_get_feedback_and_the_shortest_wins() {
        let long = |n: usize| "x".repeat(n);
        let summarizer = Scripted::with(vec![
            Ok(reply(&long(530))),
            Ok(reply(&long(520))),
            Ok(reply(&long(525))),
            Ok(reply(&long(519))),
            Ok(reply(&long(521))),
        ]);
        let line = build_line(summarizer.as_ref(), &request(), 7)
            .await
            .unwrap();
        assert_eq!(line, long(519));
        let requests = summarizer.requests();
        assert_eq!(requests.len(), TRIES);
        let mut second = first_request();
        second.messages.extend([
            Message::Assistant(reply(&long(530))),
            user(vec![text_block(
                format!(
                    "That line is 530 bytes; the limit is 512. It must end where it is cut here:\n{}| \u{2190} LIMIT",
                    long(512)
                ),
                None,
            )]),
        ]);
        assert_eq!(requests[1], second);
        // The last request replays every earlier reply and its feedback.
        assert_eq!(requests[TRIES - 1].messages.len(), 2 * TRIES - 1);
    }

    /// A line within [`NODE`] ends the retries.
    #[tokio::test]
    async fn a_line_at_the_limit_ends_the_retries() {
        let summarizer = Scripted::with(vec![
            Ok(reply(&"x".repeat(NODE + 1))),
            Ok(reply(&"y".repeat(NODE))),
        ]);
        let line = build_line(summarizer.as_ref(), &request(), 7)
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
            assert!(build_line(summarizer.as_ref(), &request(), 7)
                .await
                .is_err());
        }
    }

    /// The context is cut like the agent's view: at the last line end
    /// before each mark inside it, every piece but the last cache-marked.
    #[tokio::test]
    async fn long_contexts_are_cut_into_marked_pieces() {
        let line = format!("{}\n", "a".repeat(999));
        let context = format!("<chat>\n{}</chat>", line.repeat(60));
        let summarizer = Scripted::with(vec![Ok(reply("done"))]);
        build_line(
            summarizer.as_ref(),
            &NodeRequest {
                context: context.clone(),
                step: "step".to_string(),
            },
            7,
        )
        .await
        .unwrap();
        // The 50,000 mark falls in line 50; the later marks lie past the end.
        let cut = "<chat>\n".len() + 49 * line.len();
        assert_eq!(
            summarizer.requests()[0].messages,
            vec![user(vec![
                text_block(context[..cut].to_string(), Some(CacheBreakpoint::Ephemeral)),
                text_block(context[cut..].to_string(), None),
                text_block("step".to_string(), None),
            ])]
        );
    }
}
