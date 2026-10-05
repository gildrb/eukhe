//! Building one node with the model (`OptChat` spec §4.2-4.3): the
//! COMPACT system prompt, the context block (the bare view lines up to the
//! node, cut into cache-marked pieces like the agent's view), then the
//! step; an over-long line gets the cut-at-limit feedback in the SAME
//! conversation, and the shortest of at most [`TRIES`] lines wins.

use std::future::Future;
use std::pin::Pin;

use pa_types::ai::{
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
    use std::sync::{Arc, Mutex};

    use pa_types::ai::{Api, Usage};

    use super::*;

    /// A scripted summarizer: replies in order and records every request.
    #[derive(Default)]
    pub(crate) struct Scripted {
        pub replies: Mutex<VecDeque<anyhow::Result<AssistantMessage>>>,
        pub requests: Mutex<Vec<Context>>,
    }

    impl Scripted {
        pub(crate) fn with(replies: Vec<anyhow::Result<AssistantMessage>>) -> Arc<Scripted> {
            Arc::new(Scripted {
                replies: Mutex::new(replies.into()),
                requests: Mutex::new(Vec::new()),
            })
        }
    }

    impl Summarizer for Scripted {
        fn complete(&self, context: Context) -> SummarizerFuture {
            self.requests.lock().unwrap().push(context);
            let reply = self
                .replies
                .lock()
                .unwrap()
                .pop_front()
                .unwrap_or_else(|| Err(anyhow::anyhow!("no scripted reply left")));
            Box::pin(async move { reply })
        }
    }

    pub(crate) fn reply(text: &str) -> AssistantMessage {
        AssistantMessage {
            content: vec![AssistantContentBlock::Text(TextContent {
                text: text.to_string(),
                text_signature: None,
                cache_breakpoint: None,
                rest: serde_json::Map::default(),
            })],
            api: Api::from("faux"),
            provider: "faux".into(),
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

    fn request() -> NodeRequest {
        NodeRequest {
            context: "<chat>\nuser: hi\n</chat>".to_string(),
            step: "Compress this message".to_string(),
        }
    }

    #[tokio::test]
    async fn a_line_within_the_limit_is_taken_at_once() {
        let summarizer = Scripted::with(vec![Ok(reply("  user: hi  "))]);
        let line = build_line(summarizer.as_ref(), &request(), 7)
            .await
            .unwrap();
        assert_eq!(line, "user: hi");
        let requests = summarizer.requests.lock().unwrap();
        assert_eq!(requests.len(), 1);
        assert_eq!(requests[0].system_prompt.as_deref(), Some(COMPACT));
    }

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
        assert_eq!(line.len(), 519);
        let requests = summarizer.requests.lock().unwrap();
        assert_eq!(requests.len(), TRIES);
        // The last request replays every earlier reply and its feedback.
        assert_eq!(requests[4].messages.len(), 9);
        let Message::User(feedback) = &requests[1].messages[2] else {
            panic!("feedback is a user message");
        };
        assert!(feedback
            .content
            .text()
            .starts_with("That line is 530 bytes; the limit is 512."));
    }

    #[tokio::test]
    async fn empty_and_failed_replies_fail_the_node() {
        let summarizer = Scripted::with(vec![Ok(reply("   "))]);
        assert!(build_line(summarizer.as_ref(), &request(), 7)
            .await
            .is_err());
        let mut failed = reply("partial");
        failed.stop_reason = StopReason::Error;
        let summarizer = Scripted::with(vec![Ok(failed)]);
        assert!(build_line(summarizer.as_ref(), &request(), 7)
            .await
            .is_err());
    }

    #[tokio::test]
    async fn long_contexts_are_cut_into_marked_pieces() {
        let context = format!(
            "<chat>\n{}</chat>",
            format!("{}\n", "a".repeat(999)).repeat(60)
        );
        let summarizer = Scripted::with(vec![Ok(reply("done"))]);
        build_line(
            summarizer.as_ref(),
            &NodeRequest {
                context,
                step: "step".to_string(),
            },
            7,
        )
        .await
        .unwrap();
        let requests = summarizer.requests.lock().unwrap();
        let Message::User(user) = &requests[0].messages[0] else {
            panic!("first message is the user message");
        };
        let UserContent::Blocks(blocks) = &user.content else {
            panic!("blocks");
        };
        let marks: Vec<Option<CacheBreakpoint>> = blocks
            .iter()
            .map(|block| match block {
                UserContentBlock::Text(text) => text.cache_breakpoint,
                UserContentBlock::Image(_) | UserContentBlock::Raw(_) => None,
            })
            .collect();
        assert_eq!(marks, vec![Some(CacheBreakpoint::Ephemeral), None, None]);
    }
}
