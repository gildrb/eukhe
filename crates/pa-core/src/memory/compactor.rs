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
