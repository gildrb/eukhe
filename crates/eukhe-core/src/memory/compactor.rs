//! Building one node with the model (spec §4): a call like a turn, with
//! the turns' system prompt and tools (declared, never called) so it reads
//! them from the turns' cache entry, then its own `<chat>` view and its
//! task. The view goes in blocks of [`super::BLOCK`] lines with one cache
//! mark on the last whole block and one on the request's end (§3.3). An
//! over-long line gets the cut follow-up in the SAME conversation, and the
//! shortest of at most [`TRIES`] lines wins.

use std::future::Future;
use std::pin::Pin;

use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, CacheBreakpoint, Context, Message, StopReason,
    TextContent, UserContent, UserContentBlock, UserMessage,
};

use super::prompts::cut_follow_up;
use super::saved::CompactionPrompt;
use super::{view, NODE, TRIES};

/// The future one summarizer call returns.
pub type SummarizerFuture =
    Pin<Box<dyn Future<Output = anyhow::Result<AssistantMessage>> + Send + 'static>>;

/// Tells the owner that a compactor call's response has started: from
/// then on its prefix is in the cache, so the calls waiting to read that
/// prefix may go (§3.3: a call whose marked prefix another call is writing
/// waits until that call's response starts). Signals at most once;
/// dropping it unsignalled (a failed call) leaves the waiters to the end
/// of the call.
#[derive(Debug, Default)]
pub struct ResponseStarted(Option<tokio::sync::oneshot::Sender<()>>);

impl ResponseStarted {
    /// A signal and the receiver that learns of it.
    pub(crate) fn channel() -> (ResponseStarted, tokio::sync::oneshot::Receiver<()>) {
        let (sender, receiver) = tokio::sync::oneshot::channel();
        (ResponseStarted(Some(sender)), receiver)
    }

    /// The response has started (its first event came, or the whole reply).
    pub fn signal(&mut self) {
        if let Some(sender) = self.0.take() {
            // The owner may have stopped waiting; nothing is owed then.
            let _ = sender.send(());
        }
    }
}

/// The model behind the compactor.
///
/// An implementation completes one conversation on a cheap but competent
/// model and returns the model's message verbatim: the compactor replays it
/// in the same conversation when the line is over the size limit. It
/// signals `started` as soon as the model's response starts (its first
/// streamed event; an implementation that only sees whole replies signals
/// when it has one). Transport failures return `Err`; a reply that stopped
/// with an error is reported through its `stop_reason`. Either fails the
/// node, which the owner tries again at the next message (or after
/// [`super::RETRY`] while a turn waits). Dropping the returned future
/// cancels the call: the implementation stops its request then (the owner
/// drops its calls when it stops).
pub trait Summarizer: Send + Sync {
    /// Complete `context` and return the model's message.
    fn complete(&self, context: Context, started: ResponseStarted) -> SummarizerFuture;
}

/// The inputs of one model-built node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct NodeRequest {
    /// The compaction view up to the node, `id+n|text` lines in `<chat>`.
    pub context: String,
    /// The task: the instruction, the ruler, and the input whole.
    pub task: String,
}

/// Build one line: ask, check the size, send the cut follow-up, and keep
/// the shortest try. `started` fires when the first call's response starts
/// (the follow-ups read the same prefix from the cache).
///
/// # Errors
///
/// Returns an error when the summarizer fails, a reply stops with an error,
/// or a reply is empty after trimming.
pub(crate) async fn build_line(
    summarizer: &dyn Summarizer,
    prompt: &CompactionPrompt,
    request: &NodeRequest,
    timestamp: u64,
    mut started: ResponseStarted,
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
    blocks.push(text_block(
        request.task.clone(),
        Some(CacheBreakpoint::Ephemeral),
    ));
    let mut context = Context {
        system_prompt: Some(prompt.system.clone()),
        messages: vec![Message::User(UserMessage {
            content: UserContent::Blocks(blocks),
            timestamp,
        })],
        tools: (!prompt.tools.is_empty()).then(|| prompt.tools.clone()),
    };
    let mut tries: Vec<String> = Vec::new();
    loop {
        let reply = summarizer
            .complete(context.clone(), std::mem::take(&mut started))
            .await?;
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
        let follow_up = cut_follow_up(&line);
        tries.push(line);
        if fits || tries.len() >= TRIES {
            break;
        }
        // The request's end moves to the follow-up: one end mark only.
        unmark_request_end(&mut context.messages);
        context.messages.push(Message::Assistant(reply));
        context.messages.push(Message::User(UserMessage {
            content: UserContent::Blocks(vec![text_block(
                follow_up,
                Some(CacheBreakpoint::Ephemeral),
            )]),
            timestamp,
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

/// Drop the cache mark of the last block of the last user message (the
/// previous request's end).
fn unmark_request_end(messages: &mut [Message]) {
    let last_user = messages.iter_mut().rev().find_map(|message| match message {
        Message::User(user) => Some(user),
        Message::System(_) | Message::Assistant(_) | Message::ToolResult(_) => None,
    });
    if let Some(UserMessage {
        content: UserContent::Blocks(blocks),
        ..
    }) = last_user
    {
        if let Some(UserContentBlock::Text(text)) = blocks.last_mut() {
            text.cache_breakpoint = None;
        }
    }
}

fn text_block(text: String, cache_breakpoint: Option<CacheBreakpoint>) -> UserContentBlock {
    UserContentBlock::Text(TextContent {
        text,
        text_signature: None,
        cache_breakpoint,
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
pub(crate) mod tests;
