//! Building one node with the model (spec §4): a call with the compactor's
//! own system prompt (its instructions and how to read the view; no tools),
//! then its `<chat>` view and its task. The view goes in blocks of
//! [`super::BLOCK`] lines with one cache mark on the last whole block and
//! one on the request's end (§3.3).
//!
//! A call always ends with a line of 1 to [`NODE`] bytes, whatever the
//! model replies (spec/README.md M2): the compiled Bend core decides the
//! end (`line.open`, `line.step` of `bend/compactor.bend`, through
//! `eukhe_bend::rules::compactor`) from the reply's length; this file
//! moves the texts. One model call ([`TRIES`]): a reply within [`NODE`]
//! bytes is the line; a longer one is cut to [`NODE`] bytes (the last try
//! ends cut), with no follow-up round trip asking for a shorter one; an
//! empty or thinking-only reply gives the input cut to [`NODE`] bytes. Only
//! a provider error (or a model call past [`CALL_DEADLINE`]) fails the
//! call.

use std::future::Future;
use std::pin::Pin;

use eukhe_bend::rules::compactor::{open, Fin, Next, Reply};
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, CacheBreakpoint, Context, Message, StopReason,
    TextContent, UserContent, UserContentBlock, UserMessage,
};

use super::prompts::compactor_system_prompt;
use super::{cut, view, CALL_DEADLINE, NODE, TRIES};

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
/// model and returns the model's message verbatim. It
/// signals `started` as soon as the model's response starts (its first
/// streamed event; an implementation that only sees whole replies signals
/// when it has one). Transport failures return `Err`; a reply that stopped
/// with an error is reported through its `stop_reason`. Either fails the
/// node, which the owner tries again at the next message (or after
/// [`super::RETRY`] while a turn waits), and builds from its input after
/// [`super::FAILURES`] failures. Dropping the returned future cancels the
/// call: the implementation stops its request then (the owner drops its
/// calls when it stops, and a call past [`CALL_DEADLINE`] is dropped).
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
    /// The input: the message, labeled, or the two lines joined by a
    /// newline. Cut to [`NODE`] bytes, it is the line when no reply is.
    pub input: String,
}

/// Build one line (H1): one call; its reply within [`NODE`] bytes is the
/// line, a longer one cut to [`NODE`] bytes, an empty one gives the input
/// cut so. `started` fires when the call's response starts.
///
/// # Errors
///
/// Returns an error when the summarizer fails or takes longer than
/// [`CALL_DEADLINE`], or the reply stops with an error.
pub(crate) async fn build_line(
    summarizer: &dyn Summarizer,
    request: &NodeRequest,
    timestamp: u64,
    started: ResponseStarted,
) -> anyhow::Result<String> {
    let line = match open(TRIES) {
        Next::Ends { fin, .. } => {
            return ended(fin, "", &request.input)
                .ok_or_else(|| anyhow::anyhow!("the compactor's line failed with no reply"));
        }
        Next::Asks(line) => line,
    };
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
    let context = Context {
        system_prompt: Some(compactor_system_prompt()),
        messages: vec![Message::User(UserMessage {
            content: UserContent::Blocks(blocks),
            timestamp,
        })],
        tools: None,
    };
    let call = summarizer.complete(context, started);
    let reply = match tokio::time::timeout(CALL_DEADLINE, call).await {
        Err(_) => Err(anyhow::anyhow!(
            "the compactor model did not answer within {} s",
            CALL_DEADLINE.as_secs()
        )),
        Ok(Err(error)) => Err(error),
        Ok(Ok(reply)) if matches!(reply.stop_reason, StopReason::Error | StopReason::Aborted) => {
            Err(anyhow::anyhow!(
                "the compactor model stopped with {:?}: {}",
                reply.stop_reason,
                reply.error_message.as_deref().unwrap_or("no error message")
            ))
        }
        Ok(Ok(reply)) => Ok(reply),
    };
    let (next, said, error) = match reply {
        Ok(reply) => {
            let said = reply_text(&reply).trim().to_string();
            (line.read(NODE, Reply::Says(said.len())), said, None)
        }
        Err(error) => (line.read(NODE, Reply::Erred), String::new(), Some(error)),
    };
    match (next, error) {
        (Next::Ends { fin, .. }, error) => ended(fin, &said, &request.input).ok_or_else(|| {
            error.unwrap_or_else(|| anyhow::anyhow!("the compactor's line failed on a reply"))
        }),
        // One try (law `line_calls_at_most_tries`): the line ends at its
        // first reply.
        (Next::Asks(_), _) => Err(anyhow::anyhow!(
            "the compactor's line asked for a second call after its one try"
        )),
    }
}

/// The line a line's end stands for: the reply just read (`said`), whole
/// or cut to [`NODE`] bytes, or the node's input cut so (one call leaves
/// no earlier reply to fall back on); none when the call failed.
fn ended(fin: Fin, said: &str, input: &str) -> Option<String> {
    match fin {
        Fin::Whole => Some(said.to_string()),
        Fin::CutReply => Some(cut(said).to_string()),
        Fin::CutBest | Fin::CutInput => Some(cut(input).to_string()),
        Fin::Lost => None,
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
