//! A side request that continues a conversation's next turn: it sends the
//! request the turn will start with, so the provider reads the prompt cache
//! the conversation's requests share instead of writing one of its own.

use std::sync::Arc;

use eukhe_ai::types::SimpleStreamOptions;
use eukhe_ai::utils::context_tokens::model_tokenizer;
use eukhe_chord::context::Context;
use eukhe_types::pi_ai::{Message, Model, ModelThinkingLevel};
use futures::future::BoxFuture;
use futures::FutureExt;

use super::{Conversation, ConversationEntryQuery, Core};
use crate::entries::SYSTEM_ENTRY;
use crate::harness::context::read_context;
use crate::harness::generation::reasoning;
use crate::harness::live::run::timestamp;
use crate::harness::live::LIVE_DOC;
use crate::harness::prompt::{next_system_entries, replay_sections, system_cache_breakpoint};
use crate::harness::provider::session_provider_session_id;
use crate::harness::types::{Agent, PromptInput};
use crate::session::SessionResult;
use crate::types::{EntryId, EntryQuery};

/// The request a conversation's next turn starts with, before its input:
/// what a side request sends ahead of its own last message so that its
/// prompt, tools, and messages are the turn's byte for byte.
pub struct Continuation {
    /// The conversation's model.
    pub model: Model,
    /// The committed model context the turn sends (the system prompt and
    /// tool loadout ride its positional system messages). The generation's
    /// `before_request` hooks have not shaped it: a caller applies its own.
    pub messages: Vec<Message>,
    /// The turn's request options: the conversation's stream settings, its
    /// provider session ID, the agent's reasoning, and the system prompt's
    /// cache mark. The caller adds its signal.
    pub options: SimpleStreamOptions,
}

impl Conversation {
    /// The request the conversation's next turn would start with
    /// ([`Continuation`]); `None` when the agent has no available model.
    ///
    /// When the transcript lacks `pi.system` entries the turn's preparation
    /// would append (after a compaction, the baseline under the new head),
    /// they are appended now, as that preparation would, so the turn finds
    /// them and the side request and the turn send one prefix. They go in
    /// only while the conversation is idle and its tail is the one they
    /// were planned on: a run's preparation owns the transcript of a busy
    /// conversation.
    #[must_use]
    pub fn continuation(
        &self,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Continuation>>> {
        let core = Arc::clone(self.core());
        let conversation = self.clone();
        let cx = cx.clone();
        async move {
            let agent = Arc::new(conversation.agent(&cx).await?);
            let Some(model) = agent.model.as_ref().and_then(|reference| {
                core.options
                    .models
                    .get_model(&reference.provider, &reference.model_id)
            }) else {
                return Ok(None);
            };
            prepare_system(&core, &conversation, &agent, &model, &cx).await?;
            let id = conversation.id();
            let messages = read_context(&core.session, id, &cx, None).await?.messages;
            let mut options = Core::settings(&core.options).stream.simple_stream_options();
            options.stream.session_id =
                Some(session_provider_session_id(&core.session, id, &cx).await?);
            options.reasoning = reasoning(agent.thinking_level);
            options.disable_reasoning = matches!(agent.thinking_level, ModelThinkingLevel::Off);
            options.stream.system_cache_breakpoint =
                system_cache_breakpoint(&agent.sections, &messages);
            Ok(Some(Continuation {
                model,
                messages,
                options,
            }))
        }
        .boxed()
    }
}

/// Append the `pi.system` entries the next generation's preparation would
/// plan for the conversation's current transcript, while it is idle.
async fn prepare_system(
    core: &Arc<Core>,
    conversation: &Conversation,
    agent: &Arc<Agent>,
    model: &Model,
    cx: &Context,
) -> SessionResult<()> {
    let id = conversation.id();
    let tail = newest_entry(conversation, cx).await?;
    let view = read_context(&core.session, id, cx, None).await?;
    let env = match core.build_env(id, cx).await {
        Ok(env) => env,
        Err(error) if cx.aborted() => return Err(error),
        Err(error) => {
            (core.report)(error);
            None
        }
    };
    let input = PromptInput {
        conversation_id: id,
        agent: Arc::clone(agent),
        tokenizer: model_tokenizer(model),
        env,
        shown: replay_sections(&view.messages),
        read: Arc::new(core.session.clone()),
    };
    let report = |error| {
        (core.report)(error);
        Ok(())
    };
    let entries = next_system_entries(&input, &view, &report, timestamp((core.now)())?, cx).await?;
    if entries.is_empty() {
        return Ok(());
    }
    core.session
        .commit(
            move |tx| async move {
                let idle = tx.doc(&LIVE_DOC, id).await?.get("run")?.is_none();
                let unchanged = tx
                    .scan_entries(EntryQuery::new(id), 1, None)
                    .await?
                    .items
                    .first()
                    .map(|entry| entry.id)
                    == tail;
                if idle && unchanged {
                    for entry in entries {
                        tx.append_typed_entry(&SYSTEM_ENTRY, id, entry).await?;
                    }
                }
                Ok(())
            },
            cx,
        )
        .await
}

/// The conversation's newest entry, if any.
async fn newest_entry(conversation: &Conversation, cx: &Context) -> SessionResult<Option<EntryId>> {
    Ok(conversation
        .entries(ConversationEntryQuery::default(), 1, None, cx)
        .await?
        .items
        .first()
        .map(|entry| entry.id))
}
