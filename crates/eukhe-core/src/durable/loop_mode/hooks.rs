//! The loop extension's `pi.generation` hooks.
//!
//! - `before_request`: a loop that waits for its prompt (armed or paused)
//!   adopts the prompt the user sent after it started waiting: that turn
//!   is the loop's next iteration.
//! - `on_yield`: at a final answer the turn of the loop settled: the
//!   compiled core decides (`bend/loop.bend`): run the condition command
//!   and read its evidence, then start the next iteration as the answer's
//!   continuation, or end the loop. Queued user input and unsettled
//!   children or workflow runs hold the decision (the core answers
//!   `Defer`; their run reaches its own final answer). An aborted or
//!   failed run never reaches `on_yield`: the run-end observer tells the
//!   loop (`observer.rs`).

use std::sync::Arc;

use eukhe_bend::rules::loop_mode::{step, LoopAct, LoopEvent, TurnOutcome};
use eukhe_chord::context::Context;
use eukhe_durable::entries::{UserData, USER_ENTRY};
use eukhe_durable::harness::define::hook;
use eukhe_durable::harness::types::{
    GenerationHooks, HookApi, HookRegistration, YieldContinuation,
};
use eukhe_durable::harness::{ConversationEntryQuery, GENERATION_TASK};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::EntryData;
use eukhe_types::input_origin::InputOrigin;
use eukhe_types::loop_mode::LoopPhase;
use eukhe_types::pi_ai::{Message, UserContent, UserContentBlock};
use futures::FutureExt;

use super::docs::LOOP_MODE_DOC;
use super::drive::{core_error, decide, Facts, Input, LoopHost, Mode};
use crate::durable::goals::read_doc;

/// How many of the newest entries the adoption reads to find the prompt
/// that started the turn.
const RECENT_ENTRIES: usize = 32;

/// The loop extension's hook registration on `pi.generation`.
pub(crate) fn generation_hooks(host: &LoopHost) -> HookRegistration {
    let before = host.clone();
    let yielded = host.clone();
    hook(
        &*GENERATION_TASK,
        GenerationHooks {
            before_prepare: None,
            before_request: Some(Arc::new(move |_request, api, cx| {
                let host = before.clone();
                let api = api.clone();
                let cx = cx.clone();
                async move {
                    host.adopt(&api, &cx).await?;
                    Ok(None)
                }
                .boxed()
            })),
            after_response: None,
            on_yield: Some(Arc::new(move |_message, api, cx| {
                let host = yielded.clone();
                let api = api.clone();
                let cx = cx.clone();
                async move {
                    Ok(host
                        .on_yield(&api, &cx)
                        .await?
                        .map(|(text, origin)| YieldContinuation {
                            r#continue: UserContent::Text(text),
                            origin,
                        }))
                }
                .boxed()
            })),
            after_tools: None,
            pending_work: None,
        },
    )
}

/// The text of a user message: its text blocks, joined by a newline.
fn user_text(content: &UserContent) -> String {
    match content {
        UserContent::Text(text) => text.clone(),
        UserContent::Blocks(blocks) => blocks
            .iter()
            .filter_map(|block| match block {
                UserContentBlock::Text(text) => Some(text.text.as_str()),
                UserContentBlock::Image(_) => None,
            })
            .collect::<Vec<_>>()
            .join("\n"),
    }
}

impl LoopHost {
    /// A loop that waits for its prompt adopts the newest prompt the user
    /// sent after it started waiting.
    async fn adopt(&self, api: &HookApi, cx: &Context) -> SessionResult<()> {
        let conversation_id = api.conversation_id();
        let Some(doc) = read_doc(api, &LOOP_MODE_DOC, conversation_id, cx).await? else {
            return Ok(());
        };
        if !matches!(doc.state.phase, LoopPhase::Armed | LoopPhase::Paused) {
            return Ok(());
        }
        let since = doc.waiting_since_ms.unwrap_or(0);
        let conversation = self.conversation(conversation_id, cx).await?;
        let page = conversation
            .entries(ConversationEntryQuery::default(), RECENT_ENTRIES, None, cx)
            .await?;
        // Newest first: the newest user entry is the one this turn answers.
        let Some(entry) = page
            .items
            .iter()
            .find(|entry| entry.kind == USER_ENTRY.kind())
        else {
            return Ok(());
        };
        let origin = UserData::decode(entry.data.as_ref())
            .map_err(|error| SessionError::error(format!("a user entry's origin: {error}")))?
            .origin;
        let Some(Message::User(user)) = entry.model.as_ref().and_then(|model| model.first()) else {
            return Ok(());
        };
        if origin != InputOrigin::User || user.timestamp <= since {
            return Ok(());
        }
        let text = user_text(&user.content);
        if text.trim().is_empty() {
            return Ok(());
        }
        let facts = Facts {
            blocked: false,
            funded: true,
        };
        decide(
            &conversation,
            Input::Prompt { text },
            facts,
            Mode::Idle,
            true,
            cx,
        )
        .await?;
        Ok(())
    }

    /// The loop's step at a final answer; `Some` continues the run with
    /// the loop's prompt as its next iteration.
    #[tracing::instrument(skip_all)]
    async fn on_yield(
        &self,
        api: &HookApi,
        cx: &Context,
    ) -> SessionResult<Option<(String, InputOrigin)>> {
        let conversation_id = api.conversation_id();
        let task_id = api.task_id();
        let Some(doc) = read_doc(api, &LOOP_MODE_DOC, conversation_id, cx).await? else {
            return Ok(None);
        };
        if !doc.state.phase.is_on() {
            return Ok(None);
        }
        // A rerun of the generation that already continued into an
        // iteration: the core names the turn in flight, and it is this
        // one. The continuation is repeated, nothing is decided again.
        if let Some(record) = doc.yield_record.filter(|record| record.task_id == task_id) {
            let (_, act) =
                step(&doc.state, &LoopEvent::Restart).map_err(|error| core_error(&error))?;
            return Ok(match act {
                LoopAct::Resume { iteration, text } if iteration == record.iteration => {
                    Some((text, InputOrigin::Loop { iteration }))
                }
                LoopAct::Resume { .. }
                | LoopAct::Rest
                | LoopAct::Submit { .. }
                | LoopAct::Adopt { .. }
                | LoopAct::Judge { .. }
                | LoopAct::Report(_)
                | LoopAct::Defer => None,
            });
        }
        // A turn whose first request never asked (a rerun) is adopted here.
        self.adopt(api, cx).await?;
        let conversation = self.conversation(conversation_id, cx).await?;
        self.drive(
            &conversation,
            Input::TurnSettled(TurnOutcome::Ran),
            Mode::Yield(task_id),
            cx,
        )
        .await
    }
}
