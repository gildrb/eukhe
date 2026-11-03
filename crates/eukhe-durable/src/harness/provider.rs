//! The `pi.provider` document: a stable provider-facing identity per
//! conversation (`harness/provider.ts`).

use eukhe_ai::utils::uuid::uuidv7;
use eukhe_chord::context::Context;
use eukhe_chord::json::{from_json, JsonValue};
use serde::{Deserialize, Serialize};

use crate::documents::{ConversationDoc, DocDefinition};
use crate::session::{Session, SessionError, SessionResult, Tx};
use crate::tasks::{TaskRuntime, TaskValue};
use crate::types::{ConversationId, DocumentReaderExt, LatestFork};

/// Stable provider-facing identity of one conversation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ProviderState {
    pub session_id: String,
}

fn initial_provider_state() -> ProviderState {
    ProviderState {
        // `uuidv7()` fails only when the per-millisecond sequence is
        // exhausted or the OS random source fails; TS throws there, which a
        // document initializer (`fn() -> T`) cannot carry.
        #[expect(
            clippy::expect_used,
            reason = "document initializers are infallible; see above"
        )]
        session_id: uuidv7(None).expect("uuidv7 generates a provider session ID"),
    }
}

/// Built-in provider state; every fork starts with a fresh identity instead
/// of copying its parent.
pub static PROVIDER_DOC: ConversationDoc<ProviderState> = match ConversationDoc::define(
    DocDefinition {
        kind: "pi.provider",
        version: 1,
        initial: initial_provider_state,
        migrate: None,
        checkpoint_when: Some(|_, _, _| true),
    },
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("pi.provider has a valid version"),
};

/// Return the persisted identity without writing in the normal path. A
/// legacy conversation without `pi.provider` gets one migration commit whose
/// `tx.doc()` runs `initial()` before the provider request starts.
///
/// # Errors
///
/// Read or commit failures of the runtime.
pub async fn ensure_provider_session_id<I, S, R, H>(
    runtime: &TaskRuntime<I, S, R, H>,
    cx: &Context,
) -> SessionResult<String>
where
    I: TaskValue,
    S: TaskValue,
    R: TaskValue,
    H: Send + Sync + 'static,
{
    let conversation_id = runtime.conversation_id();
    if let Some(existing) = runtime.snapshot(&PROVIDER_DOC, conversation_id, cx).await? {
        let state: ProviderState = from_json(&JsonValue::Object(existing))?;
        return Ok(state.session_id);
    }
    let created = std::sync::Arc::new(std::sync::Mutex::new(None));
    let slot = std::sync::Arc::clone(&created);
    runtime
        .commit(
            move |tx, _current| async move {
                let session_id = stored_session_id(&tx, conversation_id).await?;
                *slot
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner) = session_id;
                Ok(None)
            },
            cx,
        )
        .await?;
    let created = created
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .take();
    created.ok_or_else(|| no_session_id(conversation_id))
}

/// [`ensure_provider_session_id`] outside a task invocation: the
/// conversation's identity read through `session`, with the same migration
/// commit for a legacy conversation.
///
/// # Errors
///
/// Read or commit failures of the session.
pub(crate) async fn session_provider_session_id(
    session: &Session,
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<String> {
    if let Some(existing) = session.snapshot(&PROVIDER_DOC, conversation_id, cx).await? {
        let state: ProviderState = from_json(&JsonValue::Object(existing))?;
        return Ok(state.session_id);
    }
    session
        .commit(
            move |tx| async move { stored_session_id(&tx, conversation_id).await },
            cx,
        )
        .await?
        .ok_or_else(|| no_session_id(conversation_id))
}

/// The identity `tx` holds; reading `pi.provider` there runs `initial()`
/// for a conversation without it.
async fn stored_session_id(
    tx: &Tx,
    conversation_id: ConversationId,
) -> SessionResult<Option<String>> {
    let state = tx.doc(&PROVIDER_DOC, conversation_id).await?;
    Ok(state.get("sessionId")?.and_then(|item| {
        item.as_value()
            .and_then(|value| value.as_str().map(str::to_owned))
    }))
}

fn no_session_id(conversation_id: ConversationId) -> SessionError {
    SessionError::error(format!(
        "Conversation {conversation_id} has no provider session ID"
    ))
}
