//! The `pi.provider` document: a stable provider-facing identity per
//! conversation (`harness/provider.ts`).

use eukhe_chord::context::Context;
use eukhe_chord::json::{from_json, JsonValue};
use eukhe_pi_ai::utils::uuid::uuidv7;
use serde::{Deserialize, Serialize};

use crate::documents::{ConversationDoc, DocDefinition};
use crate::session::{SessionError, SessionResult};
use crate::tasks::{TaskRuntime, TaskValue};
use crate::types::{DocumentReaderExt, LatestFork};

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
                let state = tx.doc(&PROVIDER_DOC, conversation_id).await?;
                let session_id = state.get("sessionId")?.and_then(|item| {
                    item.as_value()
                        .and_then(|value| value.as_str().map(str::to_owned))
                });
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
    created.ok_or_else(|| {
        SessionError::error(format!(
            "Conversation {conversation_id} has no provider session ID"
        ))
    })
}
