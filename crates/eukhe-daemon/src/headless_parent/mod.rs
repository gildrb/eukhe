//! A headless (print/json/RPC) session as the parent of its daemon
//! subagents. The session runs in the client process, so the supervisor
//! hosts no worker for it: the client registers it
//! (`register_headless_parent`) on one connection it keeps open for the
//! session's life ([`HeadlessParentLink`]). The supervisor lists it in its
//! roster views, so a child's family resolves it as the Parent, and routes
//! every `send_message` to it over that connection as a
//! `headless_parent_delivery` frame; the client admits the message into
//! the session's main conversation through the same delivery a worker
//! runs ([`crate::agent_message_delivery`]) and answers with
//! `headless_parent_receipt`. The connection's close (any exit of the
//! client, a crash or a kill included) ends the registration, and the
//! supervisor closes the parent's resident children like a dead parent
//! worker's ([`crate::supervisor_parent_death`]).
//!
//! The parent is never a wake target: its storage is leased by the client
//! process, so the supervisor refuses to launch a worker over it while it
//! is registered.

mod routes;

use std::path::PathBuf;
use std::sync::Weak;
use std::time::Duration;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_chord::json::{from_json, JsonError, JsonValue};
use eukhe_core::durable::EukheSession;
use eukhe_durable::harness::{InboxState, INBOX_DOC};
use eukhe_durable::session::SessionError;
use futures::FutureExt as _;
use serde_json::{json, Value};

use crate::agent_message_delivery::{
    AgentMessageDelivery, DeliveryRefusal, Recipient, RecipientRun,
};
use crate::supervisor_link::{HeldLink, SupervisorLink};
use crate::worker::InputRowError;

pub(crate) use routes::{HeadlessParents, HeadlessTarget};

/// The frame type of a message the supervisor pushes to a registered
/// headless parent.
const DELIVERY_FRAME: &str = "headless_parent_delivery";

/// Budget for reaching the supervisor and its hello at registration.
const REGISTER_CONNECT_TIMEOUT: Duration = Duration::from_secs(5);

/// Budget for the whole registration (connect, hello and answer): a
/// wedged supervisor must not hold the session's first spawn.
const REGISTER_TIMEOUT: Duration = Duration::from_secs(15);

/// The identity a headless session registers with. Its live session id is
/// its session id.
#[derive(Debug, Clone)]
pub struct HeadlessParentIdentity {
    pub session_id: String,
    pub session_name: Option<String>,
    /// The session's storage; `None` for a memory session.
    pub session_file: Option<PathBuf>,
    pub cwd: PathBuf,
}

/// Why a registration failed.
#[derive(Debug, thiserror::Error)]
pub enum HeadlessParentError {
    /// The supervisor could not be reached, or the connection broke
    /// before it answered.
    #[error("cannot register the headless parent with the daemon supervisor: {0:#}")]
    Link(anyhow::Error),
    /// The supervisor answered with a refusal (an older daemon without
    /// the command, or a session a daemon worker hosts).
    #[error("the daemon supervisor refused the headless parent: {0}")]
    Refused(String),
    /// The supervisor did not answer within the registration budget.
    #[error("the daemon supervisor did not answer the headless parent registration")]
    TimedOut,
}

/// A live registration. Dropping it closes its connection, which ends the
/// registration on the supervisor.
pub struct HeadlessParentLink {
    serve: tokio::task::JoinHandle<()>,
}

impl Drop for HeadlessParentLink {
    fn drop(&mut self) {
        self.serve.abort();
    }
}

impl HeadlessParentLink {
    /// Register `identity` with the supervisor `link` reaches, and serve
    /// the deliveries to it into `session` until the link drops or the
    /// supervisor closes the connection.
    ///
    /// # Errors
    ///
    /// The supervisor cannot be reached, or refuses the registration.
    #[tracing::instrument(level = "debug", skip_all, fields(session = %identity.session_id))]
    pub async fn register(
        link: &SupervisorLink,
        identity: HeadlessParentIdentity,
        session: Weak<EukheSession>,
    ) -> Result<Self, HeadlessParentError> {
        let mut early = Vec::new();
        let registered = tokio::time::timeout(
            REGISTER_TIMEOUT,
            link.hold(
                json!({
                    "type": "register_headless_parent",
                    "sessionId": identity.session_id,
                    "sessionName": identity.session_name,
                    "sessionFile": identity
                        .session_file
                        .as_ref()
                        .map(|file| file.to_string_lossy()),
                    "cwd": identity.cwd.to_string_lossy(),
                }),
                REGISTER_CONNECT_TIMEOUT,
                |frame| early.push(frame.clone()),
            ),
        )
        .await
        .map_err(|_elapsed| HeadlessParentError::TimedOut)?;
        let (response, held) = registered.map_err(HeadlessParentError::Link)?;
        if !response.success {
            return Err(HeadlessParentError::Refused(
                response
                    .error
                    .unwrap_or_else(|| "registration failed".to_string()),
            ));
        }
        Ok(Self {
            serve: tokio::spawn(serve(held, early, identity, session)),
        })
    }
}

/// Answer the deliveries on the registration's connection, `early` (the
/// frames that came before the registration's answer) first, until the
/// supervisor closes it.
#[tracing::instrument(level = "debug", skip_all, fields(session = %identity.session_id))]
async fn serve(
    mut held: HeldLink,
    early: Vec<Value>,
    identity: HeadlessParentIdentity,
    session: Weak<EukheSession>,
) {
    let mut early = early.into_iter();
    loop {
        let frame = match early.next() {
            Some(frame) => frame,
            None => match held.next_frame().await {
                Ok(Some(frame)) => frame,
                Ok(None) => {
                    tracing::warn!(
                        "the daemon supervisor closed the headless parent link; messages to this session no longer arrive"
                    );
                    return;
                }
                Err(error) => {
                    tracing::warn!(%error, "the headless parent link broke");
                    return;
                }
            },
        };
        if frame.get("type").and_then(Value::as_str) != Some(DELIVERY_FRAME) {
            continue;
        }
        let Some(delivery_id) = frame.get("deliveryId").and_then(Value::as_str) else {
            tracing::warn!(%frame, "a headless parent delivery without a delivery id");
            continue;
        };
        let payload = frame.get("delivery").cloned().unwrap_or(Value::Null);
        let answer = match session.upgrade() {
            Some(session) => deliver(&session, &identity, &payload).await,
            None => Err(DeliverError::Closed),
        };
        let mut receipt = json!({
            "type": "headless_parent_receipt",
            "deliveryId": delivery_id,
        });
        match answer {
            Ok(value) => receipt["receipt"] = value,
            Err(error) => receipt["error"] = json!(error.to_string()),
        }
        if let Err(error) = held.send(receipt).await {
            tracing::warn!(%error, "the headless parent receipt was not sent");
            return;
        }
    }
}

/// Why a delivered message was not admitted; the receipt carries the text.
#[derive(Debug, thiserror::Error)]
enum DeliverError {
    #[error("The headless session closed")]
    Closed,
    #[error(transparent)]
    Refused(#[from] DeliveryRefusal),
    #[error(transparent)]
    Session(#[from] SessionError),
    /// The inbox document does not decode.
    #[error(transparent)]
    Inbox(#[from] JsonError),
    #[error(transparent)]
    Row(#[from] InputRowError),
}

/// Admit one delivered message into `session`'s main conversation; the
/// answer is its receipt.
#[tracing::instrument(level = "debug", skip_all)]
async fn deliver(
    session: &EukheSession,
    identity: &HeadlessParentIdentity,
    payload: &Value,
) -> Result<Value, DeliverError> {
    let message = AgentMessageDelivery::validated_message(payload)?;
    let cx = &BACKGROUND_CONTEXT;
    let main = session.main();
    let harness = session.harness();
    let pending = match harness.snapshot(&INBOX_DOC, main.id(), cx).await? {
        Some(inbox) => from_json::<InboxState>(&JsonValue::Object(inbox))?
            .items
            .len(),
        None => 0,
    };
    let run = match main.wait_for_idle(cx).now_or_never() {
        Some(idle) => {
            idle?;
            RecipientRun::Idle
        }
        None => RecipientRun::Busy,
    };
    let recipient = Recipient {
        session_id: Some(&identity.session_id),
        active_session_id: &identity.session_id,
        session_file: identity.session_file.as_deref(),
    };
    let mut target = json!({
        "activeSessionId": identity.session_id,
        "sessionId": identity.session_id,
        "runtimeKind": "top-level",
    });
    if let Some(name) = identity
        .session_name
        .as_deref()
        .filter(|name| !name.is_empty())
    {
        target["sessionName"] = json!(name);
    }
    let delivery = AgentMessageDelivery::prepare(payload, message, &recipient, pending, target)?;
    delivery
        .record_child_reply(harness, || Ok(session.main()))
        .await;
    let draft = delivery.request.draft()?;
    main.submit(draft, cx).await?;
    Ok(delivery.receipt(run))
}
