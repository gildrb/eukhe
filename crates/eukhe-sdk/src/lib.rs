//! Run Eukhe sessions inside your own process.
//!
//! A host that runs sessions in its own process (no daemon, no wire) opens
//! them here. The facade is thin: the engine's own types are re-exported
//! unchanged, plus the few calls every embedding repeats.
//!
//! ```no_run
//! use eukhe_sdk::{context::BACKGROUND_CONTEXT, open_session, SessionConfig, SessionStorage};
//!
//! # async fn run() -> anyhow::Result<()> {
//! let cx = &*BACKGROUND_CONTEXT;
//! let config = SessionConfig::new(
//!     "/home/me/.eukhe",
//!     "/home/me/project",
//!     eukhe_sdk::new_session_id(),
//!     SessionStorage::Memory,
//! );
//! let session = open_session(config, cx).await?;
//! let conversation = session.main();
//! let mut events = eukhe_sdk::watch(&session, &conversation, cx).await?;
//! eukhe_sdk::prompt(&conversation, "Summarize README.md", cx).await?;
//! events.delivered().await;
//! while let Some(batch) = events.try_next() {
//!     for event in batch.iter() {
//!         println!("{}", event.kind());
//!     }
//! }
//! events.stop().await;
//! session.close(cx).await?;
//! # Ok(())
//! # }
//! ```
//!
//! - [`open_session`] opens a [`SessionConfig`]: `SessionConfig::new` sets
//!   a default for every optional input (the settings' model, the
//!   settings' thinking level, models from eukhe auth and `models.json`);
//!   set its public fields to override one. [`SessionStorage::Jsonl`]
//!   keeps the session on disk, [`SessionStorage::Memory`] in memory.
//! - [`prompt`] submits user text to a conversation and waits until the
//!   conversation is idle again.
//! - [`watch`] streams a conversation's committed events.
//! - [`unknown_effects`] lists a conversation's interrupted effects whose
//!   outcome a restart could not tell, [`resolve_unknown_effect`] settles
//!   one after the host checked the world, and [`watch_unknown_effects`]
//!   follows the ledger (its current state first, then every change).
//! - [`available_models`] lists the chat models whose providers have
//!   credentials.
//! - [`set_budget`] gives a session a [`budget`]: limits on money, tokens,
//!   tool calls and model requests, and a wall-clock deadline, that
//!   nothing the session or the agents beneath it spend can pass.
//!   [`add_budget`] adds to it (time moves the deadline; an exhausted
//!   session works again), [`budget_report`] reads what is free, held,
//!   spent and lent and the time left, [`watch_budget`] follows every
//!   change, and [`audit_budget`] replays the budget's ledger.
//! - [`context`] holds the [`Context`](context::Context) every engine call
//!   takes; [`BACKGROUND_CONTEXT`](context::BACKGROUND_CONTEXT) never
//!   cancels.
//!
//! Versioning: this crate follows the workspace version. A change to a
//! signature here, or to a re-exported type, is a breaking change of the
//! facade.

use std::sync::Arc;

use futures::FutureExt;
use tokio::sync::mpsc;

pub use eukhe_ai::models::Models;
pub use eukhe_chord::context;
pub use eukhe_core::durable::budget::{BudgetError, BudgetGate};
pub use eukhe_core::durable::{
    create_models, open_session, EukheSession, ModelRequest, OpenError, SessionConfig,
    SessionModels, SessionStorage,
};
pub use eukhe_durable::harness::effects::{
    EffectKind, EffectResolution, UnknownEffect, UnknownEffectUpdates,
};
pub use eukhe_durable::harness::{
    AgentEvent, AgentEventBatch, AgentEventStream, Conversation, SnapshotEvent,
};
pub use eukhe_types::budget;
pub use eukhe_types::daemon::BudgetAudit;
pub use eukhe_types::pi_ai::Model;

use budget::{BudgetAmounts, BudgetLimits, BudgetReport};
use context::Context;
use eukhe_durable::harness::types::InputSubmissionDraft;

/// A new session id (a `UUIDv7`, the form the engine stores).
#[must_use]
pub fn new_session_id() -> String {
    uuid::Uuid::now_v7().to_string()
}

/// Submit `text` to `conversation` as the user's input, wait until its run
/// settles, then until the conversation is idle (continuations, queued
/// input and compaction included).
///
/// # Errors
///
/// The submission is refused (the session closed, `cx` cancelled), or a
/// wait fails.
pub async fn prompt(conversation: &Conversation, text: &str, cx: &Context) -> anyhow::Result<()> {
    let submission = conversation
        .submit(InputSubmissionDraft::new(text.to_owned()), cx)
        .await?;
    submission.wait(cx).await?;
    conversation.wait_for_idle(cx).await?;
    Ok(())
}

/// The chat models of `models` whose providers have credentials (a stored
/// key or login, the provider's environment key, or a configured
/// `apiKey`).
///
/// # Errors
///
/// An auth check or a provider's model list fails.
pub async fn available_models(models: &Models) -> anyhow::Result<Vec<Model>> {
    models
        .get_available(None, eukhe_ai::auth::AuthOperationOptions::default())
        .await
        .map_err(|error| anyhow::anyhow!("list the available models: {error}"))
}

/// Start streaming `conversation`'s events: one batch per commit, from the
/// moment of the call. The stream's start is its [`Events::snapshot`].
///
/// # Errors
///
/// The session's harness cannot attach the watch (closed, `cx`
/// cancelled).
pub async fn watch(
    session: &EukheSession,
    conversation: &Conversation,
    cx: &Context,
) -> anyhow::Result<Events> {
    let stream =
        eukhe_durable::harness::watch_events(session.harness(), conversation.id(), cx).await?;
    let (sender, batches) = mpsc::unbounded_channel();
    stream.start(Arc::new(move |batch, _cx| {
        // A dropped receiver only means nobody reads any more.
        let _ = sender.send(batch);
        futures::future::ready(Ok(())).boxed()
    }))?;
    Ok(Events { stream, batches })
}

/// The ledger of `conversation`'s interrupted effects whose outcome a
/// restart could not tell, oldest first, open and resolved.
///
/// # Errors
///
/// The ledger cannot be read (the session closed, `cx` cancelled).
pub async fn unknown_effects(
    session: &EukheSession,
    conversation: &Conversation,
    cx: &Context,
) -> anyhow::Result<Vec<UnknownEffect>> {
    Ok(eukhe_durable::harness::effects::read_unknown_effects(
        session.harness(),
        conversation.id(),
        cx,
    )
    .await?)
}

/// Settle `conversation`'s open unknown effect `id` as `resolution`: the
/// effect as resolved, or `None` when the ledger holds no open effect of
/// that id (never noted, or settled already).
///
/// # Errors
///
/// The commit fails (the session closed, `cx` cancelled).
pub async fn resolve_unknown_effect(
    session: &EukheSession,
    conversation: &Conversation,
    id: &str,
    resolution: EffectResolution,
    cx: &Context,
) -> anyhow::Result<Option<UnknownEffect>> {
    let conversation_id = conversation.id();
    let id = id.to_owned();
    Ok(session
        .harness()
        .commit(
            move |tx| async move {
                eukhe_durable::harness::effects::resolve_unknown(
                    &tx,
                    conversation_id,
                    &id,
                    resolution,
                )
                .await
            },
            cx,
        )
        .await?)
}

/// Follow `conversation`'s ledger: the current ledger first, then the
/// ledger after every change (an effect noted or resolved). Dropping the
/// stream stops it.
///
/// # Errors
///
/// The session's harness cannot attach the watch (closed).
pub fn watch_unknown_effects(
    session: &EukheSession,
    conversation: &Conversation,
    cx: &Context,
) -> anyhow::Result<UnknownEffectUpdates> {
    Ok(eukhe_durable::harness::effects::watch_unknown_effects(
        session.harness(),
        conversation.id(),
        cx,
    )?)
}

/// Give `session` the budget `limits`; answers the budget's state. A
/// dimension without a limit is unlimited. Set it before the session's
/// first prompt: nothing is spent past a budget from the moment it is set.
///
/// # Errors
///
/// The session already has a budget (the [`BudgetError`] `AlreadyOpen`:
/// add to it with [`add_budget`]), or its ledger cannot be written.
pub async fn set_budget(
    session: &EukheSession,
    limits: BudgetLimits,
) -> anyhow::Result<BudgetReport> {
    let gate = session.budget();
    Ok(tokio::task::spawn_blocking(move || gate.set(limits)).await??)
}

/// Add `amounts` to `session`'s budget; answers the budget's state. A
/// session that used its budget up works again; a session without a
/// budget gets `amounts` as its budget.
///
/// # Errors
///
/// The session's budget comes from a parent session (the [`BudgetError`]
/// `NotRoot`: add to the parent's), the sum is too large, or the ledger
/// cannot be written.
pub async fn add_budget(
    session: &EukheSession,
    amounts: BudgetAmounts,
) -> anyhow::Result<BudgetReport> {
    let gate = session.budget();
    Ok(tokio::task::spawn_blocking(move || gate.add(amounts)).await??)
}

/// The state of `session`'s budget: its limits and what is free, held,
/// spent and lent to child sessions. `None`: the session has no budget.
///
/// # Errors
///
/// The read did not finish (the runtime is shutting down).
pub async fn budget_report(session: &EukheSession) -> anyhow::Result<Option<BudgetReport>> {
    let gate = session.budget();
    Ok(tokio::task::spawn_blocking(move || gate.report()).await?)
}

/// Follow `session`'s budget: the receiver holds the budget's state and
/// changes with every reservation, settlement, allotment to a child and
/// added budget, so a host can show it and react (add budget when the
/// phase leaves [`budget::BudgetPhase::Working`]).
#[must_use]
pub fn watch_budget(session: &EukheSession) -> tokio::sync::watch::Receiver<Option<BudgetReport>> {
    session.budget().watch()
}

/// Audit `session`'s budget: every record of its ledger replayed, and the
/// settled spends added up against the total the budget reports.
///
/// # Errors
///
/// The session has no budget (the [`BudgetError`] `NoBudget`), or its
/// ledger does not read.
pub async fn audit_budget(session: &EukheSession) -> anyhow::Result<BudgetAudit> {
    let gate = session.budget();
    let audit = tokio::task::spawn_blocking(move || gate.audit()).await??;
    Ok(BudgetAudit {
        records: audit.records,
        settled: audit.settled,
        spent: audit.spent,
        exact: audit.exact(),
        first_mismatch: audit.first_mismatch,
    })
}

/// A conversation's event stream (see [`watch`]).
pub struct Events {
    stream: AgentEventStream,
    batches: mpsc::UnboundedReceiver<AgentEventBatch>,
}

impl Events {
    /// The conversation's state when the stream started.
    #[must_use]
    pub fn snapshot(&self) -> &SnapshotEvent {
        self.stream.snapshot()
    }

    /// The next batch, waiting for one; `None` once the stream stopped and
    /// every batch was read.
    pub async fn next(&mut self) -> Option<AgentEventBatch> {
        self.batches.recv().await
    }

    /// The next batch already delivered, without waiting. After
    /// [`prompt`] returns, [`Events::delivered`] makes every batch it
    /// committed readable here.
    pub fn try_next(&mut self) -> Option<AgentEventBatch> {
        self.batches.try_recv().ok()
    }

    /// Resolves once every batch committed so far is readable.
    pub async fn delivered(&self) {
        self.stream.delivered().await;
    }

    /// Stop the stream; batches already delivered stay readable.
    pub async fn stop(&self) {
        self.stream.stop().await;
    }
}
