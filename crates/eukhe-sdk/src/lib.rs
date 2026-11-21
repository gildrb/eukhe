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
//! eukhe_sdk::prompt(&session, &conversation, "Summarize README.md", cx).await?;
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
//! - [`open_session`] opens a [`SessionConfig`] whose runs are SDK runs:
//!   `SessionConfig::new` sets a default for every optional input (the
//!   settings' model, the settings' thinking level, models from eukhe auth
//!   and `models.json`); set its public fields to override one.
//!   [`SessionStorage::Jsonl`] keeps the session on disk,
//!   [`SessionStorage::Memory`] in memory.
//! - [`prompt`] submits user text to a conversation as a new SDK run and
//!   waits until the conversation is idle again. A run goes until
//!   finished unless the principal set limits or turned them on
//!   (`budget.limits`); its spend is counted either way.
//! - [`watch`] streams a conversation's committed events.
//! - [`unknown_effects`] lists the steps of a conversation a restart could
//!   not tell the outcome of and treated as not run (each in its run's
//!   end-of-run report), [`resolve_unknown_effect`] corrects one after the
//!   host checked the world (optional: nothing waits for it), and
//!   [`watch_unknown_effects`] follows the ledger (its current state first,
//!   then every change).
//! - [`available_models`] lists the chat models whose providers have
//!   credentials.
//! - [`set_budget`] sets the [`budget`] limits of the session's runs (a
//!   number or `unlimited` per dimension: money, tokens, tool calls, model
//!   requests, and a wall-clock time per run) that nothing the session or
//!   the agents beneath it spend can pass; each model request and tool
//!   call reserves its worst case first, and a provider that reports more
//!   than the reserve leaves an overrun. Its [`BudgetScope`] says which
//!   runs: [`BudgetScope::Run`] is `/budget set` (the running run, or,
//!   while the session is idle, the next prompt's run only),
//!   [`BudgetScope::Standing`] is a create's `budget` config (every run
//!   from now on, the running one included). [`add_budget`] adds to the
//!   current run (time moves the deadline; an exhausted session works
//!   again), [`budget_report`] reads what is free, held, spent and lent,
//!   each limit's source, the time left and the limits set for the next
//!   run, [`watch_budget`] follows every change, [`watch_plan_notices`]
//!   the plan usage notices, and [`audit_budget`] replays the budget's
//!   ledger.
//! - [`set_acceptance`] sets the acceptance checks of a conversation's
//!   task as its owner (pass [`owner_checks`] of the explicit
//!   [`CheckSpec`]s to add the intent check);
//!   [`acceptance_state`] reads its [`AcceptanceState`] (its
//!   [`AcceptanceLabel`]: checks passed (unconfined), failed or
//!   unverified; verified is reserved for confined runs), and
//!   [`watch_acceptance_updates`] streams every change. An
//!   [`AcceptanceSeed`] is the checks a session starts with.
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
pub use eukhe_core::durable::acceptance::{
    acceptance_state, set_acceptance, watch_acceptance_updates, AcceptanceUpdates,
};
pub use eukhe_core::durable::budget::{BudgetError, BudgetGate, RunError, RunStart};
pub use eukhe_core::durable::{
    create_models, EukheSession, ModelRequest, OpenError, SessionConfig, SessionModels,
    SessionStorage,
};
pub use eukhe_durable::harness::effects::{
    EffectKind, EffectResolution, UnknownEffect, UnknownEffectUpdates,
};
pub use eukhe_durable::harness::{
    AgentEvent, AgentEventBatch, AgentEventStream, Conversation, SnapshotEvent,
};
pub use eukhe_types::acceptance::{
    owner_checks, AcceptanceLabel, AcceptanceSeed, AcceptanceState, CheckSpec,
};
pub use eukhe_types::budget;
pub use eukhe_types::daemon::BudgetAudit;
pub use eukhe_types::pi_ai::Model;

use budget::{BudgetAmounts, BudgetReport, PlanNotice, RunKind, RunLimits};
use context::Context;
use eukhe_chord::json::{from_json, JsonValue};
use eukhe_durable::harness::types::InputSubmissionDraft;
use eukhe_durable::harness::{LiveState, LIVE_DOC};

/// A new session id (a `UUIDv7`, the form the engine stores).
#[must_use]
pub fn new_session_id() -> String {
    uuid::Uuid::now_v7().to_string()
}

/// Open `config` as a session of an embedding host: each of its runs, and
/// a budget set before its first prompt, is an SDK run (B15).
///
/// # Errors
///
/// The session's storage, settings, models or harness do not open.
pub async fn open_session(config: SessionConfig, cx: &Context) -> Result<EukheSession, OpenError> {
    let config = SessionConfig {
        run_kind: RunKind::Sdk,
        ..config
    };
    eukhe_core::durable::open_session(config, cx).await
}

/// Submit `text` to `conversation` of `session` as the user's input, as a
/// new run of the session (its limits renewed: [`set_budget`], the limits
/// set for it while the session was idle used up; a `/b` prefix of `text`
/// fills it with the presets and limits it asks, and the model gets what
/// follows the prefix), wait until its run settles, then until the
/// conversation is idle (continuations, queued input and compaction
/// included).
///
/// # Errors
///
/// A `/b` prefix that does not read, the run's limits do not fill (a
/// `budget.*` setting that is no limit, a ledger that cannot be written),
/// the submission is refused (the session closed, `cx` cancelled), or a
/// wait fails.
pub async fn prompt(
    session: &EukheSession,
    conversation: &Conversation,
    text: &str,
    cx: &Context,
) -> anyhow::Result<()> {
    let gate = session.budget();
    let message = text.to_owned();
    let text = tokio::task::spawn_blocking(move || {
        gate.begin_message(RunKind::Sdk, /*joins*/ false, &message)
    })
    .await??;
    let submission = conversation
        .submit(InputSubmissionDraft::new(text), cx)
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

/// The ledger of `conversation`'s steps a restart could not tell the
/// outcome of and treated as not run, oldest first, corrected or not.
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

/// Correct `conversation`'s uncorrected entry `id` as `resolution`: the
/// entry as corrected, or `None` when the ledger holds no uncorrected
/// entry of that id (never noted, or corrected already).
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

/// Which runs of a session [`set_budget`] limits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BudgetScope {
    /// As `/budget set`: the limits of the running run, or, while the
    /// session runs nothing, of its next run only (a `/b` pair of that
    /// prompt going over them). Limits set for the next run are in the
    /// budget's ledger before [`set_budget`] answers: a session opened
    /// again after a crash still starts its next run with them.
    Run,
    /// The session's standing limits, as a create's `budget` config: every
    /// run's from now on, the running run's included.
    Standing,
}

/// Set the limits of `session`'s runs that `scope` names (each prompt is
/// a run): a dimension `limits` leaves unset fills as the session's runs
/// do (`budget.limits` off: unlimited, until finished). Answers the
/// budget's state; limits for the next run show in its `next`.
///
/// # Errors
///
/// The session draws from another session's budget (the [`BudgetError`]
/// `NotRoot`), a `budget.*` setting is no limit, the session's live state
/// does not read, or the ledger cannot be written.
pub async fn set_budget(
    session: &EukheSession,
    limits: impl Into<RunLimits>,
    scope: BudgetScope,
    cx: &Context,
) -> anyhow::Result<BudgetReport> {
    let gate = session.budget();
    let limits = limits.into();
    let target = match scope {
        BudgetScope::Standing => Target::Standing,
        BudgetScope::Run => match main_run(session, cx).await? {
            MainRun::Live => Target::Run,
            MainRun::Idle => Target::Next,
        },
    };
    tokio::task::spawn_blocking(move || -> anyhow::Result<BudgetReport> {
        Ok(match target {
            Target::Standing => gate.set_standing(limits)?,
            Target::Run => gate.set(limits)?,
            Target::Next => gate.set_next(limits)?,
        })
    })
    .await?
}

/// Whether a run is live on a session's main conversation.
#[derive(Clone, Copy)]
enum MainRun {
    Live,
    Idle,
}

/// The limits [`set_budget`] sets: the standing ones, the running run's, or
/// the next run's.
#[derive(Clone, Copy)]
enum Target {
    Standing,
    Run,
    Next,
}

/// Whether a run is live on `session`'s main conversation (its `pi.live`
/// document's run): limits set meanwhile are that run's.
async fn main_run(session: &EukheSession, cx: &Context) -> anyhow::Result<MainRun> {
    Ok(
        match session
            .harness()
            .snapshot(&LIVE_DOC, session.main().id(), cx)
            .await?
        {
            Some(value) => match from_json::<LiveState>(&JsonValue::Object(value))?.run {
                Some(_) => MainRun::Live,
                None => MainRun::Idle,
            },
            None => MainRun::Idle,
        },
    )
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

/// Follow `session`'s plan notices: a plan window's last reading passed
/// `100 - budget.planReserve` percent used while limits are off (once per
/// window until a reading below the line). The run continues.
#[must_use]
pub fn watch_plan_notices(session: &EukheSession) -> tokio::sync::broadcast::Receiver<PlanNotice> {
    session.budget().plan_notices()
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
