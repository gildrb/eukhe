//! Irreversible effects that ran (spec I4-I6): each one goes to its root
//! session's ledger (`eukhe_durable::harness::effects`), and each root
//! run's end hands its report to the session's [`RunReportSink`].
//!
//! - Recording ([`record_effects`]): a root records in its main
//!   conversation's ledger, in the commit that also numbers the run in
//!   flight when the ledger has not numbered it yet ([`record_in`]; an
//!   effect while no root run is live goes to the next run's report); a
//!   subagent hands each effect to its parent through the session's
//!   [`RanEffectRelay`] (the daemon's `relay_ran_effect`), up to the root.
//!   The tool that caused an effect tells the model its id
//!   ([`tool_notes`]); a `bash` step is recorded at its own end.
//! - Runs ([`install`], a root's service on main's commits): a run that
//!   starts is numbered once, keyed by its first input ([`run_key`]), so
//!   a run a restart takes up again numbers nothing new; a run that ended
//!   hands its report (the effects that ran in it and the steps it
//!   treated as not run) to the sink, never an empty one.
//! - MCP calls: the kernel's `effects.ran` host request
//!   ([`register_host_requests`]) records a call of an MCP tool its server
//!   does not declare read-only (class unknown); the cell prints its note.

use std::sync::{Arc, Weak};

use anyhow::Context as _;
use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_chord::json::{from_json, JsonValue};
use eukhe_durable::harness::effects::{
    begin_run, effects_state, read_effects_state, record_ran, run_report, EffectsState,
};
use eukhe_durable::harness::{Harness, LiveState, LIVE_DOC};
use eukhe_durable::session::{SessionResult, Tx};
use eukhe_durable::types::{CommitChange, CommitPublication, ConversationId, DocumentCommitChange};
use eukhe_types::effects::{EffectClass, RanEffect, RanEffectDraft, RanKind, RunReport};
use futures::future::BoxFuture;
use futures::FutureExt;
use serde_json::Value;

use super::{HostCall, HostDeps, OpenedSession, ServiceStop};

/// Hands one irreversible effect a subagent session ran to its parent,
/// which records it in its ledger when it is the root and else hands it
/// on; answers the effect as the root recorded it. The daemon worker of a
/// child session sets it (`relay_ran_effect` over its supervisor link);
/// `None`: the session is a root and records in its own ledger.
pub type RanEffectRelay =
    Arc<dyn Fn(RanEffectDraft) -> BoxFuture<'static, SessionResult<RanEffect>> + Send + Sync>;

/// Receives the report of each root run that ended with something to
/// report (spec I6): the daemon sends it as `run_report` after the run's
/// `agent_end`; a headless run prints it. Called from the session's run
/// service, once per run.
pub type RunReportSink = Arc<dyn Fn(RunReport) + Send + Sync>;

/// The ledger key of the root run `live` holds: its first input; `None`
/// while no run is live.
#[must_use]
pub fn run_key(live: &LiveState) -> Option<String> {
    let run = live.run.as_ref()?;
    run.inputs.first().map(|input| format!("in{input}"))
}

/// Record `draft` in the ledger of `conversation_id` in the commit `tx`,
/// in the run live in that conversation, numbered first when the ledger
/// has not numbered it yet (an effect can land before the run service
/// sees its run start). While no run is live (a subagent's effect while
/// its root is idle) it goes to the root's next run: that run's report
/// lists it.
///
/// # Errors
///
/// Document access or draft failures, or the ledger's core call failed.
pub async fn record_in(
    tx: &Tx,
    conversation_id: ConversationId,
    draft: RanEffectDraft,
) -> SessionResult<RanEffect> {
    let live = tx.doc(&LIVE_DOC, conversation_id).await?;
    let live: LiveState = from_json(&live.value()?)?;
    let run = match run_key(&live) {
        Some(key) => begin_run(tx, conversation_id, &key).await?,
        None => effects_state(tx, conversation_id).await?.run + 1,
    };
    record_ran(tx, conversation_id, draft, run).await
}

/// Record `draft` in the ledger of `conversation_id` in a commit of its
/// own (a root's effect, or a subagent's its relay brought up).
///
/// # Errors
///
/// The commit failed (see [`record_in`]).
pub async fn record_on(
    harness: &Harness,
    conversation_id: ConversationId,
    draft: RanEffectDraft,
    cx: &Context,
) -> SessionResult<RanEffect> {
    harness
        .commit(
            move |tx| async move { record_in(&tx, conversation_id, draft).await },
            cx,
        )
        .await
}

/// The draft of an irreversible effect the session `deps` ran: `key`
/// names it within the session (`<call>:<step>`).
pub(crate) fn draft(
    deps: &HostDeps,
    key: &str,
    kind: RanKind,
    command: String,
    classes: Vec<EffectClass>,
) -> RanEffectDraft {
    let at_ms = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |since| {
            u64::try_from(since.as_millis()).unwrap_or(u64::MAX)
        });
    RanEffectDraft {
        key: format!("{}:{key}", deps.session_id),
        kind,
        command,
        classes,
        agent: None,
        session_id: deps.session_id.clone(),
        at_ms,
    }
}

/// Record `drafts`, the irreversible effects a call in `conversation_id`
/// ran, in order: in the root's ledger (through the relay in a subagent).
/// The effects as recorded; one that could not be recorded is logged and
/// left out (it ran: the call's result stands).
pub(crate) async fn record_effects(
    deps: &HostDeps,
    conversation_id: ConversationId,
    drafts: Vec<RanEffectDraft>,
) -> Vec<RanEffect> {
    let mut recorded = Vec::with_capacity(drafts.len());
    for draft in drafts {
        let key = draft.key.clone();
        let effect = match (&deps.ran_effect_relay, deps.harness.get()) {
            (Some(relay), _) => relay(draft).await,
            (None, Some(harness)) => {
                record_on(&harness, conversation_id, draft, &BACKGROUND_CONTEXT).await
            }
            (None, None) => Err(eukhe_durable::session::SessionError::error(
                "Harness is closed",
            )),
        };
        match effect {
            Ok(effect) => recorded.push(effect),
            Err(error) => {
                tracing::warn!(%error, key, "an irreversible effect that ran was not recorded");
            }
        }
    }
    recorded
}

/// What the model reads after the output of the call that ran
/// `recorded`: one [`RanEffect::tool_note`] per line; empty for none.
pub(crate) fn tool_notes(recorded: &[RanEffect]) -> String {
    recorded
        .iter()
        .map(RanEffect::tool_note)
        .collect::<Vec<_>>()
        .join("\n")
}

/// The kernel host request that records an MCP call.
const MCP_RAN_REQUEST: &str = "effects.ran";

/// Register the kernel's [`MCP_RAN_REQUEST`]: `{"kind": "mcpCall",
/// "command": "mcp <server>.<tool>"}`, sent after a call of an MCP tool
/// its server does not declare read-only. The reply is `{"effect":
/// <RanEffect>, "note": "[irreversible: …]"}`.
pub(crate) fn register_host_requests(deps: &Arc<HostDeps>) {
    let weak = Arc::downgrade(deps);
    deps.host_requests.register(
        MCP_RAN_REQUEST,
        Arc::new(move |call: HostCall| mcp_call_ran(weak.clone(), call).boxed()),
    );
}

async fn mcp_call_ran(deps: Weak<HostDeps>, call: HostCall) -> anyhow::Result<Value> {
    let deps = deps.upgrade().context("the session closed")?;
    anyhow::ensure!(
        call.data.get("kind").and_then(Value::as_str) == Some("mcpCall"),
        "{MCP_RAN_REQUEST} records only an MCP call (kind \"mcpCall\")"
    );
    let command = call
        .data
        .get("command")
        .and_then(Value::as_str)
        .filter(|command| !command.is_empty())
        .with_context(|| format!("{MCP_RAN_REQUEST} needs a command"))?;
    let unique = uuid::Uuid::new_v4().simple();
    let (key, conversation) = match &call.call {
        Some(api) => (
            format!("{}:mcp-{unique}", api.call_id()),
            Some(api.conversation_id()),
        ),
        None => (
            format!("kernel:mcp-{unique}"),
            deps.harness.root().map(|root| root.id()),
        ),
    };
    let conversation = conversation.context("the session closed")?;
    let draft = draft(
        &deps,
        &key,
        RanKind::McpCall,
        command.to_owned(),
        vec![EffectClass::Unknown],
    );
    let effect = record_effects(&deps, conversation, vec![draft])
        .await
        .into_iter()
        .next()
        .context("the MCP call was not recorded")?;
    Ok(serde_json::json!({ "note": effect.tool_note(), "effect": effect }))
}

/// Start the run service of a root session (one that records in its own
/// ledger) when it opens.
pub(crate) fn install(deps: &Arc<HostDeps>) {
    if deps.ran_effect_relay.is_some() {
        return;
    }
    let sink = deps.run_report.clone();
    deps.add_service(Box::new(move |opened| start(opened, sink)));
}

/// Whether `publication` changed `conversation_id`'s live run state or
/// its ledger.
fn changes_runs(publication: &CommitPublication, conversation_id: ConversationId) -> bool {
    let live = LIVE_DOC.definition().kind;
    let ledger = eukhe_durable::harness::effects::EFFECTS_DOC
        .definition()
        .kind;
    publication.changes.iter().any(|change| match change {
        CommitChange::Document(DocumentCommitChange::Document {
            record,
            conversation_id: owner,
            ..
        }) => (record.kind == live || record.kind == ledger) && *owner == Some(conversation_id),
        CommitChange::Document(DocumentCommitChange::Copy { .. })
        | CommitChange::Conversation(_)
        | CommitChange::Entry(_)
        | CommitChange::Task(_)
        | CommitChange::Submission(_) => false,
    })
}

/// The runs the service follows: the one live as last seen, with its
/// number, and the key of the last run it reported (or found ended).
struct Runs {
    harness: Harness,
    main: ConversationId,
    sink: Option<RunReportSink>,
    live: Option<(String, u64)>,
    reported: Option<String>,
}

impl Runs {
    /// Read the live run and the ledger: a run seen live that is no
    /// longer, or one the ledger numbered that started and ended unseen,
    /// reports; a live run the ledger has not numbered is numbered.
    async fn step(&mut self, cx: &Context) -> SessionResult<()> {
        let live = match self.harness.snapshot(&LIVE_DOC, self.main, cx).await? {
            Some(live) => from_json::<LiveState>(&JsonValue::Object(live))?,
            None => LiveState::default(),
        };
        let key = run_key(&live);
        let state = read_effects_state(&self.harness, self.main, cx).await?;
        if let Some((seen, run)) = self.live.take() {
            if key.as_deref() == Some(seen.as_str()) {
                self.live = Some((seen, run));
            } else {
                self.report(&state, seen, run)?;
            }
        }
        if self.live.is_none() {
            if let Some(numbered) = state.run_key.clone() {
                if key.as_deref() != Some(numbered.as_str())
                    && self.reported.as_deref() != Some(numbered.as_str())
                {
                    self.report(&state, numbered, state.run)?;
                }
            }
        }
        if let (None, Some(key)) = (&self.live, key) {
            let run = if state.run_key.as_deref() == Some(key.as_str()) {
                state.run
            } else {
                let main = self.main;
                let begun = key.clone();
                self.harness
                    .commit(
                        move |tx| async move { begin_run(&tx, main, &begun).await },
                        cx,
                    )
                    .await?
            };
            self.live = Some((key, run));
        }
        Ok(())
    }

    /// The run `key` (number `run`) ended: its report goes to the sink
    /// unless it is empty.
    fn report(&mut self, state: &EffectsState, key: String, run: u64) -> SessionResult<()> {
        self.reported = Some(key);
        let report = run_report(state, run)?;
        if let (Some(sink), false) = (
            &self.sink,
            report.ran.is_empty() && report.unknown.is_empty(),
        ) {
            sink(report);
        }
        Ok(())
    }
}

/// What the run service's queue carries: a commit that may have moved a
/// run, or a barrier answered once every earlier entry was read.
enum Tick {
    Commit,
    Barrier(tokio::sync::oneshot::Sender<()>),
}

fn start(
    opened: OpenedSession,
    sink: Option<RunReportSink>,
) -> BoxFuture<'static, SessionResult<Option<ServiceStop>>> {
    async move {
        let main = opened.main.id();
        let harness = opened.harness.clone();
        let cx = BACKGROUND_CONTEXT.clone();
        // The run ended before this open was reported then (or lost with
        // the process that saw it end).
        let reported = read_effects_state(&harness, main, &cx).await?.run_key;
        let mut runs = Runs {
            harness: harness.clone(),
            main,
            sink,
            live: None,
            reported,
        };
        // Before scheduling resumes: a run taken up again keeps its number.
        runs.step(&cx).await?;
        let (ticks, mut ticked) = tokio::sync::mpsc::unbounded_channel::<Tick>();
        let barriers = ticks.clone();
        let barrier: super::deps::ObserverBarrier = Arc::new(move || {
            let (answer, answered) = tokio::sync::oneshot::channel();
            let queued = barriers.send(Tick::Barrier(answer)).is_ok();
            async move {
                if queued {
                    // A stopped service answers nothing more: nothing
                    // is left to report.
                    let _ = answered.await;
                }
            }
            .boxed()
        });
        // One service per session: a second open of the same deps keeps
        // the first barrier.
        let _ = opened.deps.runs_barrier.set(barrier);
        let commits = harness.subscribe_commits(Arc::new(
            move |publication: &CommitPublication, _cx: &Context| {
                if changes_runs(publication, main) {
                    let _ = ticks.send(Tick::Commit);
                }
            },
        ))?;
        let close = Arc::new(tokio::sync::Notify::new());
        let closing = Arc::clone(&close);
        let task = tokio::spawn(async move {
            loop {
                let tick = tokio::select! {
                    tick = ticked.recv() => tick,
                    () = closing.notified() => None,
                };
                let Some(tick) = tick else { break };
                // A burst of commits is one read; the barriers in it are
                // answered after that read.
                let mut answers: Vec<_> = match tick {
                    Tick::Commit => Vec::new(),
                    Tick::Barrier(answer) => vec![answer],
                };
                while let Ok(more) = ticked.try_recv() {
                    match more {
                        Tick::Commit => {}
                        Tick::Barrier(answer) => answers.push(answer),
                    }
                }
                if let Err(error) = runs.step(&cx).await {
                    tracing::warn!(%error, "the run service could not read the runs");
                }
                for answer in answers {
                    let _ = answer.send(());
                }
            }
            // The last commits before the close: a run that ended just
            // before it still reports.
            if let Err(error) = runs.step(&cx).await {
                tracing::warn!(%error, "the run service could not read the runs at close");
            }
        });
        let stop: ServiceStop = Box::new(move || {
            async move {
                drop(commits);
                close.notify_one();
                let _ = task.await;
            }
            .boxed()
        });
        Ok(Some(stop))
    }
    .boxed()
}
