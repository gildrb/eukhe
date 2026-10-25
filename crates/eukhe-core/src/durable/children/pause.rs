//! The pause of a worker tree inside one session's run (docs/usage.md,
//! main and worker): `pause_workers` / `resume_workers` with `ownRun`
//! pause or resume this session's own run. Every rule is the compiled
//! core's pause model (`eukhe_bend::rules::worker::pause_step`, entry 430,
//! laws `laws/worker.bend`); this module only feeds it the run's events
//! and waits where it says `Hold`:
//!
//! - the next model request (after a tool round, before the boundary that
//!   places the queued inputs, and before every request attempt), the next
//!   model-issued tool call and the next spawn ask at a gate; while paused
//!   they hold there. The current model request and the current tool calls
//!   finish: nothing is cancelled.
//! - a message that reaches the session while it is paused is kept: it
//!   waits in the durable inbox, unplaced, because the boundary that would
//!   place it holds. A user's message or main's forward wakes the run (a
//!   resume does too); the held boundary then places every kept message in
//!   arrival order, once, and the run goes on where it parked with its
//!   whole context.
//!
//! The pause state (mode, the held boundary, the kept messages) is the
//! durable session document `eukhe.pause`, so a restarted worker stays
//! paused; the count of tool calls in flight is this process's own.

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use eukhe_bend::rules::worker::{
    pause_step, GateKind, PauseEvent, PauseMode, PauseState, PauseVerdict,
};
use eukhe_chord::context::{await_with_context, Context, BACKGROUND_CONTEXT};
use eukhe_chord::json::{from_json, to_json, JsonValue};
use eukhe_durable::documents::{DocDefinition, SessionDoc};
use eukhe_durable::harness::types::{GenerationHooks, HookRegistration, ToolHooks};
use eukhe_durable::harness::{GENERATION_TASK, TOOL_TASK};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::DocumentReaderExt;
use futures::FutureExt;
use serde::{Deserialize, Serialize};
use tokio::sync::{watch, Mutex};

use super::host::PauseAction;
use crate::durable::deps::HarnessCell;
use eukhe_durable::harness::define::hook;

#[cfg(test)]
mod tests;

/// The durable part of the pause state (`eukhe.pause`).
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
struct PauseDoc {
    #[serde(default)]
    paused: bool,
    /// The boundary held while paused.
    #[serde(default)]
    parked: Option<u64>,
    /// The messages kept while paused, in arrival order.
    #[serde(default)]
    kept: Vec<u64>,
}

impl PauseDoc {
    fn of(state: &PauseState) -> Self {
        Self {
            paused: state.mode == PauseMode::Paused,
            parked: state.parked,
            kept: state.kept.clone(),
        }
    }

    /// The state this document holds, with no tool call in flight (a new
    /// process runs none yet).
    fn state(&self) -> PauseState {
        PauseState {
            mode: if self.paused {
                PauseMode::Paused
            } else {
                PauseMode::Run
            },
            parked: self.parked,
            kept: self.kept.clone(),
            inflight: 0,
        }
    }
}

static PAUSE_DOC: SessionDoc<PauseDoc> = match SessionDoc::define(DocDefinition {
    kind: "eukhe.pause",
    version: 1,
    initial: PauseDoc::default,
    migrate: None,
    checkpoint_when: None,
}) {
    Ok(token) => token,
    Err(_) => panic!("eukhe.pause has a valid version"),
};

/// What the host shows of a session's pause.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct PauseView {
    /// The session's run is paused (its summary's `isPaused`).
    pub paused: bool,
    /// The run waits at a held boundary with no tool call in flight: it
    /// counts as idle for the kernel release.
    pub held: bool,
}

impl PauseView {
    fn of(state: &PauseState) -> Self {
        let paused = state.mode == PauseMode::Paused;
        Self {
            paused,
            held: paused && state.parked.is_some() && state.inflight == 0,
        }
    }
}

/// What a message that reaches the session does to a paused run.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Wake {
    /// A user's message or main's forward: it wakes the run.
    Wakes,
    /// A report or an agent's note: it waits until the run goes on.
    Waits,
}

/// The pause of one session's run: the state the compiled core steps, kept
/// in `eukhe.pause`, and the watch the held boundaries wait on.
pub struct RunPause {
    harness: HarnessCell,
    /// The state (loaded from `eukhe.pause` at the first event); one event
    /// steps it at a time.
    state: Mutex<Option<PauseState>>,
    /// Names each boundary and message.
    next_id: AtomicU64,
    view: watch::Sender<PauseView>,
}

impl RunPause {
    pub(crate) fn new(harness: HarnessCell) -> Self {
        Self {
            harness,
            state: Mutex::new(None),
            next_id: AtomicU64::new(0),
            view: watch::Sender::new(PauseView::default()),
        }
    }

    /// The pause as the host shows it, now and on every change.
    #[must_use]
    pub fn subscribe(&self) -> watch::Receiver<PauseView> {
        self.view.subscribe()
    }

    /// Whether the run is paused now.
    #[must_use]
    pub fn view(&self) -> PauseView {
        *self.view.borrow()
    }

    fn next_id(&self) -> u64 {
        self.next_id.fetch_add(1, Ordering::Relaxed) + 1
    }

    /// Step the pause model with `event`; the durable part commits when it
    /// changed. Before the session opens nothing was paused: the state is
    /// the default and stays unread until the Harness is there.
    async fn step(&self, event: PauseEvent, cx: &Context) -> SessionResult<PauseVerdict> {
        let mut slot = self.state.lock().await;
        let current = match (slot.as_ref(), self.harness.get()) {
            (Some(state), _) => state.clone(),
            (None, None) => PauseState::default(),
            (None, Some(harness)) => match harness.snapshot(&PAUSE_DOC, (), cx).await? {
                None => PauseState::default(),
                Some(value) => from_json::<PauseDoc>(&JsonValue::Object(value))?.state(),
            },
        };
        let (next, verdict) = pause_step(&current, event)
            .map_err(|error| SessionError::error(format!("{error:#}")))?;
        let doc = PauseDoc::of(&next);
        if doc != PauseDoc::of(&current) {
            let root = self
                .harness
                .root()
                .ok_or_else(|| SessionError::error("Harness is closed"))?;
            root.commit(
                move |tx| async move {
                    let draft = tx.doc(&PAUSE_DOC, ()).await?;
                    draft.set("paused", to_json(&doc.paused)?)?;
                    draft.set("parked", to_json(&doc.parked)?)?;
                    draft.set("kept", to_json(&doc.kept)?)?;
                    Ok(())
                },
                cx,
            )
            .await?;
        }
        let view = PauseView::of(&next);
        if self.harness.get().is_some() {
            *slot = Some(next);
        }
        self.view.send_if_modified(|shown| {
            let changed = *shown != view;
            *shown = view;
            changed
        });
        Ok(verdict)
    }

    /// Pause or resume this session's own run.
    ///
    /// # Errors
    ///
    /// The pause state cannot be read or committed.
    pub async fn set(&self, action: PauseAction, cx: &Context) -> SessionResult<()> {
        let event = match action {
            PauseAction::Pause => PauseEvent::Pause,
            PauseAction::Resume => PauseEvent::Resume,
        };
        self.step(event, cx).await.map(drop)
    }

    /// A message reached the session (after it was queued): one that
    /// [`Wake::Wakes`] wakes a paused run; one that [`Wake::Waits`] is kept
    /// until the run goes on.
    ///
    /// # Errors
    ///
    /// The pause state cannot be read or committed.
    pub async fn message(&self, wake: Wake, cx: &Context) -> SessionResult<()> {
        let id = self.next_id();
        let wakes = wake == Wake::Wakes;
        self.step(PauseEvent::Msg { id, wakes }, cx).await.map(drop)
    }

    /// The run is about to start a boundary of `kind`: returns when it may
    /// start; while the run is paused, waits for a resume or a waking
    /// message. An abort of the run ends the wait (and the run).
    ///
    /// # Errors
    ///
    /// The run was aborted while it waited, or the pause state cannot be
    /// read or committed.
    pub(crate) async fn gate(&self, kind: GateKind, cx: &Context) -> SessionResult<()> {
        let mut shown = self.subscribe();
        loop {
            let id = self.next_id();
            match self.step(PauseEvent::Gate { kind, id }, cx).await? {
                PauseVerdict::Go => return Ok(()),
                PauseVerdict::Hold => {
                    let resumed = async { shown.wait_for(|view| !view.paused).await.map(drop) };
                    let waited = await_with_context(resumed, cx).await;
                    match waited {
                        Ok(Ok(())) => {}
                        Ok(Err(_closed)) => {
                            return Err(SessionError::error("The run pause was dropped"))
                        }
                        Err(reason) => {
                            // The aborted run ends here: nothing stays held.
                            self.step(PauseEvent::End, &BACKGROUND_CONTEXT).await?;
                            return Err(SessionError::Aborted(reason));
                        }
                    }
                }
                verdict @ (PauseVerdict::Release(_)
                | PauseVerdict::Kept
                | PauseVerdict::Pass
                | PauseVerdict::Ack) => {
                    return Err(SessionError::error(format!(
                        "The pause model answered {verdict:?} at a gate"
                    )))
                }
            }
        }
    }

    /// A model-issued tool call that started ended.
    async fn tool_done(&self, cx: &Context) -> SessionResult<()> {
        self.step(PauseEvent::Done, cx).await.map(drop)
    }

    /// The run ended.
    async fn end(&self, cx: &Context) -> SessionResult<()> {
        self.step(PauseEvent::End, cx).await.map(drop)
    }
}

/// The hooks that hold a paused run: the next model request (after a tool
/// round, before its boundary; before every request attempt), the next
/// model-issued tool call, and the run's end.
pub(super) fn pause_hooks(pause: &Arc<RunPause>) -> Vec<HookRegistration> {
    let (after_tools, before_request, on_yield) =
        (Arc::clone(pause), Arc::clone(pause), Arc::clone(pause));
    let (before_tool, after_tool) = (Arc::clone(pause), Arc::clone(pause));
    vec![
        hook(
            &*GENERATION_TASK,
            GenerationHooks {
                after_tools: Some(Arc::new(move |_, _, _, cx| {
                    let (pause, cx) = (Arc::clone(&after_tools), cx.clone());
                    async move { pause.gate(GateKind::Request, &cx).await }.boxed()
                })),
                before_request: Some(Arc::new(move |_, _, cx| {
                    let (pause, cx) = (Arc::clone(&before_request), cx.clone());
                    async move {
                        pause.gate(GateKind::Request, &cx).await?;
                        Ok(None)
                    }
                    .boxed()
                })),
                on_yield: Some(Arc::new(move |_, _, cx| {
                    let (pause, cx) = (Arc::clone(&on_yield), cx.clone());
                    async move {
                        pause.end(&cx).await?;
                        Ok(None)
                    }
                    .boxed()
                })),
                ..GenerationHooks::default()
            },
        ),
        hook(
            &*TOOL_TASK,
            ToolHooks {
                // A nested call runs inside a call that already started:
                // holding it would hold that call. Only the model's calls
                // ask.
                before_tool: Some(Arc::new(move |call, _, cx| {
                    let (pause, cx, nested) =
                        (Arc::clone(&before_tool), cx.clone(), call.parent.is_some());
                    async move {
                        if !nested {
                            pause.gate(GateKind::Tool, &cx).await?;
                        }
                        Ok(None)
                    }
                    .boxed()
                })),
                after_tool: Some(Arc::new(move |call, _, _, cx| {
                    let (pause, cx, nested) =
                        (Arc::clone(&after_tool), cx.clone(), call.parent.is_some());
                    async move {
                        if !nested {
                            pause.tool_done(&cx).await?;
                        }
                        Ok(None)
                    }
                    .boxed()
                })),
            },
        ),
    ]
}
