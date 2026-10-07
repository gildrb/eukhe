//! The in-process RPC connection: one live durable session slot, the
//! connection outputs (the prompt-response buffer in front of the ordered
//! writer), the event pump over the session's main conversation, and the
//! whole-session replacement `new_session` / `switch_session` / `fork`
//! drive (TS `InProcessAgentConnection` + the runtime host's session
//! replacement flows).

use std::future::Future;
use std::path::PathBuf;
use std::pin::Pin;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_core::durable::goals::goal_state;
use eukhe_core::durable::{EukheSession, TurnWait, TurnWaitSink};
use eukhe_core::goals::GoalState;
use eukhe_durable::harness::types::ConversationAbortOptions;
use eukhe_types::daemon::ChatTurnWaitEvent;
use serde_json::Value;
use tokio_util::sync::CancellationToken;

use super::event_pump::EventPump;
use super::reads::{is_busy, rpc_context};
use super::LineWriter;

/// The refusal every replacement answers once a signal exit began.
const SIGNAL_EXIT_IN_PROGRESS: &str = "A signal exit is in progress";

/// One opened durable session plus the runtime session lease the factory
/// acquired for its storage directory (dropped with the handle on
/// replacement — the old session's lease releases exactly when the
/// session that owned it closed).
pub struct RpcEngineHandle {
    pub session: Arc<EukheSession>,
    /// The cross-process ownership lease on the storage directory (`None`
    /// for in-memory sessions).
    pub session_lease: Option<crate::lease::SessionLease>,
}

/// What the factory opens (TS `createRuntime` at startup, and the runtime
/// host's `newSession` / `switchSession` / `fork` replacements).
pub enum RpcEngineRequest {
    /// The session the CLI flags select (`--session`, `--continue`,
    /// `--no-session`, ...).
    Startup,
    /// A fresh session. (Durable storage has no session header, so the
    /// TS `parentSession` lineage has no record to land in.)
    New {
        /// The ACTIVE session's cwd (TS `runtimeHost.newSession` builds
        /// the fresh session over `this.cwd` — the live runtime's
        /// project, not the CLI startup directory): the factory falls
        /// back to the startup cwd when absent.
        cwd: Option<PathBuf>,
    },
    /// An existing session: a durable storage directory or a legacy
    /// `.jsonl` file (imported on open).
    Open {
        session_path: PathBuf,
        /// The same-path reopen: the caller adopted the current lease
        /// (TS `acquireReplacementLease` reuses it), so the factory must
        /// not re-acquire (its own open guard would refuse our own
        /// holder).
        reuse_lease: bool,
    },
}

/// The composition root's session assembly. The RPC mode never opens a
/// session itself — eukhe-cli owns the assembly (cwd, model resolution,
/// auth), exactly like the TS runtime host owns `createRuntime`. The sink
/// is the connection's chat turn-wait seam: the factory installs it as the
/// opened session's `SessionConfig::turn_wait`, so the session's
/// `chat_turn_wait` frames reach this connection.
pub type RpcEngineFactory = Arc<
    dyn Fn(
            RpcEngineRequest,
            TurnWaitSink,
        ) -> Pin<Box<dyn Future<Output = Result<RpcEngineHandle, String>> + Send>>
        + Send
        + Sync,
>;

/// The connection outputs: frames published while a prompt response is
/// pending buffer (TS `bufferedConnectionOutputs`) and flush right after
/// the response; otherwise they go straight to the ordered writer.
#[derive(Clone)]
pub(crate) struct ConnectionOutputs {
    /// `Some` while a prompt response is pending.
    buffer: Arc<Mutex<Option<Vec<Value>>>>,
    writer: LineWriter,
}

impl ConnectionOutputs {
    pub(crate) fn new(writer: LineWriter) -> Self {
        Self {
            buffer: Arc::new(Mutex::new(None)),
            writer,
        }
    }

    fn buffer(&self) -> std::sync::MutexGuard<'_, Option<Vec<Value>>> {
        self.buffer.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Arm the prompt-response buffer (TS `promptResponsePending = true`).
    pub(crate) fn arm(&self) {
        let mut buffer = self.buffer();
        if buffer.is_none() {
            *buffer = Some(Vec::new());
        }
    }

    /// The prompt response was written: disarm the buffer and emit its
    /// frames in order (TS `promptResponsePending = false` +
    /// `flushConnectionEvents`, one step under the buffer lock so no frame
    /// can slip ahead of the buffered ones).
    pub(crate) fn flush(&self) {
        let mut buffer = self.buffer();
        for frame in buffer.take().unwrap_or_default() {
            self.writer.write(frame);
        }
    }

    /// Publish one frame.
    pub(crate) fn write(&self, frame: Value) {
        self.write_all(vec![frame]);
    }

    /// Publish frames in order.
    pub(crate) fn write_all(&self, frames: Vec<Value>) {
        if frames.is_empty() {
            return;
        }
        let mut buffer = self.buffer();
        match buffer.as_mut() {
            Some(buffered) => buffered.extend(frames),
            None => {
                for frame in frames {
                    self.writer.write(frame);
                }
            }
        }
    }

    /// The chat turn-wait sink publishing `chat_turn_wait` frames.
    pub(crate) fn turn_wait_sink(&self) -> TurnWaitSink {
        let outputs = self.clone();
        Arc::new(move |wait: TurnWait| {
            let event = ChatTurnWaitEvent {
                waiting: matches!(wait, TurnWait::Waiting),
            };
            outputs.write(serde_json::json!(event));
        })
    }
}

/// The live session state one RPC connection drives.
pub struct RpcSession {
    handle: tokio::sync::RwLock<RpcEngineHandle>,
    outputs: ConnectionOutputs,
    factory: RpcEngineFactory,
    pump: tokio::sync::Mutex<Option<EventPump>>,
    /// The last published `goal_update` goal (change-gated emits across
    /// pumps and replacements).
    last_goal: Arc<Mutex<GoalState>>,
    /// One replacement at a time (TS `acquireReplacementLease`): a fork
    /// racing a `switch_session` must not interleave.
    replacement: tokio::sync::Mutex<()>,
    /// Fired when a signal exit (SIGTERM/SIGHUP) begins: an in-flight
    /// replacement stops waiting the running turn out (it refuses), and
    /// later replacements answer immediately, so the 143/129 exit never
    /// queues behind a replacement's settle.
    signal_shutdown: CancellationToken,
}

impl RpcSession {
    /// Open the startup session through the factory and attach its pump.
    ///
    /// # Errors
    ///
    /// The factory's assembly error, or the pump cannot attach.
    pub(crate) async fn start(
        factory: RpcEngineFactory,
        outputs: ConnectionOutputs,
    ) -> Result<Self, String> {
        let handle = factory(RpcEngineRequest::Startup, outputs.turn_wait_sink()).await?;
        let cx = rpc_context();
        let initial_goal = goal_state(handle.session.harness(), handle.session.main().id(), &cx)
            .await
            .map_err(|error| error.to_string())?;
        let last_goal = Arc::new(Mutex::new(initial_goal));
        let pump = EventPump::attach(&handle.session, &outputs, &last_goal, &cx)
            .await
            .map_err(|error| error.to_string())?;
        Ok(Self {
            handle: tokio::sync::RwLock::new(handle),
            outputs,
            factory,
            pump: tokio::sync::Mutex::new(Some(pump)),
            last_goal,
            replacement: tokio::sync::Mutex::new(()),
            signal_shutdown: CancellationToken::new(),
        })
    }

    /// The current session handle. Holding the guard keeps a replacement
    /// (which swaps under the write guard) from closing the session under
    /// the holder.
    pub async fn handle(&self) -> tokio::sync::RwLockReadGuard<'_, RpcEngineHandle> {
        self.handle.read().await
    }

    /// The current session.
    pub async fn session(&self) -> Arc<EukheSession> {
        Arc::clone(&self.handle.read().await.session)
    }

    /// The connection outputs.
    pub(crate) fn outputs(&self) -> &ConnectionOutputs {
        &self.outputs
    }

    /// Re-attach the pump to the current session's main conversation
    /// after the main conversation moved in place (an in-memory fork).
    ///
    /// # Errors
    ///
    /// The pump cannot attach.
    pub(crate) async fn reattach_pump(&self, session: &EukheSession) -> Result<(), String> {
        let pump = EventPump::attach(session, &self.outputs, &self.last_goal, &rpc_context())
            .await
            .map_err(|error| error.to_string())?;
        let previous = self.pump.lock().await.replace(pump);
        if let Some(previous) = previous {
            previous.stop().await;
        }
        Ok(())
    }

    /// Acquire the whole-session replacement lease (TS
    /// `acquireReplacementLease`): one replacement flow at a time. The
    /// fork path holds it across its read/fork/swap so a concurrent
    /// `new_session`/`switch_session` cannot interleave between them.
    pub async fn replacement_lease(&self) -> tokio::sync::MutexGuard<'_, ()> {
        self.replacement.lock().await
    }

    /// Begin the signal exit (SIGTERM/SIGHUP): any in-flight
    /// replacement's settle gives way and later replacements refuse.
    pub fn fire_shutdown(&self) {
        self.signal_shutdown.cancel();
    }

    /// Whole-session replacement with the lease already held by the
    /// caller (`replacement_lease` / `replace` acquire it): settle the
    /// running turn, build the replacement through the factory, abort
    /// whatever the old session started meanwhile, attach the new pump,
    /// close the old session, and swap the slot. A failed build leaves
    /// the live session serving.
    ///
    /// # Errors
    ///
    /// The factory's assembly error, a signal exit in progress, or the
    /// replacement's pump cannot attach.
    pub async fn replace_locked(&self, request: RpcEngineRequest) -> Result<(), String> {
        if self.signal_shutdown.is_cancelled() {
            return Err(SIGNAL_EXIT_IN_PROGRESS.to_string());
        }
        let cx = rpc_context();
        let mut request = request;
        // Settle the running turn BEFORE the factory opens anything: the
        // turn's final entries land in the storage a same-session reopen
        // or a fork reads, and its terminal frames still stream (the old
        // pump stays attached until the swap). The settle runs WITHOUT
        // the write guard, so an RPC `abort` arriving mid-settle reaches
        // the session instead of queueing behind the replacement.
        {
            let main = self.session().await.main();
            let settled = tokio::select! {
                settled = main.wait_for_idle(&cx) => settled,
                () = self.signal_shutdown.cancelled() => {
                    return Err(SIGNAL_EXIT_IN_PROGRESS.to_string());
                }
            };
            settled.map_err(|error| error.to_string())?;
        }
        let mut handle = tokio::select! {
            guard = self.handle.write() => guard,
            () = self.signal_shutdown.cancelled() => {
                return Err(SIGNAL_EXIT_IN_PROGRESS.to_string());
            }
        };
        // Reopening the currently-owned session: ADOPT the current lease
        // (TS `acquireReplacementLease` reuses the current lease for the
        // same path) — it never leaves this process, so a failed build
        // never leaves the live session unleased.
        let mut adopted_lease = None;
        if let RpcEngineRequest::Open {
            session_path,
            reuse_lease,
        } = &mut request
        {
            let canonical = crate::lease::canonical_session_path(session_path);
            let same_path = handle
                .session_lease
                .as_ref()
                .is_some_and(|lease| lease.session_path == canonical);
            if same_path {
                adopted_lease = handle.session_lease.take();
                *reuse_lease = true;
            }
        }
        let built = tokio::select! {
            built = (self.factory)(request, self.outputs.turn_wait_sink()) => built,
            () = self.signal_shutdown.cancelled() => Err(SIGNAL_EXIT_IN_PROGRESS.to_string()),
        };
        let mut replacement = match built {
            Ok(replacement) => replacement,
            Err(error) => {
                if adopted_lease.is_some() {
                    handle.session_lease = adopted_lease;
                }
                return Err(error);
            }
        };
        // Attach the replacement's pump BEFORE publishing the handle: a
        // prompt dispatched the instant the handle lands finds the pump
        // attached, so the turn's first frames never drop.
        let pump = match EventPump::attach(
            &replacement.session,
            &self.outputs,
            &self.last_goal,
            &cx,
        )
        .await
        {
            Ok(pump) => pump,
            Err(error) => {
                close_session(&replacement.session).await;
                if adopted_lease.is_some() {
                    handle.session_lease = adopted_lease;
                }
                return Err(error.to_string());
            }
        };
        // The teardown aborts only now that the replacement exists (TS
        // teardownForReplacement runs after the open): a turn admitted
        // after the settle (it raced the write guard) is aborted, its
        // terminal frames still stream, and the old session closes idle.
        // An unreadable live state aborts too (the close must not wait a
        // turn out).
        let old_main = handle.session.main();
        if !matches!(
            is_busy(handle.session.harness(), old_main.id(), &cx).await,
            Ok(false)
        ) {
            if let Err(error) = old_main
                .abort(ConversationAbortOptions::default(), &cx)
                .await
            {
                eprintln!("eukhe-daemon: rpc replacement abort failed: {error}");
            }
        }
        let previous = self.pump.lock().await.replace(pump);
        if let Some(previous) = previous {
            previous.stop().await;
        }
        close_session(&handle.session).await;
        // The adopted same-path lease rides the replacement (TS reuses
        // the current lease); a fresh open carries the lease the
        // factory's open guard acquired.
        if adopted_lease.is_some() {
            replacement.session_lease = adopted_lease;
        }
        *handle = replacement;
        Ok(())
    }

    /// Whole-session replacement under its own lease.
    ///
    /// # Errors
    ///
    /// See [`RpcSession::replace_locked`].
    pub async fn replace(&self, request: RpcEngineRequest) -> Result<(), String> {
        let _lease = self.replacement.lock().await;
        self.replace_locked(request).await
    }

    /// Abort the main conversation's running work (TS `abort()`): withdraw
    /// its queued inputs and resolve once it is idle.
    ///
    /// # Errors
    ///
    /// The abort fails (the Harness is closed).
    pub async fn abort(&self) -> Result<(), String> {
        let session = self.session().await;
        session
            .main()
            .abort(ConversationAbortOptions::default(), &rpc_context())
            .await
            .map_err(|error| error.to_string())
    }

    /// The exit settle (TS `onInputEnd` -> `waitForIdle` -> `shutdown`):
    /// wait the main conversation idle, detach the pump (the trailing
    /// frames streamed during the wait), and close the session.
    pub async fn dispose(&self) {
        let session = self.session().await;
        if let Err(error) = session.main().wait_for_idle(&rpc_context()).await {
            eprintln!("eukhe-daemon: rpc settle failed: {error}");
        }
        if let Some(pump) = self.pump.lock().await.take() {
            pump.stop().await;
        }
        close_session(&session).await;
    }
}

/// Close one session, reporting a failure on stderr (the exit and the
/// replacement proceed either way: the storage stays for the next open).
async fn close_session(session: &EukheSession) {
    if let Err(error) = session.close(&rpc_context()).await {
        eprintln!("eukhe-daemon: rpc session close failed: {error}");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn written(rx: &mut tokio::sync::mpsc::UnboundedReceiver<Value>) -> Vec<Value> {
        let mut frames = Vec::new();
        while let Ok(frame) = rx.try_recv() {
            frames.push(frame);
        }
        frames
    }

    #[tokio::test]
    async fn armed_outputs_buffer_until_the_flush() {
        let (writer, mut rx) = LineWriter::channel();
        let outputs = ConnectionOutputs::new(writer.clone());
        outputs.write(json!({ "n": 1 }));
        outputs.arm();
        outputs.write_all(vec![json!({ "n": 2 }), json!({ "n": 3 })]);
        writer.write(json!({ "response": true }));
        outputs.flush();
        outputs.write(json!({ "n": 4 }));
        assert_eq!(
            written(&mut rx),
            vec![
                json!({ "n": 1 }),
                json!({ "response": true }),
                json!({ "n": 2 }),
                json!({ "n": 3 }),
                json!({ "n": 4 }),
            ]
        );
    }

    #[tokio::test]
    async fn turn_waits_publish_chat_turn_wait_frames() {
        let (writer, mut rx) = LineWriter::channel();
        let outputs = ConnectionOutputs::new(writer);
        let sink = outputs.turn_wait_sink();
        sink(TurnWait::Waiting);
        sink(TurnWait::Cleared);
        assert_eq!(
            written(&mut rx),
            vec![
                json!({ "type": "chat_turn_wait", "waiting": true }),
                json!({ "type": "chat_turn_wait", "waiting": false }),
            ]
        );
    }
}
