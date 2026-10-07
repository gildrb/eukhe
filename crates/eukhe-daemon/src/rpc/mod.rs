//! RPC stdio mode: headless operation with JSON commands on stdin and
//! JSON responses and events on stdout (TS `modes/rpc/rpc-mode.ts`).
//!
//! One connection drives one live durable session (`EukheSession`, its
//! main conversation). Commands arrive as JSON lines and answer one
//! ordered stream of response and event frames: the response `data`
//! channel distinguishes an absent key from JSON `null`, a `prompt`
//! response is written before the turn's stream events (events landing
//! while the response is pending are buffered and flushed after it, TS
//! `promptResponsePending`), prompts serialize on a stdin-order chain (TS
//! `promptCommandTail`) while other commands run concurrently, and stdin
//! close settles the running turn before the process exits. SIGTERM exits
//! 143 and SIGHUP 129 (TS signal exit codes).
//!
//! The in-process transport serves the session directly, exactly like the
//! TS in-process connection: the scheduling and agent-messaging surfaces
//! answer their TS in-process "requires daemon mode" errors, and `observe`
//! sees no other active sessions (the in-process session hosts no family)
//! — the daemon-attached transport serves those for real.

pub mod commands;
mod event_pump;
pub mod model_commands;
pub mod prompt_commands;
pub mod protocol;
mod reads;
pub mod session;
pub mod session_commands;

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use eukhe_core::autonomous::AgentAutonomousConfig;
use eukhe_core::durable::goals::{
    autonomous_state, seed_initial_goal, set_autonomous, AutonomousChange,
};
use serde_json::Value;
use tokio::io::AsyncBufReadExt;

use protocol::{ParsedLine, RpcCommand};
use reads::rpc_context;
use session::{ConnectionOutputs, RpcEngineFactory, RpcSession};

/// Everything the composition root hands the mode.
pub struct RpcOptions {
    /// The session assembly: opens the startup session
    /// ([`session::RpcEngineRequest::Startup`]) and every whole-session
    /// replacement (`new_session` / `switch_session` / `fork`).
    pub engine_factory: RpcEngineFactory,
    /// The CLI autonomous flags: enabled on the startup session's main
    /// conversation unless it already runs autonomously.
    pub autonomous_config: Option<AgentAutonomousConfig>,
    /// The CLI `--goal` seed (objective, token budget) for the startup
    /// session's main conversation.
    pub initial_goal: Option<(String, Option<u64>)>,
}

/// The ordered stdout writer: one queue for responses and events, in
/// publication order (TS `output` through `writeRawStdout`). The queue
/// depth is tracked so an exit path can drain every queued frame before
/// the process exits (TS `process.exit` follows synchronous writes).
#[derive(Clone)]
pub struct LineWriter {
    tx: tokio::sync::mpsc::UnboundedSender<Value>,
    /// Frames queued but not yet written by the writer task (incremented
    /// on `write`, decremented once the task wrote the frame).
    pending: Arc<AtomicUsize>,
}

impl LineWriter {
    /// Spawn the writer task over the process stdout.
    fn spawn() -> Self {
        let (tx, mut rx) = tokio::sync::mpsc::unbounded_channel::<Value>();
        let pending = Arc::new(AtomicUsize::new(0));
        let task_pending = Arc::clone(&pending);
        tokio::spawn(async move {
            use tokio::io::AsyncWriteExt;
            let mut stdout = tokio::io::stdout();
            while let Some(frame) = rx.recv().await {
                if let Ok(mut line) = serde_json::to_string(&frame) {
                    line.push('\n');
                    // A broken stdout pipe has no reader left to tell;
                    // the frames retire so the exit drains never wait on
                    // it.
                    let _ = stdout.write_all(line.as_bytes()).await;
                    let _ = stdout.flush().await;
                }
                task_pending.fetch_sub(1, Ordering::SeqCst);
            }
        });
        Self { tx, pending }
    }

    /// A writer over a channel instead of stdout (the in-crate tests read
    /// the frames back).
    #[cfg(test)]
    pub(crate) fn channel() -> (Self, tokio::sync::mpsc::UnboundedReceiver<Value>) {
        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<Value>();
        let writer = Self {
            tx,
            pending: Arc::new(AtomicUsize::new(0)),
        };
        (writer, rx)
    }

    /// Queue one frame (serializeJsonLine: LF-only framing).
    pub fn write(&self, frame: Value) {
        self.pending.fetch_add(1, Ordering::SeqCst);
        if self.tx.send(frame).is_err() {
            // The writer task is gone (the runtime is shutting down):
            // nothing will write the frame, so it must not hold a drain.
            self.pending.fetch_sub(1, Ordering::SeqCst);
        }
    }

    /// Wait until the writer task has written every queued frame (the
    /// EOF path calls this before the exit, TS parity for synchronous
    /// writes: the TS exit blocks behind its writes until the reader
    /// drains or the pipe breaks — a slow reader is drained, never
    /// truncated).
    pub async fn drain(&self) {
        while self.pending.load(Ordering::SeqCst) > 0 {
            tokio::task::yield_now().await;
        }
    }

    /// The signal-exit drain (SIGTERM/SIGHUP): the 143/129 exit codes
    /// must fire even against a stalled reader, so the wait is bounded
    /// (a broken or slow pipe retires after the deadline).
    pub async fn drain_bounded(&self) {
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(2);
        while self.pending.load(Ordering::SeqCst) > 0 {
            if std::time::Instant::now() >= deadline {
                return;
            }
            tokio::task::yield_now().await;
        }
    }
}

/// The signal exit codes (TS `runRpcModeWithConnectionInternal`).
const SIGTERM_EXIT: i32 = 143;
const SIGHUP_EXIT: i32 = 129;

/// The mode's exit path. The signal paths' bounded drains already waited
/// on the writer task (every frame is flushed as it is written), so the
/// exit never re-acquires the stdout lock directly: a stalled reader
/// holds that lock inside the writer task's blocked write, and a
/// synchronous flush here would wait on it indefinitely — the 143/129
/// exit must fire regardless of the reader (TS `process.exit` never
/// queues on the pipe).
fn exit_with(code: i32) -> ! {
    std::process::exit(code);
}

/// The async entry: open the startup session through the factory, seed
/// the CLI goal/autonomous state, and serve the RPC stdio mode until stdin
/// closes or a signal exits. Returns the process exit code.
///
/// # Errors
///
/// The startup session cannot open (the factory's error, before any
/// frame is written), or the CLI goal/autonomous seed fails. The
/// transport itself never errors out of the loop (protocol failures
/// answer on stdout, TS parity).
pub async fn run_rpc_mode(options: RpcOptions) -> anyhow::Result<i32> {
    let writer = LineWriter::spawn();
    let session = RpcSession::start(
        options.engine_factory,
        ConnectionOutputs::new(writer.clone()),
    )
    .await
    .map_err(anyhow::Error::msg)?;
    seed_startup_state(&session, options.initial_goal, options.autonomous_config).await?;
    let session = Arc::new(session);
    let state = Arc::new(commands::RpcState {
        session: Arc::clone(&session),
        writer: writer.clone(),
        model_ops: tokio::sync::Mutex::new(()),
        session_ops: tokio::sync::Mutex::new(()),
    });
    spawn_signal_handlers(&session, &writer);
    Ok(serve_stdin(state).await)
}

/// The CLI `--goal` seed and the CLI autonomous flags on the startup
/// session's main conversation (TS `createAgentSession` parity).
async fn seed_startup_state(
    session: &RpcSession,
    initial_goal: Option<(String, Option<u64>)>,
    autonomous_config: Option<AgentAutonomousConfig>,
) -> anyhow::Result<()> {
    let opened = session.session().await;
    let main = opened.main().id();
    let cx = rpc_context();
    if let Some((objective, token_budget)) = initial_goal {
        seed_initial_goal(opened.harness(), main, &objective, token_budget, &cx).await?;
    }
    if let Some(config) = autonomous_config {
        if !autonomous_state(opened.harness(), main, &cx).await?.enabled {
            set_autonomous(opened.harness(), main, AutonomousChange::On(config), &cx).await?;
        }
    }
    Ok(())
}

/// SIGTERM exits 143, SIGHUP 129 (the TS mode handles exactly this
/// pair): abort the running turn, settle it, close the session, drain
/// the queued frames, exit.
fn spawn_signal_handlers(session: &Arc<RpcSession>, writer: &LineWriter) {
    use tokio::signal::unix::{signal, SignalKind};
    for (kind, code) in [
        (SignalKind::terminate(), SIGTERM_EXIT),
        (SignalKind::hangup(), SIGHUP_EXIT),
    ] {
        let session = Arc::clone(session);
        let writer = writer.clone();
        tokio::spawn(async move {
            let Ok(mut stream) = signal(kind) else {
                return;
            };
            stream.recv().await;
            // Fire the shutdown broadcast FIRST: a replacement mid-settle
            // refuses instead of holding the lease across the model's
            // runtime, so the exit never queues behind
            // new_session/switch_session/fork.
            session.fire_shutdown();
            // Serialize with any in-flight replacement: the lease holds
            // until the exit, so the abort and the close target the
            // session that is live NOW.
            let _replacement = session.replacement_lease().await;
            if let Err(error) = session.abort().await {
                eprintln!("eukhe-daemon: rpc signal abort failed: {error}");
            }
            session.dispose().await;
            writer.drain_bounded().await;
            exit_with(code);
        });
    }
}

/// The stdin loop: parse every line, dispatch commands concurrently
/// (prompts serialize on the stdin-order chain), and settle on EOF.
async fn serve_stdin(state: Arc<commands::RpcState>) -> i32 {
    // TS `promptCommandTail`: prompt commands chain on their stdin-order
    // predecessor — the chain hands each prompt the previous prompt's
    // completion, so execution and response order follow the read order.
    let mut prompt_tail: Option<tokio::sync::oneshot::Receiver<()>> = None;
    // The in-flight handlers EOF waits for (TS `pendingInputHandlers`).
    let mut pending = tokio::task::JoinSet::new();
    let mut stdin = tokio::io::BufReader::new(tokio::io::stdin());
    let mut line = String::new();
    loop {
        line.clear();
        match stdin.read_line(&mut line).await {
            Ok(0) | Err(_) => break,
            Ok(_) => {}
        }
        if line.trim().is_empty() {
            continue;
        }
        match protocol::parse_line(&line) {
            ParsedLine::ParseError(response) => state.writer.write(response),
            ParsedLine::Command(command) => {
                let state = Arc::clone(&state);
                let is_prompt = command.command == "prompt";
                let previous = if is_prompt { prompt_tail.take() } else { None };
                let (done_tx, done_rx) = tokio::sync::oneshot::channel();
                if is_prompt {
                    prompt_tail = Some(done_rx);
                }
                pending.spawn(async move {
                    if let Some(previous) = previous {
                        // A dropped predecessor (its task panicked) still
                        // releases the chain.
                        let _ = previous.await;
                    }
                    dispatch_one(state, command).await;
                    // The successor may already be gone (EOF dropped it).
                    let _ = done_tx.send(());
                });
            }
        }
    }
    // stdin closed: settle the in-flight handlers, wait the session idle,
    // close it, drain the queued frames, exit 0 (TS `onInputEnd`).
    while pending.join_next().await.is_some() {}
    state.session.dispose().await;
    state.writer.drain().await;
    0
}

/// One command's dispatch: prompts run on the stdin-order chain (the
/// caller hands each prompt its predecessor's completion) and buffer
/// connection events until their response is written (TS
/// `handleInputLine`); every other command runs unlocked.
async fn dispatch_one(state: Arc<commands::RpcState>, command: RpcCommand) {
    if command.command != "prompt" {
        let response = commands::handle_command(&state, command).await;
        state.writer.write(response);
        return;
    }
    let outputs = state.session.outputs();
    outputs.arm();
    let response = commands::handle_command(&state, command).await;
    // The response writes while the buffer stays armed (TS `output` of
    // the response precedes the buffered events); the flush then
    // disarms and emits them in arrival order.
    state.writer.write(response);
    outputs.flush();
}
