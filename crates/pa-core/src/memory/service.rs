//! The chat's single owner and its clients (`docs/optchat.md` §2 "One
//! writer", §4.1 the pump, §6 settle).
//!
//! The first process that binds `chat/lock` owns the chat for its whole
//! life: it loads the files, folds the view, runs the compactor, and is the
//! only writer. Every other process connects to the same socket and sends
//! JSON-line requests. When the owner dies, its socket refuses connections:
//! the next request deletes the stale socket and takes ownership over.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{mpsc, Arc};
use std::time::{Duration, SystemTime};

use pa_types::platform::transport::{
    bind_transport, connect_transport, AsyncWriteHalf, TransportListener, TransportStream,
};
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio::sync::{oneshot, Mutex};

use super::chat::{free_text, Chat, Step, Zoom};
use super::compactor::{build_line, NodeRequest, Summarizer};
use super::prompts::{compress_step, merge_step};
use super::store::{LoadMode, MessageRecord, NodeRecord, Store};
use super::view::{pieces, Part};
use super::{labeled, Kind, RETRY};

/// Consecutive failures of the node a turn waits on before the wait fails
/// with the compactor's error (the compactor itself retries forever).
const SETTLE_FAILURES: u32 = 3;
/// How many recent messages a re-sent append checks for its own copy.
const DEDUPE_WINDOW: usize = 64;
/// The largest request or reply line accepted on the socket.
const MAX_LINE_BYTES: usize = 64 * 1024 * 1024;
/// How long a claimer waits for another claimer's takeover lock.
const CLAIM_LOCK_WAIT: Duration = Duration::from_secs(10);

/// The agent's view, rendered.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RenderedView {
    /// Messages the view covers (`T`).
    pub messages: u64,
    /// `<chat>`, one `id+n|text` line per part, `</chat>`.
    pub text: String,
}

impl RenderedView {
    /// The view cut at the last line end before each cache mark; every
    /// piece but the last carries a cache breakpoint.
    #[must_use]
    pub fn pieces(&self) -> Vec<String> {
        pieces(&self.text)
    }
}

/// A snapshot of the chat for status displays.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct MemoryStatus {
    pub messages: u64,
    pub nodes: u64,
    pub view_lines: u64,
    pub view_bytes: u64,
    /// Messages whose view line is not summarized yet.
    pub unsummarized: u64,
    /// Compactor calls running or waiting out their retry delay.
    pub running: u64,
    /// The newest compactor failure that is not resolved yet.
    pub last_error: Option<String>,
}

/// One imported message.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct ImportItem {
    pub kind: Kind,
    pub text: String,
    pub date: String,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "op", rename_all = "snake_case", rename_all_fields = "camelCase")]
enum Request {
    /// Log one message. `dedupe` re-sends after a lost connection: a copy
    /// with the same kind, date and text among the newest messages is
    /// answered instead of written twice.
    Append {
        kind: Kind,
        text: String,
        date: String,
        dedupe: bool,
    },
    /// Log a batch at once, only when the log has exactly `expect_start`
    /// messages (imports that keep their ids).
    Import {
        expect_start: Option<u64>,
        items: Vec<ImportItem>,
    },
    Settle,
    Render,
    Zoom {
        id: u64,
        count: u64,
    },
    Date {
        id: u64,
    },
    Status,
    Persist,
    Parts,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(
    tag = "reply",
    rename_all = "snake_case",
    rename_all_fields = "camelCase"
)]
enum Reply {
    Appended { id: u64 },
    Imported { first: u64, count: u64 },
    Settled,
    Rendered { view: RenderedView },
    Text { text: String },
    Status { status: MemoryStatus },
    Persisting,
    Parts { parts: Vec<(u32, u64)> },
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
struct RequestFrame {
    id: u64,
    request: Request,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "lowercase")]
enum Outcome {
    Ok(Reply),
    Error(String),
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
struct ReplyFrame {
    id: u64,
    outcome: Outcome,
}

/// A handle on the chat memory: the owner's actor in this process, or a
/// client of the owner in another. Cheap to clone.
#[derive(Clone)]
pub struct Memory {
    inner: Arc<Inner>,
}

impl std::fmt::Debug for Memory {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("Memory")
            .field("dir", &self.inner.dir)
            .finish_non_exhaustive()
    }
}

struct Inner {
    dir: PathBuf,
    summarizer: Arc<dyn Summarizer>,
    link: Mutex<Option<Link>>,
}

#[derive(Clone)]
enum Link {
    Owner(Arc<OwnerHandle>),
    Client(Arc<Client>),
}

impl Memory {
    /// Open the chat in `dir`: own it when no live process does, else
    /// become a client of the owner. Must run inside a tokio runtime (the
    /// owner runs its compactor on it).
    ///
    /// # Errors
    ///
    /// Returns an error when the directory cannot be created, the files
    /// cannot be loaded, or the lock socket can be neither bound nor
    /// reached.
    pub async fn open(
        dir: impl Into<PathBuf>,
        summarizer: Arc<dyn Summarizer>,
    ) -> anyhow::Result<Memory> {
        let memory = Memory {
            inner: Arc::new(Inner {
                dir: dir.into(),
                summarizer,
                link: Mutex::new(None),
            }),
        };
        memory.link().await?;
        Ok(memory)
    }

    /// The chat directory.
    #[must_use]
    pub fn dir(&self) -> &Path {
        &self.inner.dir
    }

    /// Whether this process owns the chat right now.
    pub async fn owns(&self) -> bool {
        matches!(&*self.inner.link.lock().await, Some(Link::Owner(_)))
    }

    /// Log one message (written and fsynced before this returns). Returns
    /// its id.
    ///
    /// # Errors
    ///
    /// Returns an error when the message cannot be written.
    pub async fn append(&self, kind: Kind, text: &str) -> anyhow::Result<u64> {
        let date = crate::platform::local_time(SystemTime::now())?.rfc3339();
        match self
            .request(Request::Append {
                kind,
                text: text.to_string(),
                date,
                dedupe: false,
            })
            .await?
        {
            Reply::Appended { id } => Ok(id),
            other => Err(unexpected(&other)),
        }
    }

    /// Wait until every line of the view is a summary. Dropping the future
    /// cancels the wait.
    ///
    /// # Errors
    ///
    /// Returns the compactor's error when the node the view waits on keeps
    /// failing, or when the owner cannot be reached.
    pub async fn settle(&self) -> anyhow::Result<()> {
        match self.request(Request::Settle).await? {
            Reply::Settled => Ok(()),
            other => Err(unexpected(&other)),
        }
    }

    /// The view as it is now.
    ///
    /// # Errors
    ///
    /// Returns an error when the owner cannot be reached.
    pub async fn render(&self) -> anyhow::Result<RenderedView> {
        match self.request(Request::Render).await? {
            Reply::Rendered { view } => Ok(view),
            other => Err(unexpected(&other)),
        }
    }

    /// `zoom(id, n)`: the two lines under `id+n`, or message `id` whole
    /// when `n = 1`, or `No line id+n.`.
    ///
    /// # Errors
    ///
    /// Returns an error when the message cannot be read back or the owner
    /// cannot be reached.
    pub async fn zoom(&self, id: u64, count: u64) -> anyhow::Result<String> {
        match self.request(Request::Zoom { id, count }).await? {
            Reply::Text { text } => Ok(text),
            other => Err(unexpected(&other)),
        }
    }

    /// `date(id)`: the local date and time of message `id`.
    ///
    /// # Errors
    ///
    /// Returns an error when the owner cannot be reached.
    pub async fn date(&self, id: u64) -> anyhow::Result<String> {
        match self.request(Request::Date { id }).await? {
            Reply::Text { text } => Ok(text),
            other => Err(unexpected(&other)),
        }
    }

    /// A snapshot for status displays.
    ///
    /// # Errors
    ///
    /// Returns an error when the owner cannot be reached.
    pub async fn status(&self) -> anyhow::Result<MemoryStatus> {
        match self.request(Request::Status).await? {
            Reply::Status { status } => Ok(status),
            other => Err(unexpected(&other)),
        }
    }

    /// Commit the chat directory with git in the background (§10 "persist
    /// after each turn"); failures are reported by the owner.
    ///
    /// # Errors
    ///
    /// Returns an error when the owner cannot be reached.
    pub async fn persist(&self) -> anyhow::Result<()> {
        match self.request(Request::Persist).await? {
            Reply::Persisting => Ok(()),
            other => Err(unexpected(&other)),
        }
    }

    /// Log a batch at once; with `expect_start`, only when the log holds
    /// exactly that many messages. Returns the first id and the count.
    pub(crate) async fn import(
        &self,
        expect_start: Option<u64>,
        items: Vec<ImportItem>,
    ) -> anyhow::Result<(u64, u64)> {
        match self
            .request(Request::Import {
                expect_start,
                items,
            })
            .await?
        {
            Reply::Imported { first, count } => Ok((first, count)),
            other => Err(unexpected(&other)),
        }
    }

    async fn request(&self, mut request: Request) -> anyhow::Result<Reply> {
        for _ in 0..4 {
            match self.link().await? {
                Link::Owner(owner) => return owner.request(request).await,
                Link::Client(client) => match client.request(&request).await {
                    Ok(Outcome::Ok(reply)) => return Ok(reply),
                    Ok(Outcome::Error(error)) => return Err(anyhow::anyhow!(error)),
                    Err(Disconnected) => {
                        self.forget(&client).await;
                        match &mut request {
                            Request::Append { dedupe, .. } => *dedupe = true,
                            Request::Import { .. } => anyhow::bail!(
                                "the chat owner went away during an import; nothing after the last \
                                 reply is certain: check `chat status` before importing again"
                            ),
                            Request::Settle
                            | Request::Render
                            | Request::Zoom { .. }
                            | Request::Date { .. }
                            | Request::Status
                            | Request::Persist
                            | Request::Parts => {}
                        }
                    }
                },
            }
        }
        anyhow::bail!(
            "the chat memory at {} keeps losing its owner",
            self.inner.dir.display()
        )
    }

    /// The current link, established when there is none.
    async fn link(&self) -> anyhow::Result<Link> {
        let mut slot = self.inner.link.lock().await;
        if let Some(link) = slot.as_ref() {
            return Ok(link.clone());
        }
        let link = match claim(&self.inner.dir).await? {
            Claim::Owned(listener) => Link::Owner(
                OwnerHandle::start(
                    &self.inner.dir,
                    listener,
                    Arc::clone(&self.inner.summarizer),
                )
                .await?,
            ),
            Claim::Held(stream) => Link::Client(Client::connect(stream)),
        };
        *slot = Some(link.clone());
        Ok(link)
    }

    async fn forget(&self, client: &Arc<Client>) {
        let mut slot = self.inner.link.lock().await;
        if matches!(slot.as_ref(), Some(Link::Client(current)) if Arc::ptr_eq(current, client)) {
            *slot = None;
        }
    }
}

/// The live owner's view parts, when an owner answers on `dir/lock`. Never
/// claims ownership: a reader must not start a compactor.
pub(crate) async fn live_parts(dir: &Path) -> Option<Vec<(u32, u64)>> {
    let stream = connect_transport(&dir.join("lock")).await.ok()?;
    let client = Client::connect(stream);
    match client.request(&Request::Parts).await {
        Ok(Outcome::Ok(Reply::Parts { parts })) => Some(parts),
        Ok(Outcome::Ok(_) | Outcome::Error(_)) | Err(Disconnected) => None,
    }
}

fn unexpected(reply: &Reply) -> anyhow::Error {
    anyhow::anyhow!("unexpected chat memory reply: {reply:?}")
}

// ---------------------------------------------------------------------------
// Claiming the lock socket
// ---------------------------------------------------------------------------

enum Claim {
    Owned(Box<dyn TransportListener>),
    Held(Box<dyn TransportStream>),
}

/// Attempts at claiming before a transient connect error is final.
const CLAIM_ATTEMPTS: u32 = 20;

/// Bind `dir/lock`, or reach its live owner. A socket that refuses
/// connections is stale (the OS frees it when its owner dies): it is
/// removed and taken over. Claimers serialize on a lock directory so two
/// of them never remove each other's fresh socket.
async fn claim(dir: &Path) -> anyhow::Result<Claim> {
    std::fs::create_dir_all(dir)?;
    crate::platform::restrict_dir(dir)?;
    let lock = dir.join("lock");
    let mut attempt = 0;
    loop {
        attempt += 1;
        let outcome = {
            let _takeover = acquire_takeover_lock(&lock).await?;
            claim_locked(&lock).await
        };
        match outcome {
            Ok(claim) => return Ok(claim),
            // A listener that is shutting down can accept and reset, or
            // refuse with a full backlog: the owner is changing hands.
            Err(error)
                if attempt < CLAIM_ATTEMPTS
                    && matches!(
                        io_kind(&error),
                        Some(
                            std::io::ErrorKind::ConnectionReset
                                | std::io::ErrorKind::ConnectionAborted
                                | std::io::ErrorKind::WouldBlock
                        )
                    ) =>
            {
                tokio::time::sleep(Duration::from_millis(25)).await;
            }
            Err(error) => {
                return Err(error.context(format!("cannot claim the chat lock {}", lock.display())))
            }
        }
    }
}

async fn claim_locked(lock: &Path) -> anyhow::Result<Claim> {
    match bind_transport(lock).await {
        Ok(listener) => {
            crate::platform::restrict_file(lock)?;
            return Ok(Claim::Owned(listener));
        }
        Err(bind_error) => {
            if io_kind(&bind_error) != Some(std::io::ErrorKind::AddrInUse) {
                return Err(bind_error);
            }
        }
    }
    match connect_transport(lock).await {
        Ok(stream) => Ok(Claim::Held(stream)),
        Err(connect_error) => match io_kind(&connect_error) {
            Some(std::io::ErrorKind::ConnectionRefused | std::io::ErrorKind::NotFound) => {
                match std::fs::remove_file(lock) {
                    Ok(()) => {}
                    Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                    Err(error) => return Err(error.into()),
                }
                let listener = bind_transport(lock).await?;
                crate::platform::restrict_file(lock)?;
                Ok(Claim::Owned(listener))
            }
            _ => Err(connect_error),
        },
    }
}

fn io_kind(error: &anyhow::Error) -> Option<std::io::ErrorKind> {
    error
        .downcast_ref::<std::io::Error>()
        .map(std::io::Error::kind)
}

async fn acquire_takeover_lock(lock: &Path) -> anyhow::Result<crate::platform::LockDir> {
    let deadline = tokio::time::Instant::now() + CLAIM_LOCK_WAIT;
    loop {
        match crate::platform::LockDir::acquire(lock, CLAIM_LOCK_WAIT) {
            Ok(guard) => return Ok(guard),
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                if tokio::time::Instant::now() >= deadline {
                    return Err(anyhow::Error::new(error)
                        .context(format!("another process is claiming {}", lock.display())));
                }
                tokio::time::sleep(Duration::from_millis(25)).await;
            }
            Err(error) => return Err(error.into()),
        }
    }
}

// ---------------------------------------------------------------------------
// Client
// ---------------------------------------------------------------------------

/// The connection to the owner died; the request may or may not have run.
#[derive(Debug)]
struct Disconnected;

type Pending = std::sync::Mutex<HashMap<u64, oneshot::Sender<Outcome>>>;

struct Client {
    writer: Mutex<Box<dyn AsyncWriteHalf>>,
    pending: Arc<Pending>,
    closed: Arc<AtomicBool>,
    next_id: AtomicU64,
    reader: tokio::task::JoinHandle<()>,
}

impl Drop for Client {
    fn drop(&mut self) {
        self.reader.abort();
    }
}

impl Client {
    fn connect(stream: Box<dyn TransportStream>) -> Arc<Client> {
        let (read_half, write_half) = stream.split();
        let pending: Arc<Pending> = Arc::default();
        let closed = Arc::new(AtomicBool::new(false));
        let reader = tokio::spawn({
            let pending = Arc::clone(&pending);
            let closed = Arc::clone(&closed);
            async move {
                let mut reader = BufReader::new(read_half);
                let mut line = String::new();
                loop {
                    line.clear();
                    match reader.read_line(&mut line).await {
                        Ok(0) | Err(_) => break,
                        Ok(_) => {}
                    }
                    let Ok(frame) = serde_json::from_str::<ReplyFrame>(line.trim_end()) else {
                        // A malformed reply means the peer is not a chat
                        // owner of this version: drop the connection.
                        break;
                    };
                    let waiter = pending
                        .lock()
                        .unwrap_or_else(std::sync::PoisonError::into_inner)
                        .remove(&frame.id);
                    if let Some(waiter) = waiter {
                        // The requester may have stopped waiting (a
                        // cancelled settle); its reply has no reader.
                        let _ = waiter.send(frame.outcome);
                    }
                }
                closed.store(true, Ordering::SeqCst);
                pending
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner)
                    .clear();
            }
        });
        Arc::new(Client {
            writer: Mutex::new(write_half),
            pending,
            closed,
            next_id: AtomicU64::new(1),
            reader,
        })
    }

    async fn request(&self, request: &Request) -> Result<Outcome, Disconnected> {
        let id = self.next_id.fetch_add(1, Ordering::SeqCst);
        let (sender, receiver) = oneshot::channel();
        self.pending
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .insert(id, sender);
        if self.closed.load(Ordering::SeqCst) {
            self.pending
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .remove(&id);
            return Err(Disconnected);
        }
        let mut line = serde_json::to_string(&RequestFrame {
            id,
            request: request.clone(),
        })
        .map_err(|_| Disconnected)?;
        line.push('\n');
        let written = {
            let mut writer = self.writer.lock().await;
            match writer.write_all(line.as_bytes()).await {
                Ok(()) => writer.flush().await,
                Err(error) => Err(error),
            }
        };
        if written.is_err() {
            self.pending
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .remove(&id);
            return Err(Disconnected);
        }
        receiver.await.map_err(|_| Disconnected)
    }
}

// ---------------------------------------------------------------------------
// Owner
// ---------------------------------------------------------------------------

/// The owner's entry points: the actor's command channel and the task
/// serving other processes.
struct OwnerHandle {
    commands: mpsc::Sender<Command>,
    server: tokio::task::JoinHandle<()>,
    actor: Option<std::thread::JoinHandle<()>>,
    lock: PathBuf,
    identity: Option<pa_types::daemon::SocketIdentity>,
}

impl Drop for OwnerHandle {
    fn drop(&mut self) {
        // Stop serving: the connections close and their clients fail over.
        self.server.abort();
        // The actor finishes the commands already queued, then stops; only
        // then may another process write the files.
        let _ = self.commands.send(Command::Shutdown);
        if let Some(actor) = self.actor.take() {
            // A panicked actor has nothing left to finish.
            let _ = actor.join();
        }
        // Free the path for the next owner at once; a socket that is no
        // longer this owner's is left alone.
        if self.identity.is_some()
            && pa_types::platform::socket_identity(&self.lock) == self.identity
        {
            // Already gone is fine: the next claimer binds a fresh one.
            let _ = std::fs::remove_file(&self.lock);
        }
    }
}

enum Command {
    Request {
        request: Request,
        reply: oneshot::Sender<Outcome>,
    },
    Built {
        part: Part,
        result: anyhow::Result<String>,
    },
    Retry {
        part: Part,
        generation: u64,
    },
    Persisted(Result<(), String>),
    Shutdown,
}

impl OwnerHandle {
    async fn start(
        dir: &Path,
        listener: Box<dyn TransportListener>,
        summarizer: Arc<dyn Summarizer>,
    ) -> anyhow::Result<Arc<OwnerHandle>> {
        let (commands, receiver) = mpsc::channel();
        let (ready_sender, ready) = oneshot::channel();
        let runtime = tokio::runtime::Handle::current();
        let actor_commands = commands.clone();
        let actor_dir = dir.to_path_buf();
        let lock = dir.join("lock");
        let identity = pa_types::platform::socket_identity(&lock);
        let actor = std::thread::Builder::new()
            .name("chat-memory".to_string())
            .spawn(move || {
                let actor = match Actor::load(&actor_dir, summarizer, runtime, actor_commands) {
                    Ok(actor) => {
                        // The opener waits for this; if it went away the
                        // actor still serves the socket below.
                        let _ = ready_sender.send(Ok(()));
                        actor
                    }
                    Err(error) => {
                        let _ = ready_sender.send(Err(error));
                        return;
                    }
                };
                actor.run(&receiver);
            })?;
        ready
            .await
            .map_err(|_| anyhow::anyhow!("the chat memory actor stopped while loading"))??;
        let server = tokio::spawn(serve(listener, commands.clone()));
        Ok(Arc::new(OwnerHandle {
            commands,
            server,
            actor: Some(actor),
            lock,
            identity,
        }))
    }

    async fn request(&self, request: Request) -> anyhow::Result<Reply> {
        match send_to_actor(&self.commands, request).await? {
            Outcome::Ok(reply) => Ok(reply),
            Outcome::Error(error) => Err(anyhow::anyhow!(error)),
        }
    }
}

async fn send_to_actor(
    commands: &mpsc::Sender<Command>,
    request: Request,
) -> anyhow::Result<Outcome> {
    let (reply, receiver) = oneshot::channel();
    commands
        .send(Command::Request { request, reply })
        .map_err(|_| anyhow::anyhow!("the chat memory actor has stopped"))?;
    receiver
        .await
        .map_err(|_| anyhow::anyhow!("the chat memory actor stopped before replying"))
}

/// Accept clients until the owner goes away; each request runs as its own
/// task, so a waiting settle never blocks the connection. Every task lives
/// in a `JoinSet` owned by this one: aborting the server closes them all.
async fn serve(listener: Box<dyn TransportListener>, commands: mpsc::Sender<Command>) {
    let mut connections = tokio::task::JoinSet::new();
    loop {
        // Reap finished connections so the set does not grow forever.
        while connections.try_join_next().is_some() {}
        let Ok(stream) = listener.accept().await else {
            // Accept errors are transient (descriptor exhaustion, aborted
            // handshakes); keep serving after a short pause.
            tokio::time::sleep(Duration::from_millis(100)).await;
            continue;
        };
        let commands = commands.clone();
        connections.spawn(serve_connection(stream, commands));
    }
}

/// One client connection: JSON-line requests in, replies out by id.
async fn serve_connection(stream: Box<dyn TransportStream>, commands: mpsc::Sender<Command>) {
    let (read_half, write_half) = stream.split();
    let writer = Arc::new(Mutex::new(write_half));
    let mut reader = BufReader::new(read_half);
    let mut line = String::new();
    let mut requests = tokio::task::JoinSet::new();
    loop {
        while requests.try_join_next().is_some() {}
        line.clear();
        match reader.read_line(&mut line).await {
            Ok(0) | Err(_) => break,
            Ok(read) if read > MAX_LINE_BYTES => break,
            Ok(_) => {}
        }
        let Ok(frame) = serde_json::from_str::<RequestFrame>(line.trim_end()) else {
            // Not a chat client: close the connection at once so a foreign
            // prober never waits on it.
            break;
        };
        let commands = commands.clone();
        let writer = Arc::clone(&writer);
        requests.spawn(async move {
            let outcome = match send_to_actor(&commands, frame.request).await {
                Ok(outcome) => outcome,
                Err(error) => Outcome::Error(format!("{error:#}")),
            };
            let Ok(mut reply) = serde_json::to_string(&ReplyFrame {
                id: frame.id,
                outcome,
            }) else {
                return;
            };
            reply.push('\n');
            let mut writer = writer.lock().await;
            // A client that went away loses only its own reply.
            if writer.write_all(reply.as_bytes()).await.is_ok() {
                let _ = writer.flush().await;
            }
        });
    }
    // The client hung up: its pending replies have no reader. Waiting
    // requests (a settle) end with the connection.
    requests.abort_all();
}

/// The owner's state, on its own thread: every read and write of the chat
/// files happens here, in order.
struct Actor {
    dir: PathBuf,
    chat: Chat,
    store: Store,
    summarizer: Arc<dyn Summarizer>,
    runtime: tokio::runtime::Handle,
    commands: mpsc::Sender<Command>,
    settle_waiters: Vec<oneshot::Sender<Outcome>>,
    failures: HashMap<Part, Failure>,
    /// Nodes that failed and wait out their retry delay (a subset of the
    /// chat's busy set).
    waiting: HashSet<Part>,
    persisting: bool,
    persist_again: bool,
    persist_reported: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Failure {
    count: u32,
    error: String,
    generation: u64,
}

impl Actor {
    fn load(
        dir: &Path,
        summarizer: Arc<dyn Summarizer>,
        runtime: tokio::runtime::Handle,
        commands: mpsc::Sender<Command>,
    ) -> anyhow::Result<Actor> {
        let (store, loaded) = Store::open(dir, LoadMode::Repair)?;
        let mut problems = loaded.problems.clone();
        let chat = Chat::from_loaded(loaded, &mut problems);
        for problem in problems {
            tracing::warn!(target: "chat_memory", "{problem}");
        }
        let mut actor = Actor {
            dir: dir.to_path_buf(),
            chat,
            store,
            summarizer,
            runtime,
            commands,
            settle_waiters: Vec::new(),
            failures: HashMap::new(),
            waiting: HashSet::new(),
            persisting: false,
            persist_again: false,
            persist_reported: false,
        };
        actor.pump();
        Ok(actor)
    }

    fn run(mut self, receiver: &mpsc::Receiver<Command>) {
        while let Ok(command) = receiver.recv() {
            match command {
                Command::Request { request, reply } => self.handle(request, reply),
                Command::Built { part, result } => self.built(part, result),
                Command::Retry { part, generation } => {
                    let current = self
                        .failures
                        .get(&part)
                        .is_some_and(|failure| failure.generation == generation);
                    if current && self.waiting.remove(&part) {
                        self.chat.release(part);
                        self.pump();
                    }
                }
                Command::Persisted(result) => self.persisted(result),
                Command::Shutdown => return,
            }
        }
    }

    fn handle(&mut self, request: Request, reply: oneshot::Sender<Outcome>) {
        let outcome = match request {
            Request::Settle => {
                self.add_settle_waiter(reply);
                return;
            }
            Request::Append {
                kind,
                text,
                date,
                dedupe,
            } => self
                .append(kind, text, date, dedupe)
                .map(|id| Reply::Appended { id }),
            Request::Import {
                expect_start,
                items,
            } => self.import(expect_start, items),
            Request::Render => Ok(Reply::Rendered {
                view: RenderedView {
                    messages: self.chat.total(),
                    text: self.chat.render(),
                },
            }),
            Request::Zoom { id, count } => self.zoom(id, count).map(|text| Reply::Text { text }),
            Request::Date { id } => Ok(Reply::Text {
                text: match self.chat.message(id) {
                    Some(meta) => display_date(&meta.date),
                    None => format!("No message {id}."),
                },
            }),
            Request::Status => Ok(Reply::Status {
                status: self.status(),
            }),
            Request::Persist => {
                self.persist();
                Ok(Reply::Persisting)
            }
            Request::Parts => Ok(Reply::Parts {
                parts: self
                    .chat
                    .view()
                    .parts()
                    .iter()
                    .map(|part| (part.l, part.i))
                    .collect(),
            }),
        };
        // The requester may have stopped waiting; the work is done either way.
        let _ = reply.send(match outcome {
            Ok(reply) => Outcome::Ok(reply),
            Err(error) => Outcome::Error(format!("{error:#}")),
        });
    }

    fn append(
        &mut self,
        kind: Kind,
        text: String,
        date: String,
        dedupe: bool,
    ) -> anyhow::Result<u64> {
        if dedupe {
            let total = self.chat.total();
            for id in (total.saturating_sub(DEDUPE_WINDOW as u64)..total).rev() {
                let Some(meta) = self.chat.message(id) else {
                    continue;
                };
                if meta.kind == kind && meta.date == date {
                    let record = self.store.read_message(meta)?;
                    if record.text == text {
                        return Ok(id);
                    }
                }
            }
        }
        let id = self.write_message(kind, text, date)?;
        self.pump();
        Ok(id)
    }

    fn write_message(&mut self, kind: Kind, text: String, date: String) -> anyhow::Result<u64> {
        let day = crate::platform::local_time(SystemTime::now())?.date();
        let record = MessageRecord {
            i: self.chat.total(),
            kind,
            size: labeled(kind, &text).len(),
            text,
            date,
        };
        let meta = self.store.append_message(&record, &day)?;
        Ok(self.chat.push_message(meta))
    }

    fn import(
        &mut self,
        expect_start: Option<u64>,
        items: Vec<ImportItem>,
    ) -> anyhow::Result<Reply> {
        let first = self.chat.total();
        if let Some(expected) = expect_start {
            if expected != first {
                anyhow::bail!(
                    "the chat holds {first} messages, not {expected}: an import that keeps its ids needs exactly {expected}"
                );
            }
        }
        let count = items.len() as u64;
        for item in items {
            self.write_message(item.kind, item.text, item.date)?;
        }
        self.pump();
        Ok(Reply::Imported { first, count })
    }

    fn zoom(&self, id: u64, count: u64) -> anyhow::Result<String> {
        Ok(match self.chat.zoom(id, count) {
            Zoom::Message(id) => {
                let meta = self
                    .chat
                    .message(id)
                    .ok_or_else(|| anyhow::anyhow!("message {id} is not indexed"))?;
                let record = self.store.read_message(meta)?;
                format!("{id}+0|{}", labeled(record.kind, &record.text))
            }
            Zoom::Lines(lines) => lines,
            Zoom::NoLine => format!("No line {id}+{count}."),
        })
    }

    fn status(&self) -> MemoryStatus {
        let first = self.chat.first();
        MemoryStatus {
            messages: self.chat.total(),
            nodes: self.chat.nodes().len() as u64,
            view_lines: self.chat.view().parts().len() as u64,
            view_bytes: self.chat.view().size() as u64,
            unsummarized: self.chat.total() - first,
            running: self.chat.busy_count() as u64,
            last_error: self
                .failures
                .values()
                .max_by_key(|failure| failure.generation)
                .map(|failure| failure.error.clone()),
        }
    }

    /// Start every node the pump allows. Free nodes (a short message, two
    /// short children) are built at once; the others go to the model.
    fn pump(&mut self) {
        loop {
            let mut built_free = false;
            for part in self.chat.candidates() {
                match self.prepare(part) {
                    Ok(Prepared::Free(text)) => {
                        if let Err(error) = self.save_node(part, &text) {
                            self.failed(part, &error);
                        } else {
                            built_free = true;
                        }
                    }
                    Ok(Prepared::Model(request)) => {
                        self.chat.mark_busy(part);
                        let summarizer = Arc::clone(&self.summarizer);
                        let commands = self.commands.clone();
                        self.runtime.spawn(async move {
                            let result =
                                build_line(summarizer.as_ref(), &request, now_millis()).await;
                            // A stopped owner no longer needs the line.
                            let _ = commands.send(Command::Built { part, result });
                        });
                    }
                    Err(error) => self.failed(part, &error),
                }
            }
            if !built_free {
                break;
            }
        }
        self.wake_settled();
    }

    fn prepare(&self, part: Part) -> anyhow::Result<Prepared> {
        let step = self.chat.step(part).ok_or_else(|| {
            anyhow::anyhow!("node {}+{} has no sources", part.start(), part.count())
        })?;
        let (free, step_text) = match &step {
            Step::Compress { message } => {
                let meta = self
                    .chat
                    .message(*message)
                    .ok_or_else(|| anyhow::anyhow!("message {message} is not indexed"))?;
                let record = self.store.read_message(meta)?;
                (
                    free_text(Some((record.kind, &record.text)), &step),
                    compress_step(&labeled(record.kind, &record.text)),
                )
            }
            Step::Merge { left, right } => (free_text(None, &step), merge_step(left, right)),
        };
        Ok(match free {
            Some(text) => Prepared::Free(text),
            None => Prepared::Model(NodeRequest {
                context: self.chat.context(part),
                step: step_text,
            }),
        })
    }

    fn save_node(&mut self, part: Part, text: &str) -> anyhow::Result<()> {
        let day = crate::platform::local_time(SystemTime::now())?.date();
        self.store.append_node(
            &NodeRecord {
                l: part.l,
                i: part.i,
                text: text.to_string(),
                size: text.len(),
            },
            &day,
        )?;
        self.chat.insert_node(part, text);
        self.failures.remove(&part);
        Ok(())
    }

    fn built(&mut self, part: Part, result: anyhow::Result<String>) {
        match result.and_then(|text| self.save_node(part, &text)) {
            Ok(()) => self.pump(),
            Err(error) => self.failed(part, &error),
        }
    }

    /// A node failed: report its first failure, keep it busy, and try it
    /// again after [`RETRY`] (forever; no backoff, the next turn waits).
    fn failed(&mut self, part: Part, error: &anyhow::Error) {
        let entry = self.failures.entry(part).or_insert(Failure {
            count: 0,
            error: String::new(),
            generation: 0,
        });
        entry.count += 1;
        entry.generation += 1;
        entry.error = format!("{error:#}");
        if entry.count == 1 {
            tracing::warn!(
                target: "chat_memory",
                "cannot summarize {}+{}: {}; retrying every {} s",
                part.start(),
                part.count(),
                entry.error,
                RETRY.as_secs()
            );
        }
        let generation = entry.generation;
        self.chat.mark_busy(part);
        self.waiting.insert(part);
        let commands = self.commands.clone();
        self.runtime.spawn(async move {
            tokio::time::sleep(RETRY).await;
            let _ = commands.send(Command::Retry { part, generation });
        });
        self.fail_waiters_if_stuck();
    }

    /// A turn waits for the view: answer at once when it is settled; when
    /// the node it waits on is in its retry delay, try it again now.
    fn add_settle_waiter(&mut self, reply: oneshot::Sender<Outcome>) {
        if self.chat.settled() {
            let _ = reply.send(Outcome::Ok(Reply::Settled));
            return;
        }
        self.settle_waiters.retain(|waiter| !waiter.is_closed());
        self.settle_waiters.push(reply);
        let blocking = Part {
            l: 0,
            i: self.chat.first(),
        };
        if self.waiting.remove(&blocking) {
            if let Some(failure) = self.failures.get_mut(&blocking) {
                // Invalidate the pending delayed retry.
                failure.generation += 1;
            }
            self.chat.release(blocking);
            self.pump();
        }
    }

    fn wake_settled(&mut self) {
        if self.settle_waiters.is_empty() || !self.chat.settled() {
            return;
        }
        for waiter in self.settle_waiters.drain(..) {
            let _ = waiter.send(Outcome::Ok(Reply::Settled));
        }
    }

    fn fail_waiters_if_stuck(&mut self) {
        let blocking = Part {
            l: 0,
            i: self.chat.first(),
        };
        let Some(failure) = self.failures.get(&blocking) else {
            return;
        };
        if failure.count < SETTLE_FAILURES {
            return;
        }
        let error = format!(
            "the memory compactor cannot summarize message {} ({} tries): {}; it keeps retrying every {} s",
            blocking.i,
            failure.count,
            failure.error,
            RETRY.as_secs()
        );
        for waiter in self.settle_waiters.drain(..) {
            let _ = waiter.send(Outcome::Error(error.clone()));
        }
    }

    /// Commit the chat with git off the actor thread; a request that comes
    /// while a commit runs commits again after it.
    fn persist(&mut self) {
        if self.persisting {
            self.persist_again = true;
            return;
        }
        self.persisting = true;
        let dir = self.dir.clone();
        let commands = self.commands.clone();
        self.runtime.spawn_blocking(move || {
            let result = commit(&dir, &dir.join(".git"));
            let _ = commands.send(Command::Persisted(result));
        });
    }

    fn persisted(&mut self, result: Result<(), String>) {
        self.persisting = false;
        match result {
            Ok(()) => self.persist_reported = false,
            Err(error) => {
                if !self.persist_reported {
                    self.persist_reported = true;
                    tracing::warn!(target: "chat_memory", "cannot commit the chat: {error}");
                }
            }
        }
        if self.persist_again {
            self.persist_again = false;
            self.persist();
        }
    }
}

enum Prepared {
    Free(String),
    Model(NodeRequest),
}

/// `git add` + `git commit` of the chat directory, initializing the repo on
/// first use. The lock socket is ignored; hooks and signing are off so a
/// global configuration cannot block or prompt in the background.
fn commit(dir: &Path, git_dir: &Path) -> Result<(), String> {
    let git = |args: &[&str]| -> Result<std::process::Output, String> {
        std::process::Command::new("git")
            .arg("-C")
            .arg(dir)
            .args([
                "-c",
                "core.hooksPath=/dev/null",
                "-c",
                "commit.gpgsign=false",
            ])
            .args(args)
            .stdin(std::process::Stdio::null())
            .output()
            .map_err(|error| format!("cannot run git: {error}"))
    };
    let check =
        |output: std::process::Output, what: &str| -> Result<std::process::Output, String> {
            if output.status.success() {
                Ok(output)
            } else {
                Err(format!(
                    "git {what} failed: {}",
                    String::from_utf8_lossy(&output.stderr).trim()
                ))
            }
        };
    if !git_dir.exists() {
        check(git(&["init", "-q"])?, "init")?;
        std::fs::write(dir.join(".gitignore"), "lock\nlock.lock/\n")
            .map_err(|error| format!("cannot write .gitignore: {error}"))?;
    }
    check(git(&["add", "-A"])?, "add")?;
    let status = check(git(&["status", "--porcelain"])?, "status")?;
    if status.stdout.is_empty() {
        return Ok(());
    }
    check(git(&["commit", "-q", "-m", "chat"])?, "commit").map(|_| ())
}

/// A stored ISO date as the local date and time `date(id)` answers:
/// `2026-10-05T09:32:11.123+02:00` reads `2026-10-05 09:32:11 +02:00`; a
/// bare date passes through.
fn display_date(date: &str) -> String {
    let Some((day, time)) = date.split_once('T') else {
        return date.to_string();
    };
    let offset_at = time.find(['+', '-', 'Z']).unwrap_or(time.len());
    let (clock, offset) = time.split_at(offset_at);
    let clock = clock.split('.').next().unwrap_or(clock);
    let offset = if offset == "Z" { "+00:00" } else { offset };
    if offset.is_empty() {
        format!("{day} {clock}")
    } else {
        format!("{day} {clock} {offset}")
    }
}

fn now_millis() -> u64 {
    SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |duration| duration.as_millis() as u64)
}

#[cfg(test)]
mod tests;
