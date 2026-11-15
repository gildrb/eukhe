//! The client side of the chat's `lock` socket: claiming the socket (own
//! it, or reach its live owner), the request connection, and the update
//! subscription connection. A `lock` too long to name an endpoint (an
//! abstract name on Linux: 107 bytes; a socket file on macOS: 103) is a
//! symbolic link to a short endpoint ([`short_endpoint`]).

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Duration;

use eukhe_types::daemon::MemoryUpdate;
use eukhe_types::platform::endpoints::is_socket_file;
use eukhe_types::platform::transport::{
    bind_transport, connect_transport, is_addressable, AsyncReadHalf, AsyncWriteHalf,
    TransportListener, TransportStream, ENDPOINTS_ARE_FILES,
};
use sha2::Digest as _;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader, Lines};
use tokio::sync::oneshot;

use super::{ClientFrame, Outcome, Reply, ReplyFrame, Request};

/// How long a claimer waits for another claimer's takeover lock.
const CLAIM_LOCK_WAIT: Duration = Duration::from_secs(10);
/// Attempts at claiming before a transient connect error is final.
const CLAIM_ATTEMPTS: u32 = 20;

pub(super) enum Claim {
    Owned(Box<dyn TransportListener>),
    Held(Box<dyn TransportStream>),
}

/// Bind `dir/lock`, or reach its live owner. A socket that refuses
/// connections is stale (the OS frees it when its owner dies): it is
/// removed and taken over, as is a link to such a socket. Claimers
/// serialize on a lock directory so two of them never remove each other's
/// fresh socket.
pub(super) async fn claim(dir: &Path) -> anyhow::Result<Claim> {
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
    // An owner of an earlier release listens on a socket file at the path
    // while this build's endpoint is abstract (Linux): reach that owner
    // instead of owning the files beside it; a dead one's file goes.
    if !ENDPOINTS_ARE_FILES && is_socket_file(lock) {
        if let Ok(stream) =
            connect_transport(lock, eukhe_bend::rules::server_peer::PEER_RULES).await
        {
            return Ok(Claim::Held(stream));
        }
        remove_if_present(lock)?;
    }
    match bind_lock(lock).await {
        Ok(listener) => return Ok(Claim::Owned(listener)),
        Err(bind_error) => {
            if io_kind(&bind_error) != Some(std::io::ErrorKind::AddrInUse) {
                return Err(bind_error);
            }
        }
    }
    match connect_lock(lock).await {
        Ok(stream) => Ok(Claim::Held(stream)),
        Err(connect_error) => match io_kind(&connect_error) {
            Some(std::io::ErrorKind::ConnectionRefused | std::io::ErrorKind::NotFound) => {
                remove_if_present(lock)?;
                Ok(Claim::Owned(bind_lock(lock).await?))
            }
            _ => Err(connect_error),
        },
    }
}

/// Bind the chat's endpoint at `lock`, or, for a `lock` too long to name
/// one, at its short endpoint with `lock` a symbolic link to it. An
/// existing `lock` link is in use, as for a bind.
async fn bind_lock(lock: &Path) -> anyhow::Result<Box<dyn TransportListener>> {
    if is_addressable(lock) {
        let listener = bind_transport(lock, eukhe_bend::rules::fsmode::peer_verdict).await?;
        if ENDPOINTS_ARE_FILES {
            crate::platform::restrict_file(lock)?;
        }
        return Ok(listener);
    }
    match std::fs::symlink_metadata(lock) {
        Ok(_) => return Err(std::io::Error::from(std::io::ErrorKind::AddrInUse).into()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => return Err(error.into()),
    }
    let endpoint = short_endpoint(lock)?;
    // No `lock` links to the endpoint: a socket file there is a dead owner's.
    remove_if_present(&endpoint)?;
    let listener = bind_transport(&endpoint, eukhe_bend::rules::fsmode::peer_verdict).await?;
    if ENDPOINTS_ARE_FILES {
        crate::platform::restrict_file(&endpoint)?;
    }
    std::os::unix::fs::symlink(&endpoint, lock)?;
    Ok(listener)
}

/// Connect to the owner behind `lock`: its endpoint, an earlier release's
/// socket file there (Linux binds a long one through its directory), or
/// the short endpoint a `lock` too long to name one links to.
pub(super) async fn connect_lock(lock: &Path) -> anyhow::Result<Box<dyn TransportStream>> {
    let rules = eukhe_bend::rules::server_peer::PEER_RULES;
    if is_addressable(lock) || is_socket_file(lock) {
        return connect_transport(lock, rules).await;
    }
    match std::fs::read_link(lock) {
        Ok(endpoint) => connect_transport(&endpoint, rules).await,
        // Neither a socket file nor a link: nothing listens there.
        Err(error) if error.kind() == std::io::ErrorKind::InvalidInput => {
            Err(std::io::Error::from(std::io::ErrorKind::ConnectionRefused).into())
        }
        Err(error) => Err(error.into()),
    }
}

/// The short endpoint of a `lock` too long to name one: `chat/<hash of the
/// lock's canonical path>` in the run dir (the daemon's socket dir), else
/// in `/tmp/eukhe-<uid>` when even that path is too long (a deep agent
/// dir). Both dirs pass the socket dir check.
fn short_endpoint(lock: &Path) -> anyhow::Result<PathBuf> {
    let dir = lock
        .parent()
        .ok_or_else(|| anyhow::anyhow!("the chat lock {} has no directory", lock.display()))?;
    let canonical = std::fs::canonicalize(dir)?.join("lock");
    let digest = sha2::Sha256::digest(canonical.as_os_str().as_encoded_bytes());
    let name = digest[..8]
        .iter()
        .fold(String::with_capacity(16), |mut name, byte| {
            use std::fmt::Write as _;
            // Writing to a String cannot fail.
            let _ = write!(name, "{byte:02x}");
            name
        });
    let fallback = Path::new("/tmp").join(format!(
        "eukhe-{}",
        eukhe_types::platform::access::current_uid()
    ));
    let base = [eukhe_types::platform::daemon_socket::socket_dir(), fallback]
        .into_iter()
        .find(|base| is_addressable(&base.join("chat").join(&name)))
        .ok_or_else(|| {
            anyhow::anyhow!(
                "no socket dir is short enough for the chat lock {}",
                lock.display()
            )
        })?;
    let chat = base.join("chat");
    crate::platform::socket_dir::prepare_socket_dir(&base)?;
    crate::platform::socket_dir::prepare_socket_dir(&chat)?;
    Ok(chat.join(name))
}

fn remove_if_present(path: &Path) -> std::io::Result<()> {
    match std::fs::remove_file(path) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(error),
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

/// The connection to the owner died; the request may or may not have run.
#[derive(Debug)]
pub(super) struct Disconnected;

type Pending = std::sync::Mutex<HashMap<u64, oneshot::Sender<Outcome>>>;

pub(super) struct Client {
    /// Lines for the writer task, which sends each whole and in order.
    outgoing: tokio::sync::mpsc::UnboundedSender<String>,
    pending: Arc<Pending>,
    closed: Arc<AtomicBool>,
    next_id: AtomicU64,
    reader: tokio::task::JoinHandle<()>,
    writer: tokio::task::JoinHandle<()>,
}

impl Drop for Client {
    fn drop(&mut self) {
        self.reader.abort();
        self.writer.abort();
    }
}

impl Client {
    pub(super) fn connect(stream: Box<dyn TransportStream>) -> Arc<Client> {
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
                    // A reply with no waiter answers a posted release or a
                    // request whose requester stopped waiting.
                    if let Some(waiter) = waiter {
                        // The requester may be stopping right now.
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
        let (outgoing, lines) = tokio::sync::mpsc::unbounded_channel();
        Arc::new(Client {
            outgoing,
            pending,
            closed,
            next_id: AtomicU64::new(1),
            reader,
            writer: tokio::spawn(write_lines(write_half, lines)),
        })
    }

    /// Whether the connection to the owner is gone.
    pub(super) fn is_closed(&self) -> bool {
        self.closed.load(Ordering::SeqCst)
    }

    /// Queue one frame for the writer task.
    fn send(&self, frame: &ClientFrame) -> Result<(), Disconnected> {
        let mut line = serde_json::to_string(frame).map_err(|_| Disconnected)?;
        line.push('\n');
        self.outgoing.send(line).map_err(|_| Disconnected)
    }

    /// Send `request` and wait for its outcome. Dropping the future tells
    /// the owner to drop the wait.
    pub(super) async fn request(&self, request: &Request) -> Result<Outcome, Disconnected> {
        let id = self.next_id.fetch_add(1, Ordering::SeqCst);
        let (sender, receiver) = oneshot::channel();
        self.pending
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .insert(id, sender);
        let sent = if self.is_closed() {
            Err(Disconnected)
        } else {
            self.send(&ClientFrame::Request {
                id,
                request: request.clone(),
            })
        };
        if let Err(error) = sent {
            self.pending
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .remove(&id);
            return Err(error);
        }
        let mut cancel = CancelOnDrop {
            client: self,
            id: Some(id),
        };
        let outcome = receiver.await.map_err(|_| Disconnected);
        cancel.id = None;
        outcome
    }
}

/// A request's waiter on the client side: when its future is dropped
/// before the reply, the owner is told to drop the wait.
struct CancelOnDrop<'a> {
    client: &'a Client,
    /// `None` once the reply came (or the connection died).
    id: Option<u64>,
}

impl Drop for CancelOnDrop<'_> {
    fn drop(&mut self) {
        let Some(id) = self.id else {
            return;
        };
        self.client
            .pending
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .remove(&id);
        // A closed connection has no waits left at the owner.
        let _ = self.client.send(&ClientFrame::Cancel { id });
    }
}

/// Write queued lines in order until the queue closes or the peer goes
/// away. One task owns the write half, so a sender that is cancelled never
/// leaves half a line on the socket.
pub(super) async fn write_lines(
    mut writer: Box<dyn AsyncWriteHalf>,
    mut lines: tokio::sync::mpsc::UnboundedReceiver<String>,
) {
    while let Some(line) = lines.recv().await {
        let written = match writer.write_all(line.as_bytes()).await {
            Ok(()) => writer.flush().await,
            Err(error) => Err(error),
        };
        if written.is_err() {
            // The peer went away; the reading side sees the connection end.
            return;
        }
    }
}

/// The request id of a subscription on its own connection.
const SUBSCRIPTION_ID: u64 = 1;

/// A connection of its own to the owner that carries its updates: one
/// `subscribe` request, then one reply frame per update, all under the
/// request's id, until either side hangs up.
pub(super) struct Subscription {
    lines: Lines<BufReader<Box<dyn AsyncReadHalf>>>,
    /// Held open: dropping the write half ends the subscription.
    writer: Box<dyn AsyncWriteHalf>,
}

impl Subscription {
    /// Connect to the owner of `dir` and subscribe; returns once the owner
    /// registered the subscription.
    ///
    /// # Errors
    ///
    /// Returns an error when the owner cannot be reached or refuses.
    pub(super) async fn open(dir: &Path) -> anyhow::Result<Subscription> {
        let stream = connect_lock(&dir.join("lock")).await?;
        let (read_half, mut writer) = stream.split();
        let mut line = serde_json::to_string(&ClientFrame::Request {
            id: SUBSCRIPTION_ID,
            request: Request::Subscribe,
        })?;
        line.push('\n');
        writer.write_all(line.as_bytes()).await?;
        writer.flush().await?;
        let mut lines = BufReader::new(read_half).lines();
        let ack = lines
            .next_line()
            .await?
            .ok_or_else(|| anyhow::anyhow!("the chat owner hung up on a subscription"))?;
        let frame: ReplyFrame = serde_json::from_str(&ack)?;
        match (frame.id, frame.outcome) {
            (SUBSCRIPTION_ID, Outcome::Ok(Reply::Subscribed)) => Ok(Subscription { lines, writer }),
            (_, Outcome::Error(error)) => Err(anyhow::anyhow!(
                "the chat owner refused a subscription: {error}"
            )),
            (id, Outcome::Ok(reply)) => Err(anyhow::anyhow!(
                "unexpected chat memory reply to subscription {id}: {reply:?}"
            )),
        }
    }

    /// The next update; `None` once the owner hung up or answered with
    /// anything but an update.
    pub(super) async fn next(&mut self) -> Option<MemoryUpdate> {
        let line = self.lines.next_line().await.ok()??;
        let frame = serde_json::from_str::<ReplyFrame>(&line).ok()?;
        if let (SUBSCRIPTION_ID, Outcome::Ok(Reply::Update { update })) = (frame.id, frame.outcome)
        {
            return Some(update);
        }
        // The owner refused (an older owner, or an error): this connection
        // carries nothing more.
        let _ = self.writer.shutdown().await;
        None
    }
}
