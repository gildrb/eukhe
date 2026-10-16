//! The owner's entry points: the actor thread's command channel, and the
//! task serving the other processes on the `lock` socket.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::{mpsc, Arc};
use std::time::Duration;

use eukhe_types::daemon::MemoryUpdate;
use eukhe_types::platform::transport::{TransportListener, TransportStream};
use tokio::io::{AsyncBufReadExt, BufReader};
use tokio::sync::oneshot;

use super::actor::Actor;
use super::client::write_lines;
use super::turn::Origin;
use super::{ClientFrame, Outcome, Reply, ReplyFrame, Request, Summarizer};
use crate::memory::view::Part;

/// The largest request or reply line accepted on the socket.
const MAX_LINE_BYTES: usize = 64 * 1024 * 1024;

pub(super) struct OwnerHandle {
    commands: mpsc::Sender<Command>,
    server: tokio::task::JoinHandle<()>,
    actor: Option<std::thread::JoinHandle<()>>,
    lock: PathBuf,
    identity: Option<eukhe_types::daemon::SocketIdentity>,
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
            && eukhe_types::platform::socket_identity(&self.lock) == self.identity
        {
            // Already gone is fine: the next claimer binds a fresh one.
            let _ = std::fs::remove_file(&self.lock);
        }
    }
}

pub(super) enum Command {
    Request {
        origin: Origin,
        request: Request,
        reply: oneshot::Sender<Outcome>,
    },
    /// Send every update from now on to `sender`, until it closes.
    Subscribe {
        sender: tokio::sync::mpsc::UnboundedSender<MemoryUpdate>,
    },
    /// A client connection closed: its leases end.
    Closed {
        connection: u64,
    },
    /// The response of node `part`'s call number `build` has started: its
    /// prefix is cached, so the calls waiting for it may go (§3.3).
    Started {
        part: Part,
        build: u64,
    },
    /// Node `part`'s call number `build` ended; `input` is the node's input,
    /// which the failure cap cuts (H1.5).
    Built {
        part: Part,
        build: u64,
        result: anyhow::Result<String>,
        input: String,
    },
    Retry {
        part: Part,
        generation: u64,
    },
    Persisted(Result<(), String>),
    Shutdown,
}

impl OwnerHandle {
    pub(super) async fn start(
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
        let identity = eukhe_types::platform::socket_identity(&lock);
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

    pub(super) async fn request(&self, request: Request) -> anyhow::Result<Reply> {
        let (reply, receiver) = oneshot::channel();
        self.commands
            .send(Command::Request {
                origin: Origin::Local,
                request,
                reply,
            })
            .map_err(|_| anyhow::anyhow!("the chat memory actor has stopped"))?;
        match receiver
            .await
            .map_err(|_| anyhow::anyhow!("the chat memory actor stopped before replying"))?
        {
            Outcome::Ok(reply) => Ok(reply),
            Outcome::Error(error) => Err(anyhow::anyhow!(error)),
        }
    }

    /// Every update from now on, in this process.
    pub(super) fn subscribe(
        &self,
    ) -> anyhow::Result<tokio::sync::mpsc::UnboundedReceiver<MemoryUpdate>> {
        let (sender, receiver) = tokio::sync::mpsc::unbounded_channel();
        self.commands
            .send(Command::Subscribe { sender })
            .map_err(|_| anyhow::anyhow!("the chat memory actor has stopped"))?;
        Ok(receiver)
    }

    /// Send `request` without waiting for its reply (the actor may have
    /// stopped: then nothing is left to do).
    pub(super) fn post(&self, request: Request) {
        let (reply, _) = oneshot::channel();
        let _ = self.commands.send(Command::Request {
            origin: Origin::Local,
            request,
            reply,
        });
    }
}

/// Accept clients until the owner goes away. Every connection task lives
/// in a `JoinSet` owned by this one: aborting the server closes them all.
async fn serve(listener: Box<dyn TransportListener>, commands: mpsc::Sender<Command>) {
    let mut connections = tokio::task::JoinSet::new();
    let mut next_connection: u64 = 0;
    loop {
        // Reap finished connections so the set does not grow forever.
        while connections.try_join_next().is_some() {}
        let Ok(stream) = listener.accept().await else {
            // Accept errors are transient (descriptor exhaustion, aborted
            // handshakes); keep serving after a short pause.
            tokio::time::sleep(Duration::from_millis(100)).await;
            continue;
        };
        next_connection += 1;
        connections.spawn(serve_connection(stream, commands.clone(), next_connection));
    }
}

/// One client connection: JSON-line frames in, replies out by id. Its
/// requests reach the actor in the order they arrive (a lease's release
/// never overtakes its request); each reply is awaited on its own task, so
/// a waiting request never blocks the connection, and a cancelled one
/// drops its wait. A `subscribe` request streams every update under its
/// id. When the client hangs up, the actor ends its leases.
async fn serve_connection(
    stream: Box<dyn TransportStream>,
    commands: mpsc::Sender<Command>,
    connection: u64,
) {
    let (read_half, write_half) = stream.split();
    let (replies, lines) = tokio::sync::mpsc::unbounded_channel();
    let mut tasks = tokio::task::JoinSet::new();
    tasks.spawn(write_lines(write_half, lines));
    let mut waits: HashMap<u64, tokio::task::AbortHandle> = HashMap::new();
    let mut reader = BufReader::new(read_half);
    let mut line = String::new();
    loop {
        while tasks.try_join_next().is_some() {}
        waits.retain(|_, wait| !wait.is_finished());
        line.clear();
        match reader.read_line(&mut line).await {
            Ok(0) | Err(_) => break,
            Ok(read) if read > MAX_LINE_BYTES => break,
            Ok(_) => {}
        }
        let Ok(frame) = serde_json::from_str::<ClientFrame>(line.trim_end()) else {
            // Not a chat client: close the connection at once so a foreign
            // prober never waits on it.
            break;
        };
        match frame {
            ClientFrame::Cancel { id } => {
                // Dropping the reply's receiver drops the actor's waiter.
                if let Some(wait) = waits.remove(&id) {
                    wait.abort();
                }
            }
            ClientFrame::Request {
                id,
                request: Request::Subscribe,
            } => {
                let (sender, mut updates) = tokio::sync::mpsc::unbounded_channel();
                if commands.send(Command::Subscribe { sender }).is_err() {
                    break;
                }
                let replies = replies.clone();
                let stream = tasks.spawn(async move {
                    // The actor takes commands in order: whatever the client
                    // asks after this acknowledgement comes after the
                    // subscription.
                    let mut reply = Reply::Subscribed;
                    loop {
                        let frame = ReplyFrame {
                            id,
                            outcome: Outcome::Ok(reply),
                        };
                        let Ok(mut line) = serde_json::to_string(&frame) else {
                            return;
                        };
                        line.push('\n');
                        if replies.send(line).is_err() {
                            return;
                        }
                        let Some(update) = updates.recv().await else {
                            return;
                        };
                        reply = Reply::Update { update };
                    }
                });
                waits.insert(id, stream);
            }
            ClientFrame::Request { id, request } => {
                let (reply, receiver) = oneshot::channel();
                let sent = commands.send(Command::Request {
                    origin: Origin::Connection(connection),
                    request,
                    reply,
                });
                if sent.is_err() {
                    // The actor stopped: hang up so the client fails over.
                    break;
                }
                let replies = replies.clone();
                let wait = tasks.spawn(async move {
                    let outcome = receiver.await.unwrap_or_else(|_| {
                        Outcome::Error("the chat memory actor stopped before replying".to_string())
                    });
                    let Ok(mut reply) = serde_json::to_string(&ReplyFrame { id, outcome }) else {
                        return;
                    };
                    reply.push('\n');
                    // A client that went away loses only its own reply.
                    let _ = replies.send(reply);
                });
                waits.insert(id, wait);
            }
        }
    }
    // The client hung up: its leases end (a stopped actor holds none), and
    // its pending replies have no reader.
    let _ = commands.send(Command::Closed { connection });
    tasks.abort_all();
}
