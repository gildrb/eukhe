//! The chat's single owner and its clients (spec §1 "One process owns a
//! chat", §4 the compactor, §6 the turn's wait).
//!
//! The first process that binds `chat/lock` owns the chat for its whole
//! life: it loads the files and the saved view, runs the compactor, and is
//! the only writer. Every other process connects to the same socket and
//! sends JSON-line requests. When the owner dies, its socket refuses
//! connections: the next request deletes the stale socket and takes
//! ownership over.
//!
//! A turn's view comes from one owner step: the owner answers
//! [`Memory::settled_render`] in the same step that sees every view line
//! built, so no append can slip a placeholder in between (§6). Many
//! windows are one chat, and its root turns run one at a time: the owner
//! hands out the root-turn lease ([`turn`]).
//!
//! The owner handles one connection's requests in the order they arrive.
//! A client that stops waiting for a reply says so, and the owner drops
//! the wait. A subscriber gets the compactor's progress
//! ([`MemoryUpdate`]) on a connection of its own.

mod actor;
mod client;
mod owner;
mod prefix_gate;
#[cfg(test)]
mod tests;
mod turn;

use std::path::{Path, PathBuf};
use std::sync::atomic::AtomicU64;
use std::sync::Arc;
use std::time::{Duration, SystemTime};

use eukhe_types::daemon::MemoryUpdate;
use eukhe_types::pi_ai::ImageContent;
use eukhe_types::platform::transport::connect_transport;
use tokio::sync::Mutex;

use super::compactor::Summarizer;
use super::saved::CompactionPrompt;
use super::view::pieces;
use super::{AppendKey, Kind};
use client::{claim, Claim, Client, Disconnected, Subscription};
use owner::OwnerHandle;

pub use turn::TurnLease;

/// How long a subscription waits before it reconnects to a new owner.
const RESUBSCRIBE_DELAY: Duration = Duration::from_millis(250);

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
    /// The view cut after its last whole block of [`super::BLOCK`] lines:
    /// the first piece carries the view's cache mark (§3.3).
    #[must_use]
    pub fn pieces(&self) -> Vec<String> {
        pieces(&self.text)
    }
}

/// What `zoom` gives: lines or a message as text, and the images of a
/// message zoomed whole (§5: `zoom(id, 1)` gives message id whole, with its
/// images).
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Zoomed {
    pub text: String,
    pub images: Vec<ImageContent>,
}

/// What a keyed append ([`Memory::append_keyed`]) did.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KeyedAppend {
    /// Logged now, as this message id.
    Written(u64),
    /// The log already held the key: nothing written. The id is the newest
    /// message of the key's scope.
    AlreadyLogged(u64),
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
    /// Compactor calls running, waiting for their prefix's writer, or
    /// failed and waiting to be tried again.
    pub running: u64,
    /// The newest unresolved failure: saving the view, else the compactor.
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

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "op", rename_all = "snake_case", rename_all_fields = "camelCase")]
enum Request {
    /// Log one message. `dedupe` re-sends after a lost connection: a copy
    /// with the same kind, date and text among the newest messages is
    /// answered instead of written twice. A `key` makes the append
    /// idempotent across processes and restarts: a key at or below its
    /// scope's newest logged key is answered `AlreadyAppended`.
    Append {
        kind: Kind,
        text: String,
        date: String,
        dedupe: bool,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        key: Option<AppendKey>,
        /// The images the message carried, kept beside the log.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        images: Vec<ImageContent>,
    },
    /// Log a batch at once (all or nothing).
    Import {
        items: Vec<ImportItem>,
    },
    /// Wait until every line of the view is a summary, then render it in
    /// the same owner step; after `within_ms`, render it as it is, each
    /// line not built yet as its input cut to [`super::NODE`] bytes (H2.3).
    SettledRender {
        #[serde(default = "default_settle_ms")]
        within_ms: u64,
    },
    /// The view as it is now, placeholders included.
    Render,
    Zoom {
        id: u64,
        count: u64,
    },
    Date {
        id: u64,
    },
    /// One level of the tree for a reader: the view's lines (`node`
    /// `None`), or what line `node` opens into.
    Tree {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        node: Option<eukhe_types::daemon::MemoryZoom>,
    },
    Status,
    Persist,
    Parts,
    /// Wait for the root-turn lease; `lease` names it on this connection.
    AcquireTurn {
        lease: u64,
    },
    /// End lease `lease` of this connection, held or still waited for.
    Release {
        lease: u64,
    },
    /// Compactions reuse this system prompt and these tools from now on
    /// (a root turn reports its own, §4).
    SetPrompt {
        prompt: CompactionPrompt,
    },
    /// Stream every update on this connection, as `Update` replies under
    /// the request's id, until it closes.
    Subscribe,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(
    tag = "reply",
    rename_all = "snake_case",
    rename_all_fields = "camelCase"
)]
enum Reply {
    Appended {
        id: u64,
    },
    /// A keyed append whose key the log already holds: nothing written;
    /// `id` is the newest message of the key's scope.
    AlreadyAppended {
        id: u64,
    },
    Imported {
        first: u64,
        count: u64,
    },
    Rendered {
        view: RenderedView,
    },
    Text {
        text: String,
    },
    Zoomed {
        zoomed: Zoomed,
    },
    Status {
        status: MemoryStatus,
    },
    Tree {
        level: eukhe_types::daemon::MemoryTreeLevel,
    },
    Persisting,
    Parts {
        parts: Vec<(u32, u64)>,
    },
    Granted,
    Released,
    PromptSet,
    /// A subscription is registered: every update from here on reaches
    /// it, and so does the effect of any request sent after this reply.
    Subscribed,
    /// One update of a subscription.
    Update {
        update: MemoryUpdate,
    },
}

/// One line a client sends.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
#[serde(tag = "frame", rename_all = "snake_case")]
enum ClientFrame {
    Request {
        id: u64,
        request: Request,
    },
    /// The client stopped waiting for request `id`: the owner drops the
    /// wait.
    Cancel {
        id: u64,
    },
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
    /// Names this handle's turn leases (see [`Memory::acquire_turn`]).
    next_lease: AtomicU64,
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
                next_lease: AtomicU64::new(1),
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
                key: None,
                images: Vec::new(),
            })
            .await?
        {
            Reply::Appended { id } => Ok(id),
            other => Err(unexpected(&other)),
        }
    }

    /// Log one message once per `key` (written and fsynced before this
    /// returns), with the images it carried: the owner answers
    /// [`KeyedAppend::AlreadyLogged`] when the log already holds a message
    /// of the key's scope at or past `key.seq`, across owner restarts too
    /// (the key is stored on the line). A logger that numbers its messages
    /// per scope in order may so re-send what it is unsure about after a
    /// crash.
    ///
    /// # Errors
    ///
    /// Returns an error when the message cannot be written.
    pub async fn append_keyed(
        &self,
        kind: Kind,
        text: &str,
        images: Vec<ImageContent>,
        key: AppendKey,
    ) -> anyhow::Result<KeyedAppend> {
        let date = crate::platform::local_time(SystemTime::now())?.rfc3339();
        match self
            .request(Request::Append {
                kind,
                text: text.to_string(),
                date,
                dedupe: false,
                key: Some(key),
                images,
            })
            .await?
        {
            Reply::Appended { id } => Ok(KeyedAppend::Written(id)),
            Reply::AlreadyAppended { id } => Ok(KeyedAppend::AlreadyLogged(id)),
            other => Err(unexpected(&other)),
        }
    }

    /// The view once every line of it is a summary (§6), rendered in the
    /// same owner step that sees it so, so no append slips a placeholder in
    /// between. Once `within` passes, the view as it is: each line not
    /// built yet shows its input cut to [`super::NODE`] bytes, never a
    /// placeholder (H2.3). Dropping the future cancels the wait, across
    /// processes too.
    ///
    /// # Errors
    ///
    /// Returns an error when the owner cannot be reached or cannot read
    /// the log.
    #[tracing::instrument(name = "chat_memory.settled_render", skip_all)]
    pub async fn settled_render(&self, within: Duration) -> anyhow::Result<RenderedView> {
        let within_ms = u64::try_from(within.as_millis()).unwrap_or(u64::MAX);
        match self.request(Request::SettledRender { within_ms }).await? {
            Reply::Rendered { view } => Ok(view),
            other => Err(unexpected(&other)),
        }
    }

    /// The view as it is now: a line not summarized yet shows the
    /// placeholder. A turn reads [`Memory::settled_render`] instead.
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
    /// with its images when `n = 1`, or `No line id+n.`.
    ///
    /// # Errors
    ///
    /// Returns an error when the message or its images cannot be read back
    /// or the owner cannot be reached.
    pub async fn zoom(&self, id: u64, count: u64) -> anyhow::Result<Zoomed> {
        match self.request(Request::Zoom { id, count }).await? {
            Reply::Zoomed { zoomed } => Ok(zoomed),
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

    /// One level of the memory tree for a reader (the `/memory` tree, the
    /// dashboard): the view's lines when `node` is `None`, else the two
    /// lines under `node`, or its message when it covers one; every line
    /// dated, with its kinds and its summary when built. Reads only.
    ///
    /// # Errors
    ///
    /// Returns an error when the owner cannot be reached or a message
    /// cannot be read back.
    pub async fn tree(
        &self,
        node: Option<eukhe_types::daemon::MemoryZoom>,
    ) -> anyhow::Result<eukhe_types::daemon::MemoryTreeLevel> {
        match self.request(Request::Tree { node }).await? {
            Reply::Tree { level } => Ok(level),
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

    /// Commit the chat directory with git in the background (eukhe's own
    /// backup, beside the spec); failures are reported by the owner.
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

    /// Compactions reuse `prompt` from now on (§4): the system prompt and
    /// tools of the root turns, so each compaction reads them from the
    /// turns' cache entry. Saved, so a restarted owner keeps it.
    ///
    /// # Errors
    ///
    /// Returns an error when the prompt cannot be saved or the owner
    /// cannot be reached.
    pub async fn set_compaction_prompt(&self, prompt: CompactionPrompt) -> anyhow::Result<()> {
        match self.request(Request::SetPrompt { prompt }).await? {
            Reply::PromptSet => Ok(()),
            other => Err(unexpected(&other)),
        }
    }

    /// The compactor's progress from now on, from whichever process owns
    /// the chat (display only: never log an update or send it to a model).
    ///
    /// # Errors
    ///
    /// Returns an error when the owner can be neither reached nor become
    /// this process.
    pub async fn subscribe(&self) -> anyhow::Result<MemoryUpdates> {
        Ok(MemoryUpdates {
            source: self.update_source().await?,
            memory: self.clone(),
        })
    }

    async fn update_source(&self) -> anyhow::Result<UpdateSource> {
        for _ in 0..4 {
            match self.link().await? {
                Link::Owner(owner) => return owner.subscribe().map(UpdateSource::Local),
                Link::Client(client) => match Subscription::open(&self.inner.dir).await {
                    Ok(subscription) => return Ok(UpdateSource::Remote(subscription)),
                    // The owner is gone: take over or reach the next one.
                    Err(_) => self.forget(&client).await,
                },
            }
        }
        anyhow::bail!(
            "the chat memory at {} keeps losing its owner",
            self.inner.dir.display()
        )
    }

    /// Log a batch at once. Returns the first id and the count.
    pub(crate) async fn import(&self, items: Vec<ImportItem>) -> anyhow::Result<(u64, u64)> {
        match self.request(Request::Import { items }).await? {
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
                            // A lease belongs to its connection: it ended with it.
                            Request::AcquireTurn { .. } | Request::Release { .. } => anyhow::bail!(
                                "the chat owner went away during a turn lease request"
                            ),
                            // A subscription has its own connection.
                            Request::Subscribe => anyhow::bail!(
                                "the chat owner went away during a subscription request"
                            ),
                            Request::SettledRender { .. }
                            | Request::Render
                            | Request::Zoom { .. }
                            | Request::Date { .. }
                            | Request::Tree { .. }
                            | Request::Status
                            | Request::Persist
                            | Request::Parts
                            | Request::SetPrompt { .. } => {}
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

    /// Drop the client link when its connection is gone, so the next
    /// request takes over or reaches the next owner.
    async fn forget_if_closed(&self) {
        let mut slot = self.inner.link.lock().await;
        if matches!(slot.as_ref(), Some(Link::Client(current)) if current.is_closed()) {
            *slot = None;
        }
    }
}

/// The compactor's progress ([`Memory::subscribe`]): it follows the chat
/// across owner changes (an update sent while the owner changed hands is
/// lost).
pub struct MemoryUpdates {
    memory: Memory,
    source: UpdateSource,
}

enum UpdateSource {
    /// This process owns the chat.
    Local(tokio::sync::mpsc::UnboundedReceiver<MemoryUpdate>),
    /// Another process does.
    Remote(Subscription),
}

impl std::fmt::Debug for MemoryUpdates {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("MemoryUpdates")
            .field("memory", &self.memory)
            .finish_non_exhaustive()
    }
}

impl MemoryUpdates {
    /// The next update.
    ///
    /// # Errors
    ///
    /// Returns an error when, after the owner went away, the chat can be
    /// neither reached nor owned.
    pub async fn next(&mut self) -> anyhow::Result<MemoryUpdate> {
        loop {
            let update = match &mut self.source {
                UpdateSource::Local(updates) => updates.recv().await,
                UpdateSource::Remote(subscription) => subscription.next().await,
            };
            if let Some(update) = update {
                return Ok(update);
            }
            tokio::time::sleep(RESUBSCRIBE_DELAY).await;
            self.memory.forget_if_closed().await;
            self.source = self.memory.update_source().await?;
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

/// The settle deadline of a request from a client that names none.
fn default_settle_ms() -> u64 {
    u64::try_from(super::SETTLE_TIMEOUT.as_millis()).unwrap_or(u64::MAX)
}
