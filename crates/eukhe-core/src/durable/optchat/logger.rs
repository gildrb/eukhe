//! The post-commit chat logger of a root session (§7, §9). It follows the
//! committed entries of the session's root conversations and appends what
//! each adds to the chat log, in commit order:
//!
//! - Idempotent across crashes: line `n` of a conversation is appended with
//!   the key `(session/conversation, n)` (the chat owner answers a key it
//!   holds without writing), and the cursor `eukhe.optchat.logged {through,
//!   lines}` is committed after each batch. A crash between the append and
//!   the cursor re-sends the batch with the same keys.
//! - A run's own entries wait until its call has pinned its view: the view
//!   covers everything before the run and nothing of it (§6). A call waits
//!   for the entries before its run ([`OptChat::flush`]) before rendering.
//! - Every append happens under the chat's root-turn lease. When every root
//!   conversation of the session is idle and logged, the chat is persisted
//!   (git) and the lease goes back to the owner; also when the session
//!   closes.

use std::collections::BTreeSet;
use std::sync::Arc;

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::harness::Harness;
use eukhe_durable::session::{SessionError, SessionResult, Unsubscribe};
use eukhe_durable::types::{
    CommitChange, CommitPublication, ConversationId, ConversationQuery, Cursor,
    DocumentCommitChange, EntryId, EntryQuery, EntryRecord,
};
use futures::future::BoxFuture;
use futures::FutureExt;
use tokio::sync::{mpsc, oneshot};
use tokio::task::JoinHandle;

use super::docs::{decode, write, LoggedState, CALL_DOC, LOGGED_DOC};
use super::lines::entry_lines;
use super::request::{call_state, live_run, run_key, run_start};
use super::tools::memory_error;
use super::OptChat;
use crate::memory::{AppendKey, RETRY};

const SCAN_PAGE_SIZE: usize = 256;

/// What the logger is asked.
pub(super) enum LoggerRequest {
    /// Log everything the root conversations' runs do not hold back;
    /// answered once done.
    Flush,
}

enum Command {
    /// Look at the committed state again.
    Wake,
    /// A root conversation was created.
    Follow(ConversationId),
    Request(LoggerRequest, oneshot::Sender<Result<(), String>>),
    /// Log what is held under a lease this session already has, give the
    /// lease back, and stop.
    Stop(oneshot::Sender<()>),
}

/// A cheap handle on the running logger.
#[derive(Clone)]
pub(super) struct LoggerLink {
    commands: mpsc::UnboundedSender<Command>,
}

impl LoggerLink {
    pub(super) fn wake(&self) {
        // A stopped logger has nothing left to look at.
        let _ = self.commands.send(Command::Wake);
    }

    pub(super) async fn request(&self, request: LoggerRequest) -> SessionResult<()> {
        let (reply, answer) = oneshot::channel();
        self.commands
            .send(Command::Request(request, reply))
            .map_err(|_| stopped())?;
        answer
            .await
            .map_err(|_| stopped())?
            .map_err(SessionError::error)
    }
}

fn stopped() -> SessionError {
    SessionError::error("the chat logger has stopped")
}

/// The running logger: stop it before the Harness closes.
pub(crate) struct LoggerHandle {
    chat: Arc<OptChat>,
    link: LoggerLink,
    task: JoinHandle<()>,
    subscriptions: Vec<Unsubscribe>,
}

impl LoggerHandle {
    /// Stop following commits, log what this session's held lease allows,
    /// and give the lease back.
    pub(crate) fn stop(self) -> BoxFuture<'static, ()> {
        async move {
            for subscription in &self.subscriptions {
                subscription.unsubscribe();
            }
            let (done, stopped) = oneshot::channel();
            if self.link.commands.send(Command::Stop(done)).is_ok() {
                // A logger that already ended has released its lease.
                let _ = stopped.await;
            }
            if let Err(error) = self.task.await {
                tracing::warn!(target: "chat_memory", "the chat logger task failed: {error}");
            }
            self.chat.set_link(None);
        }
        .boxed()
    }
}

/// Start the logger: follow the session's root conversations from their
/// cursors (a root conversation without one starts at its newest entry: its
/// history predates the chat memory), then every commit.
pub(super) async fn start(chat: Arc<OptChat>, harness: Harness) -> SessionResult<LoggerHandle> {
    let cx = BACKGROUND_CONTEXT.clone();
    chat.turn.lock().await.open();
    let mut followed = BTreeSet::new();
    for conversation in root_conversations(&harness, &cx).await? {
        if harness
            .snapshot(&LOGGED_DOC, conversation, &cx)
            .await?
            .is_none()
        {
            let through = newest_entry(&harness, conversation, &cx).await?;
            commit_cursor(
                &harness,
                conversation,
                LoggedState { through, lines: 0 },
                &cx,
            )
            .await?;
        }
        followed.insert(conversation);
    }
    let (commands, receiver) = mpsc::unbounded_channel();
    let link = LoggerLink { commands };
    let listener_link = link.clone();
    let commits = harness.subscribe_commits(Arc::new(
        move |publication: &CommitPublication, _cx: &Context| {
            for change in &publication.changes {
                if let CommitChange::Conversation(record) = change {
                    if record.owner.is_none() {
                        let _ = listener_link.commands.send(Command::Follow(record.id));
                    }
                }
            }
            if publication.changes.iter().any(wakes) {
                listener_link.wake();
            }
        },
    ))?;
    let close_link = link.clone();
    let close = harness.subscribe_close(Arc::new(move || {
        let (done, _ignored) = oneshot::channel();
        let _ = close_link.commands.send(Command::Stop(done));
    }))?;
    let logger = Logger {
        chat: Arc::clone(&chat),
        harness,
        followed,
        dirty: false,
        cx,
    };
    let task = tokio::spawn(logger.run(receiver));
    chat.set_link(Some(link.clone()));
    link.wake();
    Ok(LoggerHandle {
        chat,
        link,
        task,
        subscriptions: vec![commits, close],
    })
}

/// Whether a committed change can give the logger work: an entry, a run
/// starting or ending, a call pinning its view, a new conversation.
fn wakes(change: &CommitChange) -> bool {
    match change {
        CommitChange::Entry(_) | CommitChange::Conversation(_) => true,
        CommitChange::Document(DocumentCommitChange::Document { record, .. }) => {
            record.kind == "pi.live" || record.kind == CALL_DOC.definition().kind
        }
        CommitChange::Document(DocumentCommitChange::Copy { .. })
        | CommitChange::Task(_)
        | CommitChange::Submission(_) => false,
    }
}

/// How a pass may take the lease.
#[derive(Clone, Copy, PartialEq, Eq)]
enum PassMode {
    /// Wait for the lease when there is something to log.
    Normal,
    /// Closing: log only under a lease this session already holds.
    Closing,
}

struct Logger {
    chat: Arc<OptChat>,
    harness: Harness,
    followed: BTreeSet<ConversationId>,
    /// Lines appended since the chat was last persisted.
    dirty: bool,
    cx: Context,
}

impl Logger {
    async fn run(mut self, mut receiver: mpsc::UnboundedReceiver<Command>) {
        let mut retry_at: Option<tokio::time::Instant> = None;
        loop {
            let first = match retry_at {
                Some(at) => tokio::select! {
                    command = receiver.recv() => command,
                    () = tokio::time::sleep_until(at) => Some(Command::Wake),
                },
                None => receiver.recv().await,
            };
            let Some(first) = first else {
                break;
            };
            let mut waiters = Vec::new();
            let mut stop = None;
            let mut next = Some(first);
            while let Some(command) = next {
                match command {
                    Command::Wake => {}
                    Command::Follow(conversation) => {
                        self.followed.insert(conversation);
                    }
                    Command::Request(LoggerRequest::Flush, reply) => waiters.push(reply),
                    Command::Stop(done) => stop = Some(done),
                }
                next = receiver.try_recv().ok();
            }
            if let Some(done) = stop {
                for waiter in waiters {
                    let _ = waiter.send(Err("the chat logger has stopped".to_string()));
                }
                self.close().await;
                let _ = done.send(());
                return;
            }
            let passed = self.pass(PassMode::Normal).await;
            retry_at = match &passed {
                Ok(()) => None,
                Err(error) => {
                    tracing::warn!(target: "chat_memory", "cannot log to the chat: {error}");
                    Some(tokio::time::Instant::now() + RETRY)
                }
            };
            let answer = passed.map_err(|error| error.to_string());
            for waiter in waiters {
                // The asking call may have been aborted meanwhile.
                let _ = waiter.send(answer.clone());
            }
        }
        self.close().await;
    }

    /// Log what the held lease allows, persist, and give the lease back.
    async fn close(&mut self) {
        if let Err(error) = self.pass(PassMode::Closing).await {
            tracing::warn!(target: "chat_memory", "cannot log to the chat at close: {error}");
        }
        let mut state = self.chat.turn.lock().await;
        if state.held() && self.dirty {
            if let Err(error) = self.chat.memory.persist().await {
                tracing::warn!(target: "chat_memory", "cannot persist the chat: {error:#}");
            }
            self.dirty = false;
        }
        if let Err(error) = state.close().await {
            tracing::warn!(target: "chat_memory", "cannot release the chat's turn: {error:#}");
        }
    }

    /// Log every followed conversation up to what its run holds back; then,
    /// when every root conversation is idle and logged, persist and give
    /// the lease back. The decision reads the runs under the lease lock: a
    /// call that finds the lease held there runs while its run is live, so
    /// the lease stays.
    async fn pass(&mut self, mode: PassMode) -> SessionResult<()> {
        let chat = Arc::clone(&self.chat);
        loop {
            let followed: Vec<ConversationId> = self.followed.iter().copied().collect();
            for conversation in followed {
                if !self.log_conversation(conversation, &chat, mode).await? {
                    return Ok(());
                }
            }
            if mode == PassMode::Closing {
                return Ok(());
            }
            let mut state = chat.turn.lock().await;
            if !state.held() {
                return Ok(());
            }
            for &conversation in &self.followed {
                if live_run(&self.harness, conversation, &self.cx)
                    .await?
                    .is_some()
                {
                    return Ok(());
                }
            }
            if self.pending().await? {
                // An entry landed after this pass looked: log it before the
                // lease goes back.
                continue;
            }
            if self.dirty {
                chat.memory
                    .persist()
                    .await
                    .map_err(|error| memory_error(&error))?;
                self.dirty = false;
            }
            return state.release().await.map_err(|error| memory_error(&error));
        }
    }

    /// Log the entries of `conversation` after its cursor and before its
    /// run's start while the run has not pinned its view. `false` when a
    /// closing pass needs a lease this session does not hold. The entries
    /// are read before the run state: an entry committed with a run's start
    /// is then always seen with that run.
    async fn log_conversation(
        &mut self,
        conversation: ConversationId,
        chat: &OptChat,
        mode: PassMode,
    ) -> SessionResult<bool> {
        let cursor = self.cursor(conversation).await?;
        let min = cursor
            .through
            .map(|through| EntryId::from_number(through.get() + 1));
        let mut entries = self.entries(conversation, min).await?;
        if entries.is_empty() {
            return Ok(true);
        }
        let gate = match live_run(&self.harness, conversation, &self.cx).await? {
            Some(run) => {
                let key = run_key(&run);
                match call_state(&self.harness, conversation, &self.cx).await? {
                    Some(call) if call.run_key.as_deref() == Some(key.as_str()) => None,
                    Some(_) | None => run_start(&self.harness, &run, &self.cx).await?,
                }
            }
            None => None,
        };
        if let Some(gate) = gate {
            entries.retain(|entry| entry.id < gate);
        }
        let Some(last) = entries.last() else {
            return Ok(true);
        };
        let through = last.id;
        let lines: Vec<_> = entries.iter().flat_map(entry_lines).collect();
        if !lines.is_empty() {
            match mode {
                PassMode::Normal => chat
                    .turn
                    .ensure(&chat.memory)
                    .await
                    .map_err(|error| memory_error(&error))?,
                PassMode::Closing => {
                    if !chat.turn.lock().await.held() {
                        return Ok(false);
                    }
                }
            }
            let scope = format!("{}/{conversation}", chat.session_id);
            for (seq, (kind, text)) in (cursor.lines..).zip(&lines) {
                let key = AppendKey {
                    scope: scope.clone(),
                    seq,
                };
                chat.memory
                    .append_keyed(*kind, text, key)
                    .await
                    .map_err(|error| memory_error(&error))?;
            }
            self.dirty = true;
        }
        let next = LoggedState {
            through: Some(through),
            lines: cursor.lines + lines.len() as u64,
        };
        commit_cursor(&self.harness, conversation, next, &self.cx).await?;
        Ok(true)
    }

    /// Whether any followed conversation has an entry after its cursor.
    async fn pending(&self) -> SessionResult<bool> {
        for &conversation in &self.followed {
            let cursor = self.cursor(conversation).await?;
            let query = EntryQuery {
                conversation_id: conversation,
                min_entry_id: cursor
                    .through
                    .map(|through| EntryId::from_number(through.get() + 1)),
                max_entry_id: None,
            };
            if !scan_page(&self.harness, query, 1, None, &self.cx)
                .await?
                .0
                .is_empty()
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    async fn cursor(&self, conversation: ConversationId) -> SessionResult<LoggedState> {
        match self
            .harness
            .snapshot(&LOGGED_DOC, conversation, &self.cx)
            .await?
        {
            Some(value) => decode(&value),
            // A root conversation created after the logger started: all of
            // it is new.
            None => Ok(LoggedState::default()),
        }
    }

    /// Entries of `conversation` from `min` on, oldest first, as of the
    /// first page read.
    async fn entries(
        &self,
        conversation: ConversationId,
        min: Option<EntryId>,
    ) -> SessionResult<Vec<EntryRecord>> {
        let query = EntryQuery {
            conversation_id: conversation,
            min_entry_id: min,
            max_entry_id: None,
        };
        let mut entries = Vec::new();
        let mut cursor = None;
        loop {
            let (items, next) =
                scan_page(&self.harness, query, SCAN_PAGE_SIZE, cursor, &self.cx).await?;
            entries.extend(items);
            match next {
                Some(next) => cursor = Some(next),
                None => break,
            }
        }
        // Storage scans newest first.
        entries.reverse();
        Ok(entries)
    }
}

/// One page of a conversation's visible entries, newest first.
async fn scan_page(
    harness: &Harness,
    query: EntryQuery,
    limit: usize,
    cursor: Option<Cursor>,
    cx: &Context,
) -> SessionResult<(Vec<EntryRecord>, Option<Cursor>)> {
    let storage = Arc::clone(harness.storage());
    let line_cx = cx.clone();
    let page = harness
        .read_on_line(async move {
            Ok(storage
                .scan_entries(&query, limit, cursor.as_ref(), &line_cx)
                .await?)
        })
        .await?;
    Ok((page.items, page.next))
}

async fn newest_entry(
    harness: &Harness,
    conversation: ConversationId,
    cx: &Context,
) -> SessionResult<Option<EntryId>> {
    let (items, _) = scan_page(harness, EntryQuery::new(conversation), 1, None, cx).await?;
    Ok(items.first().map(|entry| entry.id))
}

/// The conversations no task owns.
async fn root_conversations(harness: &Harness, cx: &Context) -> SessionResult<Vec<ConversationId>> {
    let mut roots = Vec::new();
    let mut cursor: Option<Cursor> = None;
    loop {
        let storage = Arc::clone(harness.storage());
        let line_cx = cx.clone();
        let after = cursor.take();
        let page = harness
            .read_on_line(async move {
                Ok(storage
                    .scan_conversations(
                        &ConversationQuery::default(),
                        SCAN_PAGE_SIZE,
                        after.as_ref(),
                        &line_cx,
                    )
                    .await?)
            })
            .await?;
        roots.extend(
            page.items
                .iter()
                .filter(|record| record.owner.is_none())
                .map(|record| record.id),
        );
        match page.next {
            Some(next) => cursor = Some(next),
            None => return Ok(roots),
        }
    }
}

async fn commit_cursor(
    harness: &Harness,
    conversation: ConversationId,
    state: LoggedState,
    cx: &Context,
) -> SessionResult<()> {
    harness
        .commit(
            move |tx| async move {
                let draft = tx.doc(&LOGGED_DOC, conversation).await?;
                write(&draft, &state, &["through"])
            },
            cx,
        )
        .await
}
