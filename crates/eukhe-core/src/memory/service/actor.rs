//! The owner's state, on its own thread: every read and write of the chat
//! files happens here, in order.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::{mpsc, Arc};
use std::time::SystemTime;

use eukhe_types::daemon::{MemoryLine, MemoryUpdate};
use eukhe_types::pi_ai::ImageContent;
use tokio::sync::oneshot;

use super::owner::Command;
use super::prefix_gate::{prefix_key, PrefixGate};
use super::turn::{Origin, Turns, TURN_FILE};
use super::{ImportItem, MemoryStatus, Outcome, RenderedView, Reply, Request, Summarizer, Zoomed};
use crate::memory::chat::{free_text, Batch, Chat, Step, Zoom};
use crate::memory::compactor::{build_line, NodeRequest, ResponseStarted};
use crate::memory::prompts::{compress_task, merge_task};
use crate::memory::saved::{self, CompactionPrompt};
use crate::memory::store::{note_scope, LoadMode, MessageRecord, NodeRecord, ScopeMark, Store};
use crate::memory::view::Part;
use crate::memory::{labeled, AppendKey, Kind, RETRY};

/// Consecutive failures of the node a turn waits on before the wait fails
/// with the compactor's error (the node is tried again at the next message
/// or turn).
const SETTLE_FAILURES: u32 = 3;
/// How many recent messages a re-sent append checks for its own copy.
const DEDUPE_WINDOW: usize = 64;

pub(super) struct Actor {
    dir: PathBuf,
    chat: Chat,
    store: Store,
    summarizer: Arc<dyn Summarizer>,
    runtime: tokio::runtime::Handle,
    commands: mpsc::Sender<Command>,
    /// The turns' system prompt and tools, which compactions reuse.
    prompt: Arc<CompactionPrompt>,
    /// Turns waiting for the view to settle (§6).
    view_waiters: Vec<oneshot::Sender<Outcome>>,
    /// The root-turn lease.
    turns: Turns,
    /// The newest keyed message of each append scope (keyed appends).
    scopes: HashMap<String, ScopeMark>,
    failures: HashMap<Part, Failure>,
    /// Nodes that failed and wait for their retry (a subset of the chat's
    /// busy set).
    waiting: HashSet<Part>,
    /// The running compactor calls: the owner aborts them when it stops.
    builds: HashMap<Part, tokio::task::AbortHandle>,
    /// Where updates go (display only: never logged, never sent to a
    /// model).
    subscribers: Vec<tokio::sync::mpsc::UnboundedSender<MemoryUpdate>>,
    /// Nodes built in the current step, published when it ends.
    built_lines: Vec<MemoryLine>,
    /// Why the last save of `view.json` failed; cleared by the next
    /// successful one (every change saves the whole view again).
    save_error: Option<String>,
    /// Bumped whenever the prompt changes: part of every cache prefix.
    prompt_generation: u64,
    /// One writer per new cache prefix (§3.3).
    gate: PrefixGate,
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

enum Prepared {
    Free(String),
    Model(NodeRequest),
}

impl Actor {
    pub(super) fn load(
        dir: &Path,
        summarizer: Arc<dyn Summarizer>,
        runtime: tokio::runtime::Handle,
        commands: mpsc::Sender<Command>,
    ) -> anyhow::Result<Actor> {
        let (mut store, mut loaded) = Store::open(dir, LoadMode::Repair)?;
        let mut problems = loaded.problems.clone();
        let scopes = std::mem::take(&mut loaded.scopes);
        let saved_view = readable(saved::load_view(dir), saved::VIEW_FILE, &mut problems)?;
        let prompt = readable(saved::load_prompt(dir), saved::PROMPT_FILE, &mut problems)?
            .unwrap_or_else(CompactionPrompt::memory_layer);
        let (chat, unlogged) = Chat::from_loaded(loaded, saved_view.clone(), &mut problems);
        if !unlogged.is_empty() {
            let day = crate::platform::local_time(SystemTime::now())?.date();
            for record in &unlogged {
                store.append_merge(record, &day)?;
            }
        }
        // `view.json` is a cache of the fold.
        if saved_view.as_deref() != Some(chat.view().parts()) {
            saved::save_view(dir, chat.view().parts())?;
        }
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
            prompt: Arc::new(prompt),
            view_waiters: Vec::new(),
            turns: Turns::default(),
            scopes,
            failures: HashMap::new(),
            waiting: HashSet::new(),
            builds: HashMap::new(),
            subscribers: Vec::new(),
            built_lines: Vec::new(),
            save_error: None,
            prompt_generation: 0,
            gate: PrefixGate::default(),
            persisting: false,
            persist_again: false,
            persist_reported: false,
        };
        actor.pump();
        actor.built_lines.clear();
        Ok(actor)
    }

    pub(super) fn run(mut self, receiver: &mpsc::Receiver<Command>) {
        while let Ok(command) = receiver.recv() {
            match command {
                Command::Request {
                    origin,
                    request,
                    reply,
                } => self.handle(origin, request, reply),
                Command::Subscribe { sender } => self.subscribers.push(sender),
                Command::Closed { connection } => self.turns.closed(connection),
                Command::Started { part } => {
                    // The prefix is written: its waiters read it now.
                    for (waiter, request) in self.gate.finished(part, true) {
                        self.spawn_build(waiter, request);
                    }
                }
                Command::Built { part, result } => self.built(part, result),
                Command::Retry { part, generation } => {
                    let current = self
                        .failures
                        .get(&part)
                        .is_some_and(|failure| failure.generation == generation);
                    // The delayed retry serves a waiting turn: with none
                    // waiting, the node waits for the next message.
                    self.view_waiters.retain(|waiter| !waiter.is_closed());
                    if current && !self.view_waiters.is_empty() && self.waiting.remove(&part) {
                        self.chat.release(part);
                        self.pump();
                    }
                }
                Command::Persisted(result) => self.persisted(result),
                Command::Shutdown => return,
            }
            self.publish_built();
        }
    }

    fn handle(&mut self, origin: Origin, request: Request, reply: oneshot::Sender<Outcome>) {
        let outcome = match request {
            Request::SettledRender => {
                self.add_view_waiter(reply);
                return;
            }
            Request::AcquireTurn { lease } => {
                self.turns.acquire(origin, lease, reply);
                return;
            }
            Request::Release { lease } => {
                self.turns.release(origin, lease);
                Ok(Reply::Released)
            }
            Request::Append {
                kind,
                text,
                date,
                dedupe,
                key: Some(key),
                images,
            } => match self.scopes.get(&key.scope) {
                Some(mark) if key.seq <= mark.seq => Ok(Reply::AlreadyAppended { id: mark.id }),
                Some(_) | None => self
                    .append(kind, text, &images, date, dedupe, Some(key))
                    .map(|id| Reply::Appended { id }),
            },
            Request::Append {
                kind,
                text,
                date,
                dedupe,
                key: None,
                images,
            } => self
                .append(kind, text, &images, date, dedupe, None)
                .map(|id| Reply::Appended { id }),
            Request::Import { items } => self.import(items),
            Request::Render => Ok(Reply::Rendered {
                view: self.rendered(),
            }),
            Request::Zoom { id, count } => {
                self.zoom(id, count).map(|zoomed| Reply::Zoomed { zoomed })
            }
            Request::Date { id } => Ok(Reply::Text {
                text: match self.chat.message(id) {
                    Some(meta) => display_date(&meta.date),
                    None => format!("No message {id}."),
                },
            }),
            Request::Tree { node } => crate::memory::tree::level(&self.chat, &self.store, node)
                .map(|level| Reply::Tree { level }),
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
            Request::SetPrompt { prompt } => self.set_prompt(prompt).map(|()| Reply::PromptSet),
            // A connection streams its subscription itself; a request
            // channel has nowhere to stream it to.
            Request::Subscribe => Err(anyhow::anyhow!(
                "a subscription needs a connection of its own"
            )),
        };
        // The requester may have stopped waiting; the work is done either way.
        let _ = reply.send(match outcome {
            Ok(reply) => Outcome::Ok(reply),
            Err(error) => Outcome::Error(format!("{error:#}")),
        });
    }

    fn set_prompt(&mut self, prompt: CompactionPrompt) -> anyhow::Result<()> {
        if *self.prompt == prompt {
            return Ok(());
        }
        saved::save_prompt(&self.dir, &prompt)?;
        self.prompt = Arc::new(prompt);
        self.prompt_generation += 1;
        Ok(())
    }

    fn append(
        &mut self,
        kind: Kind,
        text: String,
        images: &[ImageContent],
        date: String,
        dedupe: bool,
        key: Option<AppendKey>,
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
        let id = self.write_message(kind, text, images, date, key)?;
        self.save_view();
        self.retry_failed();
        self.pump();
        Ok(id)
    }

    /// Log one message: its images first (§5: `zoom(id, 1)` gives them
    /// back), then its line.
    fn write_message(
        &mut self,
        kind: Kind,
        text: String,
        images: &[ImageContent],
        date: String,
        key: Option<AppendKey>,
    ) -> anyhow::Result<u64> {
        let day = crate::platform::local_time(SystemTime::now())?.date();
        let i = self.chat.total();
        saved::save_images(&self.dir, i, images)?;
        let record = MessageRecord {
            i,
            kind,
            size: labeled(kind, &text).len(),
            text,
            date,
            key,
        };
        let meta = self.store.append_message(&record, &day)?;
        if let Some(key) = &record.key {
            note_scope(&mut self.scopes, key, i);
        }
        let (id, batch) = self.chat.push_message(meta);
        if let Some(batch) = batch {
            // Logged even when it merged nothing: a restart reads whether
            // the view is still shrinking from it.
            self.store.append_merge(&batch.record(), &day)?;
            if !batch.merged.is_empty() {
                self.publish_batch(&batch);
            }
        }
        Ok(id)
    }

    fn import(&mut self, items: Vec<ImportItem>) -> anyhow::Result<Reply> {
        let first = self.chat.total();
        let count = items.len() as u64;
        for item in items {
            self.write_message(item.kind, item.text, &[], item.date, None)?;
        }
        self.save_view();
        self.retry_failed();
        self.pump();
        Ok(Reply::Imported { first, count })
    }

    /// Save the view after a change (§3.2). A failure is reported in the
    /// status and the log, and the next change saves the whole view again.
    fn save_view(&mut self) {
        match saved::save_view(&self.dir, self.chat.view().parts()) {
            Ok(()) => self.save_error = None,
            Err(error) => {
                let error = format!("cannot save {}: {error}", saved::VIEW_FILE);
                if self.save_error.as_deref() != Some(error.as_str()) {
                    tracing::warn!(target: "chat_memory", "{error}");
                }
                self.save_error = Some(error);
            }
        }
    }

    /// A new message tries every failed node again at once (§4: "A failed
    /// call is tried again at the next message").
    fn retry_failed(&mut self) {
        for part in self.waiting.drain() {
            if let Some(failure) = self.failures.get_mut(&part) {
                // Invalidate the pending delayed retry.
                failure.generation += 1;
            }
            self.chat.release(part);
        }
    }

    /// `zoom(id, n)`; a message zoomed whole comes with its images (§5).
    fn zoom(&self, id: u64, count: u64) -> anyhow::Result<Zoomed> {
        Ok(match self.chat.zoom(id, count) {
            Zoom::Message(id) => {
                let meta = self
                    .chat
                    .message(id)
                    .ok_or_else(|| anyhow::anyhow!("message {id} is not indexed"))?;
                let record = self.store.read_message(meta)?;
                Zoomed {
                    text: format!("{id}+0|{}", labeled(record.kind, &record.text)),
                    images: saved::load_images(&self.dir, id)?,
                }
            }
            Zoom::Lines(text) => Zoomed {
                text,
                images: Vec::new(),
            },
            Zoom::NoLine => Zoomed {
                text: format!("No line {id}+{count}."),
                images: Vec::new(),
            },
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
            last_error: self.save_error.clone().or_else(|| {
                self.failures
                    .values()
                    .max_by_key(|failure| failure.generation)
                    .map(|failure| failure.error.clone())
            }),
        }
    }

    /// Send `update` to every subscriber still listening.
    fn publish(&mut self, update: &MemoryUpdate) {
        self.subscribers
            .retain(|subscriber| subscriber.send(update.clone()).is_ok());
    }

    /// The nodes built in this step, as one update.
    fn publish_built(&mut self) {
        if self.built_lines.is_empty() {
            return;
        }
        let update = MemoryUpdate::Summarized {
            lines: std::mem::take(&mut self.built_lines),
            view_bytes: self.chat.view().size() as u64,
        };
        self.publish(&update);
    }

    fn publish_batch(&mut self, batch: &Batch) {
        // Lines built before the batch come first.
        self.publish_built();
        self.publish(&MemoryUpdate::Merged {
            pairs: batch.merged.len() as u64,
            before_bytes: batch.before as u64,
            after_bytes: batch.after as u64,
        });
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
                        let key = prefix_key(self.prompt_generation, &request);
                        if let Some(request) = self.gate.admit(key, part, request) {
                            self.spawn_build(part, request);
                        }
                    }
                    Err(error) => self.failed(part, &error),
                }
            }
            if !built_free {
                break;
            }
        }
        self.wake_view_waiters();
    }

    /// Ask the model for node `part`'s line off the actor thread. Its
    /// response's start frees the calls waiting for its prefix (§3.3),
    /// before the line is done.
    fn spawn_build(&mut self, part: Part, request: NodeRequest) {
        let summarizer = Arc::clone(&self.summarizer);
        let prompt = Arc::clone(&self.prompt);
        let commands = self.commands.clone();
        let build = self.runtime.spawn(async move {
            let (started, response) = ResponseStarted::channel();
            let line = build_line(
                summarizer.as_ref(),
                &prompt,
                &request,
                now_millis(),
                started,
            );
            tokio::pin!(line);
            let result = tokio::select! {
                biased;
                result = &mut line => result,
                Ok(()) = response => {
                    // Sent before `Built`: the actor sees them in order.
                    let _ = commands.send(Command::Started { part });
                    line.await
                }
            };
            // A stopped owner no longer needs the line.
            let _ = commands.send(Command::Built { part, result });
        });
        self.builds.insert(part, build.abort_handle());
    }

    fn prepare(&self, part: Part) -> anyhow::Result<Prepared> {
        let step = self.chat.step(part).ok_or_else(|| {
            anyhow::anyhow!("node {}+{} has no sources", part.start(), part.count())
        })?;
        let (free, task) = match &step {
            Step::Compress { message } => {
                let meta = self
                    .chat
                    .message(*message)
                    .ok_or_else(|| anyhow::anyhow!("message {message} is not indexed"))?;
                let record = self.store.read_message(meta)?;
                (
                    free_text(Some((record.kind, &record.text)), &step),
                    compress_task(*message, &labeled(record.kind, &record.text)),
                )
            }
            Step::Merge { left, right } => {
                let half = part.count() / 2;
                let name = |start: u64| format!("{start}+{half}");
                (
                    free_text(None, &step),
                    merge_task(
                        &name(part.start()),
                        &name(part.start() + half),
                        (part.start(), part.end() - 1),
                        (left, right),
                    ),
                )
            }
        };
        Ok(match free {
            Some(text) => Prepared::Free(text),
            None => Prepared::Model(NodeRequest {
                context: self.chat.context(part),
                task,
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
        self.built_lines.push(MemoryLine {
            id: part.start(),
            count: part.count(),
            text: text.to_string(),
        });
        Ok(())
    }

    fn built(&mut self, part: Part, result: anyhow::Result<String>) {
        self.builds.remove(&part);
        for (waiter, request) in self.gate.finished(part, result.is_ok()) {
            self.spawn_build(waiter, request);
        }
        match result.and_then(|text| self.save_node(part, &text)) {
            Ok(()) => self.pump(),
            Err(error) => self.failed(part, &error),
        }
    }

    /// A node failed: report its first failure, keep it busy, and try it
    /// again at the next message or turn. While a turn waits for the view,
    /// it is also tried again after [`RETRY`] (no backoff: the wait fails
    /// after [`SETTLE_FAILURES`]); an idle chat makes no call for it.
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
                "cannot summarize {}+{}: {}; retrying at the next message",
                part.start(),
                part.count(),
                entry.error
            );
        }
        let generation = entry.generation;
        self.chat.mark_busy(part);
        self.waiting.insert(part);
        self.fail_waiters_if_stuck();
        self.view_waiters.retain(|waiter| !waiter.is_closed());
        if self.view_waiters.is_empty() {
            return;
        }
        let commands = self.commands.clone();
        self.runtime.spawn(async move {
            tokio::time::sleep(RETRY).await;
            let _ = commands.send(Command::Retry { part, generation });
        });
    }

    /// A turn waits for the view: rendered at once when every line is a
    /// summary, else by [`Actor::wake_view_waiters`] in the step that builds
    /// the last one (§6). Like a new message, the wait tries every failed
    /// node again now.
    fn add_view_waiter(&mut self, reply: oneshot::Sender<Outcome>) {
        if self.chat.settled() {
            // The requester may have stopped waiting.
            let _ = reply.send(Outcome::Ok(Reply::Rendered {
                view: self.rendered(),
            }));
            return;
        }
        self.view_waiters.retain(|waiter| !waiter.is_closed());
        self.view_waiters.push(reply);
        if !self.waiting.is_empty() {
            self.retry_failed();
            self.pump();
        }
    }

    /// Answer the waiting turns when every view line is a summary: the
    /// check and the render are one step, so the view they get is the one
    /// that was checked (an append can only come after).
    fn wake_view_waiters(&mut self) {
        self.view_waiters.retain(|waiter| !waiter.is_closed());
        if self.view_waiters.is_empty() || !self.chat.settled() {
            return;
        }
        let view = self.rendered();
        for waiter in self.view_waiters.drain(..) {
            // A waiter that went away just now loses only its own view.
            let _ = waiter.send(Outcome::Ok(Reply::Rendered { view: view.clone() }));
        }
    }

    fn rendered(&self) -> RenderedView {
        RenderedView {
            messages: self.chat.total(),
            text: self.chat.render(),
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
            "the memory compactor cannot summarize message {} ({} tries): {}; it tries again at the next message",
            blocking.i,
            failure.count,
            failure.error
        );
        for waiter in self.view_waiters.drain(..) {
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

impl Drop for Actor {
    fn drop(&mut self) {
        // A stopped owner's compactor calls stop with it: their lines would
        // have nowhere to go, and dropping a call cancels its request.
        for build in self.builds.values() {
            build.abort();
        }
    }
}

/// A saved file's content; a damaged one is a load problem (the chat
/// works without it), any other read error fails the load.
fn readable<T>(
    loaded: std::io::Result<Option<T>>,
    file: &str,
    problems: &mut Vec<String>,
) -> anyhow::Result<Option<T>> {
    match loaded {
        Ok(value) => Ok(value),
        Err(error) if error.kind() == std::io::ErrorKind::InvalidData => {
            problems.push(format!("ignored a damaged {file}: {error}"));
            Ok(None)
        }
        Err(error) => Err(anyhow::Error::new(error).context(format!("cannot read {file}"))),
    }
}

/// The chat directory's runtime files, never committed: the lock socket,
/// the takeover lock, the turn file, the temporary files of atomic saves,
/// the compaction prompt (derived from the turns, rewritten often), and
/// the view cache (a fold of the logs).
const IGNORED: [&str; 6] = [
    "lock",
    "lock.lock/",
    TURN_FILE,
    ".*.tmp",
    saved::PROMPT_FILE,
    saved::VIEW_FILE,
];

/// `git add` + `git commit` of the chat directory, initializing the repo on
/// first use. The runtime files are ignored (an ignore file from before a
/// runtime file existed gets its line); hooks and signing are off so a
/// global configuration cannot block or prompt in the background.
pub(super) fn commit(dir: &Path, git_dir: &Path) -> Result<(), String> {
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
    }
    let ignore = dir.join(".gitignore");
    let mut ignored = match std::fs::read_to_string(&ignore) {
        Ok(text) => text,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => String::new(),
        Err(error) => return Err(format!("cannot read .gitignore: {error}")),
    };
    let missing: Vec<&str> = IGNORED
        .into_iter()
        .filter(|entry| !ignored.lines().any(|line| line == *entry))
        .collect();
    if !missing.is_empty() {
        if !ignored.is_empty() && !ignored.ends_with('\n') {
            ignored.push('\n');
        }
        for entry in missing {
            ignored.push_str(entry);
            ignored.push('\n');
        }
        std::fs::write(&ignore, ignored)
            .map_err(|error| format!("cannot write .gitignore: {error}"))?;
    }
    // A chat committed before the view was a cache tracks it: untrack it.
    check(
        git(&[
            "rm",
            "-q",
            "--cached",
            "--ignore-unmatch",
            "--",
            saved::VIEW_FILE,
        ])?,
        "rm",
    )?;
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
pub(super) fn display_date(date: &str) -> String {
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
