//! File watching for `NativeExecutionEnv`. Port of `env/node-watch.ts`.
//!
//! Watches by snapshots: native events only trigger a debounced rescan, and
//! changes are the difference between snapshots plus the event paths. A
//! replaced file, a renamed or recreated ancestor, or a directory created with
//! its contents therefore never depends on which events an operating system
//! sends. New directories get their watchers before they are scanned again, so
//! nothing written into them before the watcher existed is missed.
//!
//! Native events come from inotify on Linux (`native_watch/inotify.rs`, with
//! libuv's event names) and kqueue on macOS (`native_watch/kqueue.rs`). Both
//! watch one directory per watch, so the TS `perDirectory` layout applies on
//! both platforms and no watch is recursive. Where this differs from Node:
//!
//! - inotify's queue overflow (`IN_Q_OVERFLOW`) schedules a rescan; libuv
//!   drops it.
//! - A failed read of the inotify or kqueue descriptor (libuv aborts the
//!   process) switches the watcher to polling, delivering `Overflow`.
//! - Node's watcher `'error'` event is never emitted for inotify or kqueue
//!   handles (libuv reports no error status for them), so its handler has no
//!   counterpart.

#[cfg(target_os = "linux")]
mod inotify;
#[cfg(target_os = "macos")]
mod kqueue;
mod paths;
mod scan;
#[cfg(test)]
mod tests;

use std::collections::{HashMap, HashSet};
use std::panic::{self, AssertUnwindSafe};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, MutexGuard, PoisonError, Weak};
use std::time::Duration;

use eukhe_chord::context::Context;
use futures::future::{self, BoxFuture};
use futures::FutureExt;
use tokio::sync::Notify;
use tokio::task::AbortHandle;

#[cfg(target_os = "linux")]
use self::inotify::Backend;
#[cfg(target_os = "macos")]
use self::kqueue::Backend;
use self::paths::{ancestors_of, compare_utf16, components_below, is_within, join};
use self::scan::{EntryKind, ResolvedTarget, ScanError, Snapshot};
use super::node_error::uv_code;
use super::{FileError, FileWatcher, OnWatchChange, WatchChange, WatchMode, WatchTarget};

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
compile_error!("native watching supports Linux (inotify) and macOS (kqueue) only");

const DEBOUNCE: Duration = Duration::from_millis(50);
const DEFAULT_POLL_MS: u64 = 2000;
const DEFAULT_MAX_DIRECTORIES: usize = 10_000;
/// Rescans one sync makes while new watchers keep appearing.
const MAX_SYNC_ROUNDS: usize = 10;

/// How `NativeExecutionEnv` watches (TS `NodeWatchOptions`).
#[derive(Clone, Debug, Default, PartialEq)]
pub struct NativeWatchOptions {
    /// Force a mode. By default `Polling` is chosen for file systems that do
    /// not report remote changes (Linux network and FUSE file systems).
    pub mode: Option<WatchMode>,
    /// Interval between snapshots in `Polling` mode; default 2000 ms.
    pub poll_interval_ms: Option<u64>,
    /// Most directories one watcher covers; default 10,000.
    pub max_directories: Option<usize>,
}

/// Identifies one native watch of a [`Backend`].
type HandleId = u64;

/// What a native watch reports to: the closure TS passes to `fs.watch`.
#[derive(Clone, Debug)]
enum Listener {
    /// A watched directory: TS `#onEvent(path, filename)`.
    Directory(String),
    /// A target that is a symbolic link to a file, watched through the link:
    /// TS `#onLinkedFileEvent(target)`.
    LinkedFile(String),
    /// macOS: a file inside a watched directory, whose content changes kqueue
    /// does not report on the directory: TS `#onEvent(directory, name)`, the
    /// event `FSEvents` would report.
    #[cfg(target_os = "macos")]
    File { directory: String, name: String },
}

/// What a [`Backend`] reads.
enum Notice {
    /// A native watch fired; `filename` is the name libuv would report, if
    /// any.
    Event {
        listener: Listener,
        filename: Option<String>,
    },
    /// The kernel dropped events (inotify `IN_Q_OVERFLOW`): rescan.
    #[cfg(target_os = "linux")]
    Overflow,
    /// The event descriptor failed and reports nothing more.
    Broken,
}

/// Where a [`Backend`] sends what it reads.
type Sink = Arc<dyn Fn(Vec<Notice>) + Send + Sync>;

/// A native watch and the identity of what it was installed on: a path
/// replaced by another file needs a new one.
struct Installed {
    handle: HandleId,
    dev: u64,
    ino: u64,
}

/// A pending `setTimeout`. Clearing it (TS `clearTimeout`) cancels it even if
/// its task already woke up and waits for the state lock.
struct Timer {
    cancelled: Arc<AtomicBool>,
    task: AbortHandle,
}

impl Timer {
    fn clear(&self) {
        self.cancelled.store(true, Ordering::SeqCst);
        self.task.abort();
    }

    fn is(&self, cancelled: &Arc<AtomicBool>) -> bool {
        Arc::ptr_eq(&self.cancelled, cancelled)
    }
}

/// What a fired timer does.
#[derive(Clone, Copy)]
enum TimerAction {
    /// The debounce timer: `void this.#flush()`.
    Flush,
    /// The polling timer: `void this.#flush().finally(() => this.#schedulePoll())`.
    Poll,
}

/// Whether a sync reports differences from the previous snapshot.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Report {
    /// The first sync of `open`: the snapshot is the baseline.
    Baseline,
    Changes,
}

/// What `#reconcileWatchers` did.
enum Reconciled {
    Added,
    NothingAdded,
    /// Installing a watch failed for lack of watches or support: switch to
    /// polling.
    OutOfWatches,
}

/// The running flush: TS `#running`, awaited by `close`.
type Running = future::Shared<BoxFuture<'static, ()>>;

/// The mutable fields of TS `NodeFileWatcher`.
struct State {
    watchers: HashMap<String, Installed>,
    events: HashSet<String>,
    snapshot: Snapshot,
    timer: Option<Timer>,
    /// Timers TS overwrote or forgot without clearing (they still fire);
    /// tracked only so stopping can cancel them.
    stray_timers: Vec<Timer>,
    running: Option<Running>,
    dirty: bool,
    closed: bool,
    /// Callbacks in progress; `close` waits for them.
    delivering: usize,
    backend: Backend,
}

impl State {
    /// TS `#stop`.
    fn stop(&mut self) {
        self.closed = true;
        if let Some(timer) = self.timer.take() {
            timer.clear();
        }
        for timer in self.stray_timers.drain(..) {
            timer.clear();
        }
        for (_, installed) in self.watchers.drain() {
            self.backend.remove(installed.handle);
        }
        self.backend.close();
    }
}

struct Shared {
    targets: Vec<ResolvedTarget>,
    on_change: OnWatchChange,
    poll_interval: Duration,
    max_directories: usize,
    /// TS `#mode === "polling"`; read by scans on blocking threads.
    polling: AtomicBool,
    /// Signalled when the last callback in progress returns.
    idle: Notify,
    state: Mutex<State>,
}

/// Watches by snapshots (TS `NodeFileWatcher`).
pub(crate) struct NativeFileWatcher {
    shared: Arc<Shared>,
}

impl NativeFileWatcher {
    /// Establish coverage: watchers first, then the snapshot later changes are
    /// compared with. Fails like node.ts `watch`: a tree over the directory
    /// budget with an `invalid` error without path; an unreadable target with
    /// node.ts `toFileError` of the Node error.
    pub(crate) async fn open(
        targets: &[WatchTarget],
        resolve_path: &(dyn Fn(&str) -> String + Send + Sync),
        on_change: OnWatchChange,
        options: &NativeWatchOptions,
    ) -> Result<NativeFileWatcher, FileError> {
        let resolved: Vec<ResolvedTarget> = targets
            .iter()
            .map(|target| ResolvedTarget {
                path: resolve_path(&target.path),
                recursive: target.recursive,
                hidden: target.exclude.hidden,
                names: target.exclude.names.iter().cloned().collect(),
            })
            .collect();
        let mode = if let Some(mode) = options.mode {
            mode
        } else {
            let paths: Vec<String> = resolved.iter().map(|target| target.path.clone()).collect();
            if blocking(move || scan::any_unreliable(&paths)).await {
                WatchMode::Polling
            } else {
                WatchMode::Native
            }
        };
        let watcher = Self {
            shared: Shared::new(resolved, on_change, mode, options),
        };
        if let Err(error) = watcher.shared.sync(Report::Baseline).await {
            watcher.shared.lock().stop();
            return Err(error.into_open_error());
        }
        watcher.shared.schedule_poll(&mut watcher.shared.lock());
        Ok(watcher)
    }
}

impl FileWatcher for NativeFileWatcher {
    fn mode(&self) -> WatchMode {
        self.shared.mode()
    }

    fn close<'a>(&'a self, _cx: &'a Context) -> BoxFuture<'a, ()> {
        Box::pin(async move {
            let running = {
                let mut state = self.shared.lock();
                if state.closed {
                    return;
                }
                state.stop();
                state.running.clone()
            };
            if let Some(running) = running {
                running.await;
            }
            // A callback that started before `stop` (the overflow of a broken event
            // descriptor) finishes before `close` resolves.
            self.shared.deliveries_settled().await;
        })
    }
}

impl Drop for NativeFileWatcher {
    /// A watcher dropped without `close` stops: its timers, native watches,
    /// and descriptors go with it.
    fn drop(&mut self) {
        self.shared.lock().stop();
    }
}

/// Run `work` on a blocking thread, as Node runs `fs` calls on its thread
/// pool.
async fn blocking<T: Send + 'static>(work: impl FnOnce() -> T + Send + 'static) -> T {
    match tokio::task::spawn_blocking(work).await {
        Ok(value) => value,
        Err(error) => match error.try_into_panic() {
            Ok(payload) => panic::resume_unwind(payload),
            // Blocking tasks are only cancelled by a runtime shutting down, which
            // stops this task too.
            Err(error) => panic!("blocking watch task cancelled: {error}"),
        },
    }
}

impl Shared {
    fn new(
        targets: Vec<ResolvedTarget>,
        on_change: OnWatchChange,
        mode: WatchMode,
        options: &NativeWatchOptions,
    ) -> Arc<Self> {
        Arc::new_cyclic(|weak: &Weak<Self>| {
            let weak = weak.clone();
            let sink: Sink = Arc::new(move |notices| {
                if let Some(shared) = weak.upgrade() {
                    shared.notify(notices);
                }
            });
            Self {
                targets,
                on_change,
                poll_interval: Duration::from_millis(
                    options.poll_interval_ms.unwrap_or(DEFAULT_POLL_MS),
                ),
                max_directories: options.max_directories.unwrap_or(DEFAULT_MAX_DIRECTORIES),
                polling: AtomicBool::new(mode == WatchMode::Polling),
                idle: Notify::new(),
                state: Mutex::new(State {
                    watchers: HashMap::new(),
                    events: HashSet::new(),
                    snapshot: Snapshot::new(),
                    timer: None,
                    stray_timers: Vec::new(),
                    running: None,
                    dirty: false,
                    closed: false,
                    delivering: 0,
                    backend: Backend::new(sink),
                }),
            }
        })
    }

    fn lock(&self) -> MutexGuard<'_, State> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }

    fn mode(&self) -> WatchMode {
        if self.polling.load(Ordering::SeqCst) {
            WatchMode::Polling
        } else {
            WatchMode::Native
        }
    }

    /// Wait until no callback is in progress.
    async fn deliveries_settled(&self) {
        loop {
            let settled = self.idle.notified();
            if self.lock().delivering == 0 {
                return;
            }
            settled.await;
        }
    }

    /// TS `#deliver`.
    fn deliver(&self, change: WatchChange) {
        {
            let mut state = self.lock();
            if state.closed {
                return;
            }
            state.delivering += 1;
        }
        // A panicking callback must not stop watching: TS swallows what the callback throws.
        // The panic hook has already reported the panic.
        let _ = panic::catch_unwind(AssertUnwindSafe(|| (self.on_change)(change)));
        let mut state = self.lock();
        state.delivering -= 1;
        if state.delivering == 0 {
            self.idle.notify_waiters();
        }
    }

    /// TS `#schedulePoll`.
    fn schedule_poll(self: &Arc<Self>, state: &mut State) {
        if state.closed || !self.polling.load(Ordering::SeqCst) {
            return;
        }
        let timer = self.start_timer(self.poll_interval, TimerAction::Poll);
        // TS overwrites `#timer` without clearing it: the previous timer still fires.
        if let Some(previous) = state.timer.replace(timer) {
            state.stray_timers.push(previous);
        }
    }

    /// TS `#scheduleFlush`.
    fn schedule_flush(self: &Arc<Self>, state: &mut State) {
        if state.closed || state.timer.is_some() {
            return;
        }
        state.timer = Some(self.start_timer(DEBOUNCE, TimerAction::Flush));
    }

    fn start_timer(self: &Arc<Self>, delay: Duration, action: TimerAction) -> Timer {
        let cancelled = Arc::new(AtomicBool::new(false));
        let shared = Arc::clone(self);
        let fired = Arc::clone(&cancelled);
        let task = tokio::spawn(async move {
            tokio::time::sleep(delay).await;
            {
                let mut state = shared.lock();
                if fired.load(Ordering::SeqCst) {
                    return;
                }
                state.stray_timers.retain(|timer| !timer.is(&fired));
                // `this.#timer = undefined`, whichever timer it holds.
                if let Some(current) = state.timer.take() {
                    if !current.is(&fired) {
                        state.stray_timers.push(current);
                    }
                }
            }
            match action {
                TimerAction::Flush => drop(shared.flush()),
                TimerAction::Poll => {
                    shared.flush().await;
                    shared.schedule_poll(&mut shared.lock());
                }
            }
        });
        Timer {
            cancelled,
            task: task.abort_handle(),
        }
    }

    /// TS `#flush`: start a flush, or mark the running one dirty so it goes
    /// round again.
    fn flush(self: &Arc<Self>) -> Running {
        let mut state = self.lock();
        if let Some(running) = state.running.clone() {
            state.dirty = true;
            return running;
        }
        let running = Arc::clone(self).run_flush().boxed().shared();
        state.running = Some(running.clone());
        drop(state);
        tokio::spawn(running.clone());
        running
    }

    async fn run_flush(self: Arc<Self>) {
        if let Err(error) = self.flush_rounds().await {
            self.deliver(WatchChange::Error(error.into_flush_error()));
            self.lock().stop();
        }
        self.lock().running = None;
    }

    async fn flush_rounds(self: &Arc<Self>) -> Result<(), ScanError> {
        loop {
            let events = {
                let mut state = self.lock();
                state.dirty = false;
                std::mem::take(&mut state.events)
            };
            let mut changed = self.sync(Report::Changes).await?;
            changed.extend(events);
            if !changed.is_empty() {
                let mut paths: Vec<String> = changed.into_iter().collect();
                paths.sort_by(|left, right| compare_utf16(left, right));
                self.deliver(WatchChange::Paths(paths));
            }
            let state = self.lock();
            if !state.dirty || state.closed {
                return Ok(());
            }
        }
    }

    /// TS `#sync`: rescan, report differences, and install watchers for new
    /// directories, rescanning until none are new.
    async fn sync(self: &Arc<Self>, mut report: Report) -> Result<HashSet<String>, ScanError> {
        let mut changed = HashSet::new();
        for _ in 0..MAX_SYNC_ROUNDS {
            if self.lock().closed {
                break;
            }
            let shared = Arc::clone(self);
            let scan = blocking(move || {
                scan::scan(&shared.targets, &shared.polling, shared.max_directories)
            })
            .await?;
            let mut state = self.lock();
            // Closed during the scan: installing watchers now would leak them.
            if state.closed {
                break;
            }
            if report == Report::Changes {
                for path in diff(&state.snapshot, &scan.snapshot) {
                    changed.insert(self.reported(path));
                }
            }
            state.snapshot = scan.snapshot;
            if self.polling.load(Ordering::SeqCst) {
                break;
            }
            match self.reconcile_watchers(&mut state, &scan.linked_files) {
                Reconciled::Added => {}
                Reconciled::NothingAdded => break,
                Reconciled::OutOfWatches => {
                    drop(state);
                    self.switch_to_polling();
                    break;
                }
            }
            // Something written into a new directory before its watcher existed shows up in
            // the next round.
            report = Report::Changes;
        }
        Ok(changed)
    }

    /// TS `#reported`: an ancestor that changed identity moved every target
    /// below it; report those targets.
    fn reported(&self, path: &str) -> String {
        if self
            .targets
            .iter()
            .any(|target| is_within(path, &target.path))
        {
            return path.to_owned();
        }
        self.targets
            .iter()
            .find(|target| is_within(&target.path, path))
            .map_or_else(|| path.to_owned(), |target| target.path.clone())
    }

    /// TS `#reconcileWatchers`: watch every existing ancestor of each target,
    /// each target directory, each target that is a symbolic link to a file
    /// (changes to that file are not events of the link's directory), and each
    /// directory below a recursive target (on macOS also each file within a
    /// target). Reports whether a watcher was added.
    fn reconcile_watchers(&self, state: &mut State, linked_files: &[String]) -> Reconciled {
        let State {
            snapshot,
            watchers,
            backend,
            ..
        } = state;
        let mut wanted: Vec<(String, Listener)> = Vec::new();
        let mut wanted_paths: HashSet<String> = HashSet::new();
        let mut want = |path: &str, listener: Listener| {
            if wanted_paths.insert(path.to_owned()) {
                wanted.push((path.to_owned(), listener));
            }
        };
        for path in linked_files {
            want(path, Listener::LinkedFile(path.clone()));
        }
        let is_directory = |path: &str| {
            snapshot
                .get(path)
                .is_some_and(|entry| entry.kind == EntryKind::Directory)
        };
        for target in &self.targets {
            for ancestor in ancestors_of(&target.path) {
                if is_directory(&ancestor) {
                    let listener = Listener::Directory(ancestor.clone());
                    want(&ancestor, listener);
                }
            }
            if !is_directory(&target.path) {
                continue;
            }
            want(&target.path, Listener::Directory(target.path.clone()));
            if target.recursive {
                for (path, entry) in snapshot.iter() {
                    if entry.kind == EntryKind::Directory
                        && *path != target.path
                        && is_within(path, &target.path)
                    {
                        want(path, Listener::Directory(path.clone()));
                    }
                }
            }
        }
        #[cfg(target_os = "macos")]
        for target in &self.targets {
            for (path, entry) in snapshot.iter() {
                if entry.kind == EntryKind::File && is_within(path, &target.path) {
                    let listener = Listener::File {
                        directory: paths::dirname(path).to_owned(),
                        name: paths::basename(path).to_owned(),
                    };
                    want(path, listener);
                }
            }
        }
        // Gone, or replaced: a watcher follows the directory it was installed on, not the path.
        watchers.retain(|path, installed| {
            let keep = wanted_paths.contains(path)
                && snapshot
                    .get(path)
                    .is_some_and(|entry| entry.dev == installed.dev && entry.ino == installed.ino);
            if !keep {
                backend.remove(installed.handle);
            }
            keep
        });
        let mut added = false;
        for (path, listener) in wanted {
            let Some(entry) = snapshot.get(&path) else {
                continue;
            };
            if watchers.contains_key(&path) {
                continue;
            }
            match backend.add(&path, listener) {
                Ok(handle) => {
                    watchers.insert(
                        path,
                        Installed {
                            handle,
                            dev: entry.dev,
                            ino: entry.ino,
                        },
                    );
                    added = true;
                }
                // Out of watches or unsupported: compare snapshots from now on, and say coverage
                // was uncertain. A path that vanished or is not readable is skipped.
                Err(error) => {
                    if !matches!(uv_code(&error), "ENOENT" | "EACCES" | "EPERM") {
                        return Reconciled::OutOfWatches;
                    }
                }
            }
        }
        if added {
            Reconciled::Added
        } else {
            Reconciled::NothingAdded
        }
    }

    /// TS `#switchToPolling`.
    fn switch_to_polling(self: &Arc<Self>) {
        {
            let mut state = self.lock();
            if self.polling.swap(true, Ordering::SeqCst) {
                return;
            }
            let State {
                watchers, backend, ..
            } = &mut *state;
            for (_, installed) in watchers.drain() {
                backend.remove(installed.handle);
            }
        }
        self.deliver(WatchChange::Overflow);
        let mut state = self.lock();
        if let Some(timer) = state.timer.take() {
            timer.clear();
        }
        self.schedule_poll(&mut state);
    }

    /// Handle what the backend read.
    fn notify(self: &Arc<Self>, notices: Vec<Notice>) {
        for notice in notices {
            match notice {
                Notice::Event { listener, filename } => {
                    let mut state = self.lock();
                    match listener {
                        Listener::Directory(path) => {
                            self.on_event(&mut state, &path, filename.as_deref());
                        }
                        Listener::LinkedFile(target) => {
                            self.on_linked_file_event(&mut state, target);
                        }
                        #[cfg(target_os = "macos")]
                        Listener::File { directory, name } => {
                            self.on_event(&mut state, &directory, Some(&name));
                        }
                    }
                }
                #[cfg(target_os = "linux")]
                Notice::Overflow => self.schedule_flush(&mut self.lock()),
                Notice::Broken => {
                    if !self.lock().closed {
                        self.switch_to_polling();
                    }
                }
            }
        }
    }

    /// TS `#onEvent`.
    fn on_event(self: &Arc<Self>, state: &mut State, directory: &str, filename: Option<&str>) {
        if state.closed {
            return;
        }
        let path = match filename {
            None => directory.to_owned(),
            Some(name) => join(directory, name),
        };
        // Events about unrelated siblings of an ancestor, or about excluded entries, are ignored.
        let relevant = self.in_scope(&path);
        if relevant {
            state.events.insert(self.reported(&path));
        }
        if relevant || filename.is_none() {
            self.schedule_flush(state);
        }
    }

    /// TS `#onLinkedFileEvent`: the file a target links to changed; report
    /// the target.
    fn on_linked_file_event(self: &Arc<Self>, state: &mut State, target: String) {
        if state.closed {
            return;
        }
        state.events.insert(target);
        self.schedule_flush(state);
    }

    /// TS `#inScope`.
    fn in_scope(&self, path: &str) -> bool {
        for target in &self.targets {
            if is_within(&target.path, path) {
                return true;
            }
            if !is_within(path, &target.path) || path == target.path {
                continue;
            }
            let components = components_below(&target.path, path);
            if !target.recursive && components.len() > 1 {
                continue;
            }
            if components.iter().any(|name| target.excluded(name)) {
                continue;
            }
            return true;
        }
        false
    }
}

/// TS `#diff` before `#reported`: paths added, changed, or removed.
fn diff<'a>(previous: &'a Snapshot, next: &'a Snapshot) -> Vec<&'a str> {
    let mut changed = Vec::new();
    for (path, entry) in next {
        if previous.get(path) != Some(entry) {
            changed.push(path.as_str());
        }
    }
    for path in previous.keys() {
        if !next.contains_key(path) {
            changed.push(path.as_str());
        }
    }
    changed
}
