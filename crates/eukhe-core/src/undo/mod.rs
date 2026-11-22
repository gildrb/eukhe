//! `/undo` and `/diff`: a snapshot of the workspace at the start of every
//! turn of a top-level session (a prompt: one run of its main
//! conversation, all its rounds), taken in the background when the turn's
//! first request is prepared and awaited before any tool of the turn runs.
//! Every decision is the compiled core's (`bend/undo.bend`, laws
//! `laws/undo.bend`, called through `eukhe_bend::rules::undo`): which
//! snapshot `/undo` restores and `/diff` compares with, what `/undo` does
//! to each changed path, what `/diff` says of it. Rust does the git IO
//! ([`store`]) and writes the files ([`restore`]). Paths the workspace's
//! `.gitignore` ignores, files over [`store::FILE_CAP_BYTES`] and nested
//! repositories are held back: never snapshotted, never touched. Each turn
//! records the root run it starts, so `/undo` names the irreversible
//! effects of the undone prompt's run (the session's `eukhe.effects`
//! ledger), which it does not take back. `/undo` is refused while a run is
//! going ([`undo_turn`], the one entry every surface calls).

mod hooks;
mod prune;
mod restore;
mod store;
#[cfg(test)]
mod tests;

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_bend::rules::undo::{self as rules, Act, Event, Fix, Reach, Row, Seen, Snapshots};
use eukhe_chord::context::Context;
use eukhe_chord::json::{from_json, JsonValue};
use eukhe_durable::harness::effects::{read_effects_state, run_report, EffectsState};
use eukhe_durable::harness::{LiveState, LIVE_DOC};
use eukhe_durable::types::{SubmissionId, TaskId};
use eukhe_types::effects::RanEffect;
use eukhe_types::undo::{DiffScope, TurnDiffReply, UndoReply};
use futures::future::{BoxFuture, Shared};
use futures::FutureExt;

use crate::durable::EukheSession;

pub(crate) use hooks::extension;
pub use prune::prune_snapshots;

use store::{Blob, Change, Loaded, Store, Taken};

/// The directory under the work root holding the sessions' snapshots.
const SNAPSHOTS_DIR: &str = "snapshots";

/// A unified diff longer than this is cut.
const DIFF_CAP_BYTES: usize = 1024 * 1024;

/// The longest reason kept for a turn whose snapshot failed.
const REASON_CHARS: usize = 200;

/// `/undo` on `session`: restore its workspace to the start of the newest
/// turn not undone, naming the irreversible effects of that prompt's run.
/// Refused while a run is going on its main conversation (the tools of the
/// run would race the restore).
///
/// # Errors
///
/// [`UndoError::RunInProgress`] while a run is going,
/// [`UndoError::NoSnapshots`] for a session that keeps none, the ledger
/// does not read, and every error of [`TurnSnapshots::undo`].
pub async fn undo_turn(session: &EukheSession, cx: &Context) -> Result<UndoReply, UndoError> {
    let snapshots = session.turn_snapshots().ok_or(UndoError::NoSnapshots)?;
    let main = session.main().id();
    let live = match session.harness().snapshot(&LIVE_DOC, main, cx).await? {
        Some(value) => {
            from_json::<LiveState>(&JsonValue::Object(value))
                .map_err(eukhe_durable::session::SessionError::from)?
                .run
        }
        None => None,
    };
    if live.is_some() {
        return Err(UndoError::RunInProgress);
    }
    let ledger = read_effects_state(session.harness(), main, cx).await?;
    snapshots.undo(&ledger).await
}

/// `/diff` on `session`: what changed in its workspace since the start of
/// the newest turn not undone ([`DiffScope::Turn`]) or of its first turn
/// ([`DiffScope::All`]). Allowed while a run is going: it first waits for
/// the snapshot of the turn that is starting, if one is being taken.
///
/// # Errors
///
/// [`UndoError::NoSnapshots`] for a session that keeps none, and every
/// error of [`TurnSnapshots::diff`].
pub async fn turn_diff(
    session: &EukheSession,
    scope: DiffScope,
) -> Result<TurnDiffReply, UndoError> {
    let snapshots = session.turn_snapshots().ok_or(UndoError::NoSnapshots)?;
    snapshots.ready().await;
    snapshots.diff(scope).await
}

/// The snapshot of `turn` is kept: refused when its turn has none.
fn kept(loaded: &Loaded, turn: u64) -> Result<(), UndoError> {
    match loaded.lost.get(&turn) {
        Some(reason) => Err(UndoError::NoTurnSnapshot {
            turn,
            reason: reason.clone(),
        }),
        None => Ok(()),
    }
}

/// The irreversible effects of `run` in `ledger`, in ledger order (the
/// end list of that run): none for a turn with no recorded run.
fn not_undone(ledger: &EffectsState, run: Option<u64>) -> Result<Vec<RanEffect>, UndoError> {
    match run {
        Some(run) => Ok(run_report(ledger, run)?.ran),
        None => Ok(Vec::new()),
    }
}

/// Why `/undo`, `/diff` or a turn's snapshot failed.
#[derive(Debug, thiserror::Error)]
pub enum UndoError {
    /// No snapshot is left to restore.
    #[error("Nothing to undo")]
    NothingToUndo,
    /// No turn has started: nothing to compare with.
    #[error("No prompt to compare with yet")]
    NothingToDiff,
    /// A run is going on the session: `/undo` would race its tools.
    #[error("A run is going: /undo is refused until it ends")]
    RunInProgress,
    /// The session keeps no snapshots (a subagent, a session without
    /// storage).
    #[error("This session keeps no workspace snapshots")]
    NoSnapshots,
    /// The snapshot `/undo` restores or `/diff` compares with failed when
    /// its turn started; nothing changed.
    #[error("Prompt {turn} has no workspace snapshot (taking it failed: {reason}), so /undo and /diff cannot go back past its start; nothing changed")]
    NoTurnSnapshot { turn: u64, reason: String },
    /// A turn start could not even read the snapshots: which turns they
    /// hold is unknown from then on.
    #[error("This session's workspace snapshots cannot be used since a prompt started without reading them ({reason}); nothing changed")]
    Unread { reason: String },
    /// The workspace holds more files than a snapshot takes.
    #[error("The workspace has {files} files, more than a snapshot takes")]
    TooLarge { files: usize },
    /// The compiled core answered outside its laws.
    #[error("The compiled core answered {0} to {1}")]
    Answer(String, &'static str),
    /// A git command failed.
    #[error("{detail}")]
    Git { detail: String, status: Option<i32> },
    /// The session's run state did not read.
    #[error(transparent)]
    Session(#[from] eukhe_durable::session::SessionError),
    #[error(transparent)]
    Io(#[from] std::io::Error),
    #[error(transparent)]
    Core(#[from] eukhe_bend::Error),
}

impl UndoError {
    fn git(detail: &str) -> Self {
        Self::Git {
            detail: detail.to_owned(),
            status: None,
        }
    }
}

/// The directory of every session's snapshots of the install at
/// `agent_dir`: `<work root>/snapshots`.
#[must_use]
pub fn snapshots_dir(agent_dir: &Path) -> Option<PathBuf> {
    Some(eukhe_types::platform::dirs::work_root_of(agent_dir)?.join(SNAPSHOTS_DIR))
}

/// What one turn's snapshot is taken for: a run of the main conversation,
/// named by its first input (its later rounds hand the run over to new
/// generation tasks, which stay in the turn); a generation of a run with
/// no input is a turn of its own.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TurnKey {
    Run(SubmissionId),
    Task(TaskId),
}

/// The snapshot of the turn that is starting, while it is taken.
enum Pending {
    Idle,
    Taking {
        turn: TurnKey,
        done: Shared<BoxFuture<'static, ()>>,
    },
}

/// The workspace snapshots of one top-level session.
pub struct TurnSnapshots {
    store: Store,
    /// One git operation on the store at a time.
    gate: tokio::sync::Mutex<()>,
    pending: Mutex<Pending>,
}

impl std::fmt::Debug for TurnSnapshots {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("TurnSnapshots")
            .field("store", &self.store)
            .finish_non_exhaustive()
    }
}

/// One path compared between a snapshot and the workspace.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Entry {
    path: String,
    before: Option<Blob>,
    now: Option<Blob>,
    reach: Reach,
}

impl TurnSnapshots {
    /// The snapshots of session `session_id` in `workspace`, kept under the
    /// work root of `agent_dir`; `None` when it has no work root.
    #[must_use]
    pub fn open(agent_dir: &Path, session_id: &str, workspace: &Path) -> Option<Self> {
        let work_root = eukhe_types::platform::dirs::work_root_of(agent_dir)?;
        let git_dir = work_root
            .join(SNAPSHOTS_DIR)
            .join(format!("{session_id}.git"));
        let state = [agent_dir.to_path_buf(), work_root];
        Some(Self {
            store: Store::new(git_dir, workspace.to_path_buf(), &state),
            gate: tokio::sync::Mutex::new(()),
            pending: Mutex::new(Pending::Idle),
        })
    }

    /// Start the snapshot of `turn`, the start of the root session's run
    /// `run`, unless it is started already.
    pub(crate) fn begin(self: &Arc<Self>, turn: TurnKey, run: u64) {
        let mut pending = self.pending.lock().unwrap_or_else(PoisonError::into_inner);
        match &*pending {
            Pending::Taking { turn: taking, .. } if *taking == turn => return,
            Pending::Taking { .. } | Pending::Idle => {}
        }
        let this = Arc::clone(self);
        let done = async move {
            if let Err(error) = this.take_turn(run).await {
                tracing::warn!(%error, "the turn's workspace snapshot failed");
            }
        }
        .boxed()
        .shared();
        tokio::spawn(done.clone());
        *pending = Pending::Taking { turn, done };
    }

    /// Wait for the snapshot of the current turn, if one is being taken.
    pub(crate) async fn ready(&self) {
        let done = match &*self.pending.lock().unwrap_or_else(PoisonError::into_inner) {
            Pending::Idle => None,
            Pending::Taking { done, .. } => Some(done.clone()),
        };
        if let Some(done) = done {
            done.await;
        }
    }

    /// Snapshot the workspace as the start of a new turn, the start of the
    /// root session's run `run`; its number. A turn whose snapshot fails
    /// still counts: it is recorded as lost (why, in the store), so `/undo`
    /// stops at its start and never takes back two turns at once.
    ///
    /// # Errors
    ///
    /// Git or file IO failed, or the workspace is too large.
    pub async fn take_turn(&self, run: u64) -> Result<u64, UndoError> {
        let _gate = self.gate.lock().await;
        let old = match self.store.load().await {
            Ok(old) => old,
            Err(error @ UndoError::Unread { .. }) => return Err(error),
            Err(error) => {
                self.lose(None, &error);
                return Err(error);
            }
        };
        let turn = old
            .state
            .live
            .iter()
            .chain(old.state.base.iter())
            .max()
            .map_or(1, |turn| turn.saturating_add(1));
        match self.start_turn(turn, run, &old.state).await {
            Ok(()) => Ok(turn),
            Err(error) => {
                self.lose(Some(turn), &error);
                Err(error)
            }
        }
    }

    /// The snapshots' answer to the start of `turn`, and its snapshot and
    /// run kept.
    async fn start_turn(&self, turn: u64, run: u64, old: &Snapshots) -> Result<(), UndoError> {
        let (new, act) = rules::step(old, Event::TurnStart { turn })?;
        match act {
            Act::Took => {}
            Act::Restore { .. } | Act::Refused | Act::Compare { .. } | Act::NoSnapshot => {
                return Err(UndoError::Answer(format!("{act:?}"), "a turn start"));
            }
        }
        let taken = self.store.take().await?;
        self.store.keep(turn, &taken).await?;
        self.store.keep_run(turn, run)?;
        if new.base == Some(turn) && old.base != Some(turn) {
            self.store.keep_base(turn, &taken.tree).await?;
        }
        self.store.forget(old, &new).await
    }

    /// Record that the snapshot of `turn` (`None`: of a turn whose number
    /// the unread store hides) failed with `error`.
    fn lose(&self, turn: Option<u64>, error: &UndoError) {
        let reason = error.to_string();
        let reason = reason.lines().next().unwrap_or_default().trim();
        let reason: String = reason.chars().take(REASON_CHARS).collect();
        if let Err(record) = self.store.lose(turn, &reason) {
            tracing::warn!(%record, %error, "recording a turn without a workspace snapshot failed");
        }
    }

    /// Restore the workspace to its snapshot at the start of the newest
    /// turn not undone; the reply names the irreversible effects of that
    /// turn's run in `ledger` (the root session's), which it does not take
    /// back.
    ///
    /// # Errors
    ///
    /// [`UndoError::NothingToUndo`] when no snapshot is left,
    /// [`UndoError::NoTurnSnapshot`] when that turn has none (nothing
    /// changes); git or file IO failed.
    pub async fn undo(&self, ledger: &EffectsState) -> Result<UndoReply, UndoError> {
        let _gate = self.gate.lock().await;
        let old = self.store.load().await?;
        let (new, act) = rules::step(&old.state, Event::Undo)?;
        let turn = match act {
            Act::Restore { turn } => turn,
            Act::Refused => return Err(UndoError::NothingToUndo),
            Act::Took | Act::Compare { .. } | Act::NoSnapshot => {
                return Err(UndoError::Answer(format!("{act:?}"), "/undo"));
            }
        };
        kept(&old, turn)?;
        let not_undone = not_undone(ledger, self.store.run_of(turn)?)?;
        let entries = self.compare(turn).await?;
        let fixes = rules::fixes(&rows_of(&entries))?;
        let restored = restore::apply(&self.store, &entries, &fixes).await?;
        self.store.forget(&old.state, &new).await?;
        // The turns a later /undo restores: up to the first one without a
        // snapshot, where it stops.
        let left = new
            .live
            .iter()
            .take_while(|turn| !old.lost.contains_key(turn))
            .count();
        Ok(UndoReply {
            restored,
            turn,
            left: u64::try_from(left).unwrap_or(u64::MAX),
            not_undone,
        })
    }

    /// What changed in the workspace since the start of the newest turn
    /// not undone (`Turn`) or of the session's first turn (`Run`).
    ///
    /// # Errors
    ///
    /// [`UndoError::NothingToDiff`] before the first turn,
    /// [`UndoError::NoTurnSnapshot`] when that turn has none; git IO
    /// failed.
    pub async fn diff(&self, scope: DiffScope) -> Result<TurnDiffReply, UndoError> {
        let _gate = self.gate.lock().await;
        let old = self.store.load().await?;
        let (_, act) = rules::step(&old.state, Event::Diff(scope))?;
        let turn = match act {
            Act::Compare { turn } => turn,
            Act::NoSnapshot => return Err(UndoError::NothingToDiff),
            Act::Took | Act::Restore { .. } | Act::Refused => {
                return Err(UndoError::Answer(format!("{act:?}"), "/diff"));
            }
        };
        kept(&old, turn)?;
        let snapshot = self.store.snapshot(turn).await?;
        let now = self.store.take().await?;
        let entries = self.entries(&snapshot, &now).await?;
        let seens = rules::seens(&rows_of(&entries))?;
        let pick = |wanted: Seen| -> Vec<String> {
            entries
                .iter()
                .zip(&seens)
                .filter(|(_, seen)| **seen == wanted)
                .map(|(entry, _)| entry.path.clone())
                .collect()
        };
        let paths = pick(Seen::Differs);
        let diff = self
            .store
            .unified(&snapshot.tree, &now.tree, &paths)
            .await?;
        Ok(TurnDiffReply {
            diff: cut(diff),
            paths,
            skipped: pick(Seen::Skipped),
        })
    }

    /// The paths that differ between the snapshot of `turn` and the
    /// workspace now, and the held ones.
    async fn compare(&self, turn: u64) -> Result<Vec<Entry>, UndoError> {
        let snapshot = self.store.snapshot(turn).await?;
        let now = self.store.take().await?;
        self.entries(&snapshot, &now).await
    }

    async fn entries(&self, snapshot: &Taken, now: &Taken) -> Result<Vec<Entry>, UndoError> {
        let changes = self.store.changes(&snapshot.tree, &now.tree).await?;
        let gone: Vec<String> = changes
            .iter()
            .filter(|change| change.now.is_none())
            .map(|change| change.path.clone())
            .collect();
        let ignored = self.store.ignored(&gone).await?;
        let held: BTreeSet<String> = snapshot.held.union(&now.held).cloned().collect();
        Ok(entries_of(changes, &held, &ignored))
    }
}

/// Is `path` held back by `held` (a path, or a nested repository `dir/`
/// above it)?
fn is_held(path: &str, held: &BTreeSet<String>) -> bool {
    held.contains(path)
        || held
            .iter()
            .any(|dir| dir.ends_with('/') && path.starts_with(dir.as_str()))
}

/// The compared paths: each change, held when a snapshot held it back or
/// the workspace ignores it now, then each held path no change names,
/// sorted by path.
fn entries_of(
    changes: Vec<Change>,
    held: &BTreeSet<String>,
    ignored: &BTreeSet<String>,
) -> Vec<Entry> {
    let named: BTreeSet<String> = changes.iter().map(|change| change.path.clone()).collect();
    let mut entries: Vec<Entry> = changes
        .into_iter()
        .map(|change| Entry {
            reach: if is_held(&change.path, held) || ignored.contains(&change.path) {
                Reach::Held
            } else {
                Reach::Open
            },
            path: change.path,
            before: change.before,
            now: change.now,
        })
        .chain(
            held.iter()
                .filter(|path| !named.contains(*path))
                .map(|path| Entry {
                    path: path.clone(),
                    before: None,
                    now: None,
                    reach: Reach::Held,
                }),
        )
        .collect();
    entries.sort_by(|a, b| a.path.cmp(&b.path));
    entries
}

/// The rows of `entries` for the compiled core: each blob numbered.
fn rows_of(entries: &[Entry]) -> Vec<Row> {
    let changes: Vec<Change> = entries
        .iter()
        .map(|entry| Change {
            path: entry.path.clone(),
            before: entry.before.clone(),
            now: entry.now.clone(),
        })
        .collect();
    let numbers = store::blob_numbers(&changes);
    let number = |blob: &Option<Blob>| blob.as_ref().and_then(|blob| numbers.get(blob).copied());
    entries
        .iter()
        .map(|entry| Row {
            before: number(&entry.before),
            now: number(&entry.now),
            reach: entry.reach,
        })
        .collect()
}

/// `diff`, cut after [`DIFF_CAP_BYTES`] with a line that says so.
fn cut(diff: String) -> String {
    if diff.len() <= DIFF_CAP_BYTES {
        return diff;
    }
    let end = (0..=DIFF_CAP_BYTES)
        .rev()
        .find(|at| diff.is_char_boundary(*at))
        .unwrap_or(0);
    format!(
        "{}\n[the diff is cut at {} MiB]\n",
        &diff[..end],
        DIFF_CAP_BYTES / (1024 * 1024)
    )
}

/// Every fix of `fixes`, paired with its entry: the ones that change a
/// path.
fn changed<'a>(entries: &'a [Entry], fixes: &'a [Fix]) -> impl Iterator<Item = (&'a Entry, Fix)> {
    entries
        .iter()
        .zip(fixes.iter().copied())
        .filter(|(_, fix)| *fix != Fix::Keep)
}
