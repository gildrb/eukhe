//! The ephemeral progress of running tool calls.
//!
//! What a running call reports (its output window and dropped counts, its
//! details, diagnostics, and usage) reaches the live observers of its
//! conversation through this board and never reaches storage: the durable
//! records of one call are its start (the `running` slot with the
//! `execute` checkpoint) and its settle commit, which carries the whole
//! result. A crash loses what the board held, so a call that a crash
//! interrupted settles from what is durable.

use std::collections::HashMap;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError, Weak};

use eukhe_chord::delta::overlap;
use eukhe_chord::json::JsonValue;

use crate::harness::events::ToolOutputUpdate;
use crate::harness::live::SlotProgress;
use crate::harness::types::ToolDiagnostic;
use crate::types::{ConversationId, TaskId};

/// How far back a new output window is searched for the text it shares
/// with the last one, in UTF-16 code units (as Chord's string diff).
const OVERLAP_SCAN: usize = 65_536;

/// One change of a running call's progress, as its observers get it: each
/// field is absent when it did not change.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ProgressChange {
    pub(crate) output: Option<ToolOutputUpdate>,
    /// The new details; `null` when they were removed.
    pub(crate) details: Option<JsonValue>,
    /// Every diagnostic so far.
    pub(crate) diagnostics: Option<Vec<ToolDiagnostic>>,
}

/// Receives each change of a call of its conversation: the call's task,
/// its whole progress after the change, and the change. Runs while the
/// board is locked, so it must not block or publish.
pub(crate) type Deliver = Arc<dyn Fn(TaskId, &SlotProgress, &ProgressChange) + Send + Sync>;

/// Reads everything a running call reported so far.
pub(crate) type Source = Box<dyn Fn() -> SlotProgress + Send + Sync>;

struct Watcher {
    id: u64,
    conversation_id: ConversationId,
    deliver: Deliver,
}

/// One running call on the board.
struct Call {
    conversation_id: ConversationId,
    source: Source,
    /// What the watchers got last.
    published: SlotProgress,
}

#[derive(Default)]
struct Board {
    calls: HashMap<TaskId, Call>,
    watchers: Vec<Watcher>,
    next_watcher: u64,
}

/// The Harness's board of running tool calls' progress: in memory only.
/// Clones share it.
#[derive(Clone, Default)]
pub struct LiveProgress {
    board: Arc<Mutex<Board>>,
}

/// Stops one watch of the board; idempotent.
pub(crate) type StopWatch = Box<dyn FnOnce() + Send>;

fn lock(board: &Mutex<Board>) -> MutexGuard<'_, Board> {
    board.lock().unwrap_or_else(PoisonError::into_inner)
}

/// UTF-8 byte offset of `units` UTF-16 code units into `text`.
fn utf16_to_byte(text: &str, units: usize) -> usize {
    let mut count = 0;
    for (index, c) in text.char_indices() {
        if count >= units {
            return index;
        }
        count += c.len_utf16();
    }
    text.len()
}

/// The output change from `before` to `after`, as Chord diffs a string: an
/// append, a trim of the front plus an append of what follows the shared
/// part, or the whole window when the bounded overlap search finds nothing.
fn output_change(before: Option<&str>, after: Option<&str>) -> Option<ToolOutputUpdate> {
    let set = |text: &str| ToolOutputUpdate::Set {
        set: text.to_owned(),
    };
    match (before, after) {
        (before, after) if before == after => None,
        (_, None) => Some(set("")),
        (None, Some(after)) => Some(set(after)),
        (Some(before), Some(after)) => {
            if let Some(appended) = after.strip_prefix(before) {
                return Some(ToolOutputUpdate::Window {
                    trim_start: None,
                    append: Some(appended.to_owned()),
                });
            }
            let shared = overlap(before, after, OVERLAP_SCAN);
            if shared == 0 {
                return Some(set(after));
            }
            let appended = &after[utf16_to_byte(after, shared)..];
            Some(ToolOutputUpdate::Window {
                trim_start: Some(before.encode_utf16().count() - shared),
                append: (!appended.is_empty()).then(|| appended.to_owned()),
            })
        }
    }
}

/// The size of `change`: what a progress publication paces itself by.
fn change_bytes(change: &ProgressChange) -> usize {
    let output = match &change.output {
        Some(ToolOutputUpdate::Set { set }) => set.len(),
        Some(ToolOutputUpdate::Window { append, .. }) => append.as_ref().map_or(0, String::len),
        None => 0,
    };
    let details = change
        .details
        .as_ref()
        .map_or(0, |details| details.to_string().len());
    let diagnostics = change.diagnostics.as_ref().map_or(0, |diagnostics| {
        serde_json::to_string(diagnostics).map_or(0, |text| text.len())
    });
    output + details + diagnostics
}

impl LiveProgress {
    /// Put the running call `task_id` of `conversation_id` on the board;
    /// `source` reads what it reported. A call that is not on the board
    /// publishes nothing.
    pub(crate) fn start(&self, conversation_id: ConversationId, task_id: TaskId, source: Source) {
        lock(&self.board).calls.insert(
            task_id,
            Call {
                conversation_id,
                source,
                published: SlotProgress::default(),
            },
        );
    }

    /// Publish the progress of the running call `task_id`: read what it
    /// reported and hand what changed since its last publication to the
    /// watchers of its conversation. Returns the size of the change.
    pub(crate) fn publish(&self, task_id: TaskId) -> usize {
        let mut board = lock(&self.board);
        let Board {
            calls, watchers, ..
        } = &mut *board;
        let Some(call) = calls.get_mut(&task_id) else {
            return 0;
        };
        let progress = (call.source)();
        let previous = &call.published;
        let change = ProgressChange {
            output: output_change(previous.output.as_deref(), progress.output.as_deref()),
            details: (previous.details != progress.details)
                .then(|| progress.details.clone().unwrap_or(JsonValue::Null)),
            diagnostics: (previous.diagnostics != progress.diagnostics)
                .then(|| progress.diagnostics.clone().unwrap_or_default()),
        };
        let bytes = change_bytes(&change);
        let changed =
            change.output.is_some() || change.details.is_some() || change.diagnostics.is_some();
        if changed {
            for watcher in watchers.iter() {
                if watcher.conversation_id == call.conversation_id {
                    (watcher.deliver)(task_id, &progress, &change);
                }
            }
        }
        call.published = progress;
        bytes
    }

    /// Everything the call `task_id` reported, read now: it settles with
    /// this. The call stays on the board until [`Self::remove`], so a settle
    /// whose commit did not land, and the settle that follows it, still
    /// read it. `None` for a call that is not on the board, as every call
    /// after a crash.
    pub(crate) fn read(&self, task_id: TaskId) -> Option<SlotProgress> {
        lock(&self.board)
            .calls
            .get(&task_id)
            .map(|call| (call.source)())
    }

    /// Take the call `task_id` off the board once its settle committed.
    pub(crate) fn remove(&self, task_id: TaskId) {
        lock(&self.board).calls.remove(&task_id);
    }

    /// Watch the calls of `conversation_id`: what each of its running calls
    /// published last, and `deliver` for every later change, from the same
    /// instant. The returned function stops the watch.
    pub(crate) fn watch(
        &self,
        conversation_id: ConversationId,
        deliver: Deliver,
    ) -> (HashMap<TaskId, SlotProgress>, StopWatch) {
        let mut board = lock(&self.board);
        let current = board
            .calls
            .iter()
            .filter(|(_, call)| call.conversation_id == conversation_id)
            .map(|(task_id, call)| (*task_id, call.published.clone()))
            .collect();
        board.next_watcher += 1;
        let id = board.next_watcher;
        board.watchers.push(Watcher {
            id,
            conversation_id,
            deliver,
        });
        let weak: Weak<Mutex<Board>> = Arc::downgrade(&self.board);
        let stop: StopWatch = Box::new(move || {
            if let Some(board) = weak.upgrade() {
                lock(&board).watchers.retain(|watcher| watcher.id != id);
            }
        });
        (current, stop)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn window(trim_start: Option<usize>, append: Option<&str>) -> ToolOutputUpdate {
        ToolOutputUpdate::Window {
            trim_start,
            append: append.map(str::to_owned),
        }
    }

    fn set(text: &str) -> ToolOutputUpdate {
        ToolOutputUpdate::Set {
            set: text.to_owned(),
        }
    }

    #[test]
    fn diffs_an_output_window_as_chord_diffs_the_string() {
        assert_eq!(output_change(Some("ab"), Some("ab")), None);
        assert_eq!(output_change(None, Some("ab")), Some(set("ab")));
        assert_eq!(
            output_change(Some("ab"), Some("abc")),
            Some(window(None, Some("c")))
        );
        assert_eq!(
            output_change(Some("a\nb\n"), Some("b\nc\n")),
            Some(window(Some(2), Some("c\n")))
        );
        assert_eq!(
            output_change(Some("a\nb\n"), Some("b\n")),
            Some(window(Some(2), None))
        );
        assert_eq!(output_change(Some("ab"), Some("xy")), Some(set("xy")));
    }

    #[test]
    fn hands_each_change_to_the_watchers_of_its_conversation_and_settles_with_the_latest() {
        let board = LiveProgress::default();
        let (one, two) = (
            ConversationId::from_number(1),
            ConversationId::from_number(2),
        );
        let task = TaskId::from_number(7);
        let progress = |text: &str| SlotProgress {
            output: Some(text.to_owned()),
            ..SlotProgress::default()
        };
        let reported = Arc::new(Mutex::new("a".to_owned()));
        let source: Source = {
            let reported = Arc::clone(&reported);
            Box::new(move || progress(&reported.lock().unwrap_or_else(PoisonError::into_inner)))
        };
        let report = |text: &str| {
            *reported.lock().unwrap_or_else(PoisonError::into_inner) = text.to_owned();
        };
        board.start(one, task, source);
        board.publish(task);
        let seen = Arc::new(Mutex::new(Vec::new()));
        let deliver: Deliver = {
            let seen = Arc::clone(&seen);
            Arc::new(move |task_id, _progress, change| {
                seen.lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push((task_id, change.clone()));
            })
        };
        let (current, stop) = board.watch(one, Arc::clone(&deliver));
        let (other, stop_other) = board.watch(two, deliver);
        assert_eq!(
            (current, other),
            (HashMap::from([(task, progress("a"))]), HashMap::new())
        );
        report("ab");
        assert_eq!(board.publish(task), 1);
        stop();
        report("abc");
        board.publish(task);
        stop_other();
        // Reported after the last publication: the settle still carries it.
        report("abcd");
        assert_eq!(
            seen.lock().unwrap_or_else(PoisonError::into_inner).clone(),
            vec![(
                task,
                ProgressChange {
                    output: Some(window(None, Some("b"))),
                    details: None,
                    diagnostics: None,
                }
            )]
        );
        // A settle reads it and keeps the call until its commit landed.
        assert_eq!(board.read(task), Some(progress("abcd")));
        assert_eq!(board.read(task), Some(progress("abcd")));
        board.remove(task);
        assert_eq!((board.read(task), board.publish(task)), (None, 0));
    }
}
