//! The work a session did, as the stall checks measure it (rule H5 for a
//! subagent's parent watch, `docs/harness.md`; the goal loop's progress
//! check, `docs/control.md`): the number of distinct acts.
//!
//! An act is a tool call with its result (the tool's name and arguments,
//! and the result's text, images and error flag), or an accepted progress
//! note. Two acts are the same when the model sees the same thing: call
//! ids, timestamps, usage, and the text and thinking around the call do
//! not count. So a session that does new work grows its count, and a
//! session that loops (the same calls with the same results, retries,
//! answers that only say it waits) does not, however many events it
//! streams. `bend/progress.bend` models the count (`work`),
//! `LAWS.bend` section `progress` states what it guarantees, and the bridge test
//! (`goals/hooks/bridge.rs`) runs both on the same scenarios.

use std::collections::{HashMap, HashSet};
use std::hash::{DefaultHasher, Hash, Hasher};

use eukhe_durable::types::{EntryId, EntryRecord};
use eukhe_types::pi_ai::{AssistantContentBlock, Message, UserContentBlock};

/// The distinct acts of a session. It reads each entry once, in append
/// order.
#[derive(Debug, Default)]
pub struct WorkLedger {
    /// The fingerprints of every act seen.
    seen: HashSet<u64>,
    /// The fingerprints of the calls whose result did not come yet, by
    /// call id.
    calls: HashMap<String, u64>,
    /// How many entries of the transcript [`Self::read_entries`] read.
    read: usize,
    /// The id of the last entry read.
    last: Option<EntryId>,
}

impl WorkLedger {
    /// Read the entries of `entries` (the whole transcript, append order)
    /// that the ledger did not read yet. A transcript that does not hold
    /// the last entry read at its place any more (a replaced view) is read
    /// again from the start.
    pub fn read_entries(&mut self, entries: &[EntryRecord]) {
        let kept = match self.read.checked_sub(1) {
            None => true,
            Some(at) => entries.get(at).map(|entry| entry.id) == self.last,
        };
        if !kept {
            *self = Self::default();
        }
        for entry in &entries[self.read..] {
            self.read_entry(entry);
        }
        self.read = entries.len();
    }

    /// Read one entry, the next one in append order.
    pub fn read_entry(&mut self, entry: &EntryRecord) {
        self.last = Some(entry.id);
        for message in entry.model.iter().flatten() {
            match message {
                Message::Assistant(assistant) => {
                    for block in &assistant.content {
                        match block {
                            AssistantContentBlock::ToolCall(call) => {
                                let mut hasher = DefaultHasher::new();
                                call.name.hash(&mut hasher);
                                call.arguments.hash(&mut hasher);
                                self.calls.insert(call.id.clone(), hasher.finish());
                            }
                            AssistantContentBlock::Text(_) | AssistantContentBlock::Thinking(_) => {
                            }
                        }
                    }
                }
                Message::ToolResult(result) => {
                    let mut hasher = DefaultHasher::new();
                    "call".hash(&mut hasher);
                    self.calls.remove(&result.tool_call_id).hash(&mut hasher);
                    result.tool_name.hash(&mut hasher);
                    for block in &result.content {
                        match block {
                            UserContentBlock::Text(text) => {
                                "text".hash(&mut hasher);
                                text.text.hash(&mut hasher);
                            }
                            UserContentBlock::Image(image) => {
                                "image".hash(&mut hasher);
                                image.mime_type.hash(&mut hasher);
                                image.data.hash(&mut hasher);
                            }
                        }
                    }
                    result.is_error.hash(&mut hasher);
                    self.seen.insert(hasher.finish());
                }
                Message::System(_) | Message::User(_) => {}
            }
        }
    }

    /// The id of the last entry read; `None` before any.
    #[must_use]
    pub fn last(&self) -> Option<EntryId> {
        self.last
    }

    /// Read an accepted progress note.
    pub fn read_note(&mut self, text: &str) {
        let mut hasher = DefaultHasher::new();
        "note".hash(&mut hasher);
        text.hash(&mut hasher);
        self.seen.insert(hasher.finish());
    }

    /// The number of distinct acts read.
    #[must_use]
    pub fn count(&self) -> u64 {
        u64::try_from(self.seen.len()).unwrap_or(u64::MAX)
    }
}
