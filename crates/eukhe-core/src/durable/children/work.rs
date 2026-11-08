//! The work a session did, as the stall checks measure it (rule H5 for a
//! subagent's parent watch, `LAWS.bend`; the goal loop's progress
//! check): the number of distinct acts.
//!
//! An act is a tool call with its result (the tool's name and arguments,
//! and the result's text, images and error flag), or an accepted progress
//! note. Two acts are the same when the model sees the same thing: call
//! ids, timestamps, usage, and the text and thinking around the call do
//! not count. So a session that does new work grows its count, and a
//! session that loops (the same calls with the same results, retries,
//! answers that only say it waits) does not, however many events it
//! streams.
//!
//! The ledger is the stepper of the compiled Bend core's `work` entry
//! (`bend/ffi_work.bend`, model `next` in `bend/progress.bend`, laws
//! `laws/work.bend`): it decides what each block of an entry adds, which
//! acts are new, which entries it reads, and the count. This host only
//! moves bytes: it hashes each block's bytes into a fingerprint, sends the
//! transcript's entries, and keeps the core's last answer.

use std::hash::{DefaultHasher, Hash, Hasher};

use eukhe_bend::wire::{Reader, WireError, Writer, NAT_MAX};
use eukhe_bend::{Entry, Stepper};
use eukhe_durable::types::{EntryId, EntryRecord};
use eukhe_types::pi_ai::{AssistantContentBlock, Message, UserContentBlock};

/// The distinct acts of a session, as the compiled core's ledger counts
/// them.
#[derive(Debug, Default)]
pub struct WorkLedger {
    /// The ledger in the compiled core; opened at the first event.
    core: Option<Stepper>,
    /// The core's last answer: the work, how many entries of the shown
    /// view it read, and the id of the last entry it read.
    work: u64,
    read: usize,
    last: Option<EntryId>,
}

/// An answer of the core's ledger.
enum Answer {
    /// The ledger read the event.
    Read,
    /// The view no longer holds what the ledger read: it started over, and
    /// wants the view from its start.
    Again,
}

impl WorkLedger {
    /// Read the shown view's entries (the whole transcript, append order):
    /// the core reads those it did not read yet, or all of them again when
    /// the view no longer holds the last entry it read at its place (a
    /// replaced view).
    pub fn read_entries(&mut self, entries: &[EntryRecord]) {
        let answer = match self.view(entries) {
            Ok(Answer::Again) => {
                self.read = 0;
                self.view(entries).and_then(|answer| match answer {
                    Answer::Read => Ok(answer),
                    // The core reads a view from its start whatever it
                    // read before (laws/work.bend work_entry_history).
                    Answer::Again => Err(WireError::Malformed {
                        at: 0,
                        expected: "a ledger that reads a view from its start",
                    }
                    .into()),
                })
            }
            answer => answer,
        };
        eukhe_bend::expect_core(Entry::Work, answer);
    }

    /// Read a page of entries in id order: the core reads those newer than
    /// the last entry it read.
    pub fn read_page(&mut self, entries: &[EntryRecord]) {
        let mut request = Writer::new();
        request.tag(1);
        put_entries(&mut request, entries);
        let answer = self.send(request);
        eukhe_bend::expect_core(Entry::Work, answer);
    }

    /// Read an accepted progress note.
    pub fn read_note(&mut self, text: &str) {
        let mut request = Writer::new();
        request.tag(2).nat(fingerprint(&("note", text)));
        let answer = self.send(request);
        eukhe_bend::expect_core(Entry::Work, answer);
    }

    /// The id of the last entry read; `None` before any.
    #[must_use]
    pub fn last(&self) -> Option<EntryId> {
        self.last
    }

    /// The number of distinct acts read.
    #[must_use]
    pub fn count(&self) -> u64 {
        self.work
    }

    /// Send the view: the id of its entry at the place of the last entry
    /// the core read, and its entries from that place on.
    fn view(&mut self, entries: &[EntryRecord]) -> Result<Answer, eukhe_bend::Error> {
        let at = self
            .read
            .checked_sub(1)
            .and_then(|place| entries.get(place));
        let mut request = Writer::new();
        request.tag(0);
        match at {
            None => request.none(),
            Some(entry) => request.some().nat(entry.id.get().min(NAT_MAX)),
        };
        put_entries(&mut request, entries.get(self.read..).unwrap_or_default());
        self.send(request)
    }

    /// One event to the core's ledger; keeps its answer.
    fn send(&mut self, mut request: Writer) -> Result<Answer, eukhe_bend::Error> {
        let request = request.finish()?;
        let core = if let Some(core) = self.core.take() {
            core
        } else {
            let (core, reply) = Stepper::open(Entry::Work, "")?;
            Reader::reply(&reply)?.end()?;
            core
        };
        let core = self.core.insert(core);
        let reply = core.step(&request)?;
        let mut reply = Reader::reply(&reply)?;
        let answer = match reply.tag_of(2, "a ledger's answer")? {
            0 => {
                let work = reply.nat()?;
                let read = reply.nat()?;
                let last = if reply.maybe()? {
                    Some(EntryId::from_number(reply.nat()?))
                } else {
                    None
                };
                self.work = work;
                self.read = usize::try_from(read).unwrap_or(usize::MAX);
                self.last = last;
                Answer::Read
            }
            // `tag_of` answers a tag below 2: this is 1.
            _ => Answer::Again,
        };
        reply.end()?;
        Ok(answer)
    }
}

/// A fingerprint of `value`'s bytes, below 2^46 (the wire carries Nats
/// below 10^14).
fn fingerprint(value: &impl Hash) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    short(&hasher)
}

/// The hash `hasher` holds, below 2^46.
fn short(hasher: &DefaultHasher) -> u64 {
    hasher.finish() >> 18
}

/// The entries, each its id and its blocks: a call (the fingerprints of
/// its id, and of its name and arguments), a result (the fingerprints of
/// its call's id, and of its tool name, content and error flag), text,
/// thinking, a user message, a system message.
fn put_entries(request: &mut Writer, entries: &[EntryRecord]) {
    request.count(entries.len());
    for entry in entries {
        request.nat(entry.id.get().min(NAT_MAX));
        let blocks = entry
            .model
            .iter()
            .flatten()
            .map(|message| match message {
                Message::Assistant(assistant) => assistant.content.len(),
                Message::ToolResult(_) | Message::System(_) | Message::User(_) => 1,
            })
            .sum();
        request.count(blocks);
        for message in entry.model.iter().flatten() {
            match message {
                Message::Assistant(assistant) => {
                    for block in &assistant.content {
                        match block {
                            AssistantContentBlock::ToolCall(call) => {
                                request.tag(0).nat(fingerprint(&call.id)).nat(fingerprint(&(
                                    "call",
                                    &call.name,
                                    &call.arguments,
                                )));
                            }
                            AssistantContentBlock::Text(_) => {
                                request.tag(2);
                            }
                            AssistantContentBlock::Thinking(_) => {
                                request.tag(3);
                            }
                        }
                    }
                }
                Message::ToolResult(result) => {
                    let mut hasher = DefaultHasher::new();
                    "result".hash(&mut hasher);
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
                    request
                        .tag(1)
                        .nat(fingerprint(&result.tool_call_id))
                        .nat(short(&hasher));
                }
                Message::User(_) => {
                    request.tag(4);
                }
                Message::System(_) => {
                    request.tag(5);
                }
            }
        }
    }
}
