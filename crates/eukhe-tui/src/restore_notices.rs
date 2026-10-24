//! The kernel restore notices a view shows (`ipython_state_restored`).
//!
//! A worker that boots a kernel over a namespace snapshot stores one
//! restore notice in the session. Each attach (a reconnect, a worker
//! restart, a session rebind) and each transcript refetch rebuilds the
//! transcript from every stored message. The view records each restore
//! notice it shows and does not show a recorded notice again. Thus each
//! restore shows its notice once, after any number of attaches.
//!
//! The rule runs as compiled Bend: `bend/notice.bend`, a stepper behind
//! `bend/ffi_notice.bend` whose state (the record) stays in the Bend heap;
//! `laws/notice.bend` pins it. This file only spells each message (its
//! role, or its custom kind and stored timestamp) and each ask on the wire.

use eukhe_bend::wire::{Reader, Writer};
use eukhe_bend::{expect_core, Entry, Error, Stepper};
use eukhe_types::session::AgentMessage;

/// The restore notices a view showed (session id and stored timestamp of
/// each), held by the compiled rule. A notice's timestamp is the time its
/// entry was stored: it is the same in each transcript and each live event
/// of the session.
#[derive(Debug)]
pub(crate) struct RestoreNotices {
    record: Stepper,
}

impl Default for RestoreNotices {
    fn default() -> Self {
        let opened = (|| -> Result<Stepper, Error> {
            let (record, reply) = Stepper::open(Entry::Notice, "")?;
            Reader::reply(&reply)?.end()?;
            Ok(record)
        })();
        RestoreNotices {
            record: expect_core(Entry::Notice, opened),
        }
    }
}

/// `message` on the wire: 0 for any role but a custom message; 1, its
/// kind and its stored timestamp (decimal) for a custom message.
fn put_message(w: &mut Writer, message: &AgentMessage) {
    match message {
        AgentMessage::Custom(custom) => {
            w.tag(1)
                .str(&custom.custom_type)
                .str(&custom.timestamp.to_string());
        }
        AgentMessage::User(_)
        | AgentMessage::Assistant(_)
        | AgentMessage::ToolResult(_)
        | AgentMessage::BashExecution(_)
        | AgentMessage::BranchSummary(_)
        | AgentMessage::CompactionSummary(_) => {
            w.tag(0);
        }
    }
}

impl RestoreNotices {
    /// Whether the view shows `message` of the session `session_id`: each
    /// message, but not a restore notice that the view showed before.
    ///
    /// # Panics
    ///
    /// Only on an inconsistent build (see [`expect_core`]).
    pub(crate) fn shows(&mut self, session_id: &str, message: &AgentMessage) -> bool {
        let shown = (|| -> Result<bool, Error> {
            let mut ask = Writer::new();
            ask.tag(0).str(session_id);
            put_message(&mut ask, message);
            let reply = self.record.step(&ask.finish()?)?;
            let mut reply = Reader::reply(&reply)?;
            let shown = reply.bool()?;
            reply.end()?;
            Ok(shown)
        })();
        expect_core(Entry::Notice, shown)
    }

    /// Record the restore notices in `messages` of the session
    /// `session_id`: the view shows them now.
    ///
    /// # Panics
    ///
    /// Only on an inconsistent build (see [`expect_core`]).
    pub(crate) fn record<'a>(
        &mut self,
        session_id: &str,
        messages: impl IntoIterator<Item = &'a AgentMessage>,
    ) {
        let noted = (|| -> Result<(), Error> {
            let messages: Vec<&AgentMessage> = messages.into_iter().collect();
            let mut ask = Writer::new();
            ask.tag(1).str(session_id).count(messages.len());
            for message in messages {
                put_message(&mut ask, message);
            }
            let reply = self.record.step(&ask.finish()?)?;
            Reader::reply(&reply)?.end()?;
            Ok(())
        })();
        expect_core(Entry::Notice, noted);
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    const SESSION: &str = "session-1";

    fn notice(stamp: u64) -> AgentMessage {
        serde_json::from_value(json!({
            "role": "custom",
            "customType": "ipython_state_restored",
            "content": "[python-state-restored]",
            "display": true,
            "details": { "restored": true },
            "timestamp": stamp,
        }))
        .expect("a restore notice")
    }

    fn user(stamp: u64) -> AgentMessage {
        serde_json::from_value(json!({ "role": "user", "content": "go", "timestamp": stamp }))
            .expect("a user message")
    }

    /// The calls reach the compiled rule: a recorded notice no longer shows
    /// for its session, and still shows for another.
    #[test]
    fn the_record_runs_as_the_compiled_rule() {
        let mut notices = RestoreNotices::default();
        assert!(notices.shows(SESSION, &notice(5)));
        notices.record(SESSION, [&user(1), &notice(5)]);
        assert!(!notices.shows(SESSION, &notice(5)));
        assert!(notices.shows(SESSION, &user(1)));
        assert!(notices.shows("session-2", &notice(5)));
    }
}
