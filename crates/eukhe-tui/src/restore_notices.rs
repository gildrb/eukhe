//! The kernel restore notices a view shows (`ipython_state_restored`).
//!
//! A worker that boots a kernel over a namespace snapshot stores one
//! restore notice in the session. Each attach (a reconnect, a worker
//! restart, a session rebind) and each transcript refetch rebuilds the
//! transcript from every stored message. The view records each restore
//! notice it shows and does not show a recorded notice again. Thus each
//! restore shows its notice once, after any number of attaches
//! (`laws/supervisor.bend` `notice_shown_once` and `notice_per_restore`,
//! the model `bend/notice.bend`).

use std::collections::{HashMap, HashSet};

use eukhe_types::custom_type::CustomType;
use eukhe_types::session::AgentMessage;

/// The restore notices a view showed: for each session id, the stored
/// timestamps of its notices. A notice's timestamp is the time its entry
/// was stored: it is the same in each transcript and each live event of
/// the session.
#[derive(Debug, Default)]
pub(crate) struct RestoreNotices {
    shown: HashMap<String, HashSet<u64>>,
}

/// The stored timestamp of `message` when it is a restore notice.
fn restore_stamp(message: &AgentMessage) -> Option<u64> {
    match message {
        AgentMessage::Custom(custom) => (custom.custom_type
            == CustomType::IpythonStateRestored.as_str())
        .then_some(custom.timestamp),
        AgentMessage::User(_)
        | AgentMessage::Assistant(_)
        | AgentMessage::ToolResult(_)
        | AgentMessage::BashExecution(_)
        | AgentMessage::BranchSummary(_)
        | AgentMessage::CompactionSummary(_) => None,
    }
}

impl RestoreNotices {
    /// Whether the view shows `message` of the session `session_id`: each
    /// message, but not a restore notice that the view showed before.
    pub(crate) fn shows(&self, session_id: &str, message: &AgentMessage) -> bool {
        restore_stamp(message).is_none_or(|stamp| {
            !self
                .shown
                .get(session_id)
                .is_some_and(|shown| shown.contains(&stamp))
        })
    }

    /// Record the restore notices in `messages` of the session
    /// `session_id`: the view shows them now.
    pub(crate) fn record<'a>(
        &mut self,
        session_id: &str,
        messages: impl IntoIterator<Item = &'a AgentMessage>,
    ) {
        for stamp in messages.into_iter().filter_map(restore_stamp) {
            match self.shown.get_mut(session_id) {
                Some(shown) => {
                    shown.insert(stamp);
                }
                None => {
                    self.shown
                        .insert(session_id.to_owned(), HashSet::from([stamp]));
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::fmt::Write as _;

    use serde_json::json;

    use super::*;
    use crate::testing::{compare, Rng, Scenario};

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

    /// Restores, live notices and attaches in any order. The stored
    /// transcript holds the notices among user messages; each attach
    /// rebuilds it the way `attach_session` and `rebuild_transcript` do.
    fn scenario(rng: &mut Rng) -> Scenario {
        let mut notices = RestoreNotices::default();
        let mut stored: Vec<AgentMessage> = Vec::new();
        let mut stamps: Vec<u64> = Vec::new();
        let mut shown: Vec<u64> = Vec::new();
        let mut events = String::new();
        let mut transcript = String::new();
        for _ in 0..rng.range(1, 30) {
            match rng.below(3) {
                0 => {
                    let stamp = 1_000 + stored.len() as u64;
                    events.push_str("r\n");
                    stored.push(user(stamp));
                    stored.push(notice(stamp + 1));
                    stamps.push(stamp + 1);
                    shown.push(0);
                }
                1 => {
                    events.push_str("l\n");
                    if let Some(&newest) = stamps.last() {
                        let message = notice(newest);
                        if notices.shows(SESSION, &message) {
                            notices.record(SESSION, [&message]);
                            *shown.last_mut().expect("a stored notice") += 1;
                        }
                    }
                }
                _ => {
                    events.push_str("c\n");
                    let mut messages = stored.clone();
                    messages.retain(|message| notices.shows(SESSION, message));
                    notices.record(SESSION, &messages);
                    for stamp in messages.iter().filter_map(restore_stamp) {
                        let index = stamps
                            .iter()
                            .position(|stored| *stored == stamp)
                            .expect("a stored notice");
                        shown[index] += 1;
                    }
                }
            }
            transcript.push('s');
            for count in &shown {
                write!(transcript, " {count}").unwrap();
            }
            transcript.push('\n');
        }
        Scenario {
            name: format!("{} restores", stamps.len()),
            events,
            transcript,
        }
    }

    /// Restores, live notices and attaches in any order.
    #[test]
    fn the_restore_notices_run_as_their_model() {
        let mut rng = Rng(0x0de5_7012);
        let scenarios: Vec<Scenario> = (0..60).map(|_| scenario(&mut rng)).collect();
        compare("bend/bridge_notice.bend", scenarios);
    }

    /// A rebuild shows the notices the view did not show yet, and the
    /// notices of another session stay apart.
    #[test]
    fn a_rebuild_shows_only_the_new_notices() {
        let mut notices = RestoreNotices::default();
        notices.record(SESSION, [&notice(5)]);
        let mut messages = vec![user(1), notice(5), user(6), notice(7)];
        messages.retain(|message| notices.shows(SESSION, message));
        assert_eq!(messages, vec![user(1), user(6), notice(7)]);
        assert!(notices.shows("session-2", &notice(5)));
    }
}
