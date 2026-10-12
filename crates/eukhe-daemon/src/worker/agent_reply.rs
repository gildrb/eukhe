//! A family agent's answer to the user's `@name` message. The prompt names
//! the session the user typed it in (`replyTo`); the answering agent
//! commits an owed-reply bookkeeping row before the input, and every run
//! end looks at its latest owed reply: once the run the input started has
//! a final answer, the answer goes to the user's session over the
//! supervisor (`agent_reply`). That session commits it as one
//! `agent_reply` row keyed by the owed reply's id, so a redelivery (a
//! restarted agent re-sending) never lands twice; the row shows
//! `name -> you`, logs to chat memory as `[name] answer`, and never starts
//! a turn.

use std::collections::HashSet;
use std::path::PathBuf;
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::agent_messaging::{
    create_agent_reply_prompt, AGENT_MESSAGE_CUSTOM_TYPE, AGENT_REPLY_CUSTOM_TYPE,
    AGENT_REPLY_OWED_CUSTOM_TYPE,
};
use eukhe_core::durable::{custom_entry_draft, CustomEntryData, CUSTOM_ENTRY};
use eukhe_durable::harness::types::WriteSubmissionDraft;
use eukhe_durable::types::EntryRecord;
use eukhe_types::pi_ai::UserContent;
use serde_json::{json, Value};

use super::durable_host::wire_messages::{entry_data, entry_wire_message};
use super::{HostedSession, SessionCore, Worker};
use crate::protocol::{response_failure, response_success, DaemonResponse};

/// How long one delivery waits on the supervisor.
const DELIVERY_TIMEOUT: Duration = Duration::from_secs(10);

/// One reply an agent owes the session a user's `@name` message came from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct OwedReply {
    /// The durable id: the receiving row's dedupe key.
    pub(crate) id: String,
    /// The live session the user sent the message from.
    pub(crate) reply_to: String,
}

/// Whether `entry` is an owed-reply bookkeeping row.
fn is_owed_row(entry: &EntryRecord) -> bool {
    entry.kind == CUSTOM_ENTRY.kind()
        && entry_data::<CustomEntryData>(entry)
            .is_some_and(|data| data.custom_type == AGENT_REPLY_OWED_CUSTOM_TYPE)
}

/// The latest owed reply among `messages` (the shown conversation's wire
/// messages) and, once the run its input started has one, its final
/// answer: the last assistant message that stopped with text before the
/// next input (a user message or a delivered agent message) after its own.
pub(crate) fn latest_owed_reply(messages: &[Value]) -> Option<(OwedReply, Option<String>)> {
    let (index, owed) = messages
        .iter()
        .enumerate()
        .rev()
        .find_map(|(index, message)| {
            if message.get("customType").and_then(Value::as_str)
                != Some(AGENT_REPLY_OWED_CUSTOM_TYPE)
            {
                return None;
            }
            let details = message.get("details")?;
            let text = |key: &str| details.get(key).and_then(Value::as_str).map(str::to_string);
            Some((
                index,
                OwedReply {
                    id: text("id")?,
                    reply_to: text("replyTo")?,
                },
            ))
        })?;
    let is_input = |message: &Value| {
        crate::types::message_role(message) == Some("user")
            || message.get("customType").and_then(Value::as_str) == Some(AGENT_MESSAGE_CUSTOM_TYPE)
    };
    let mut inputs = 0;
    let mut answer = None;
    for message in &messages[index + 1..] {
        if is_input(message) {
            inputs += 1;
            if inputs > 1 {
                break;
            }
            continue;
        }
        if crate::types::message_role(message) == Some("assistant")
            && message.get("stopReason").and_then(Value::as_str) == Some("stop")
        {
            let text = crate::types::message_text(message);
            if !text.trim().is_empty() {
                answer = Some(text);
            }
        }
    }
    Some((owed, answer))
}

/// The worker's owed-reply delivery: the supervisor socket and the owed
/// ids this process already delivered (a restarted process re-sends its
/// latest once; the receiving row dedupes it).
pub(crate) struct AgentReplies {
    supervisor_socket: PathBuf,
    delivered: Mutex<HashSet<String>>,
}

impl AgentReplies {
    pub(crate) fn new(supervisor_socket: PathBuf) -> Self {
        Self {
            supervisor_socket,
            delivered: Mutex::new(HashSet::new()),
        }
    }

    /// Deliver the latest owed reply of `core`'s shown conversation when
    /// its answer is in and this process has not delivered it yet. A
    /// delivery failure is logged; the next run end retries it.
    pub(crate) async fn deliver_latest(&self, core: &Mutex<SessionCore>) {
        let (owed, answer, from) = {
            let core = core.lock().unwrap_or_else(PoisonError::into_inner);
            let Some(view) = core.view.as_ref() else {
                return;
            };
            // Only the tail from the latest owed row converts to wire
            // messages; a session that owes nothing converts none.
            let entries = &view.translator.mirror().entries;
            let Some(start) = entries.iter().rposition(is_owed_row) else {
                return;
            };
            let messages: Vec<Value> = entries[start..]
                .iter()
                .filter_map(entry_wire_message)
                .collect();
            let Some((owed, Some(answer))) = latest_owed_reply(&messages) else {
                return;
            };
            let from = core
                .session_name
                .clone()
                .filter(|name| !name.is_empty())
                .unwrap_or_else(|| core.active_session_id.clone());
            (owed, answer, from)
        };
        if self.supervisor_socket.as_os_str().is_empty()
            || self
                .delivered
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .contains(&owed.id)
        {
            return;
        }
        let sent = crate::supervisor_link::SupervisorLink::new(self.supervisor_socket.clone())
            .request_success(
                json!({
                    "type": "agent_reply",
                    "activeSessionId": owed.reply_to,
                    "from": from,
                    "text": answer,
                    "replyId": owed.id,
                }),
                DELIVERY_TIMEOUT,
            )
            .await;
        match sent {
            Ok(_) => {
                self.delivered
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .insert(owed.id);
            }
            Err(error) => eprintln!(
                "eukhe-daemon worker: delivering the reply to session {} failed: {error:#}",
                owed.reply_to
            ),
        }
    }
}

impl Worker {
    /// Commit the owed-reply row for a prompt the user sent from
    /// `reply_to` as an `@name` message: hidden bookkeeping, no model
    /// text, written right before the input it stands beside.
    ///
    /// # Errors
    ///
    /// The row write fails.
    pub(crate) async fn write_owed_reply(
        &self,
        hosted: &HostedSession,
        reply_to: &str,
    ) -> anyhow::Result<()> {
        let id = format!("reply_{}", uuid::Uuid::new_v4());
        let entry = custom_entry_draft(
            AGENT_REPLY_OWED_CUSTOM_TYPE,
            UserContent::Text(String::new()),
            false,
            Some(json!({ "id": id, "replyTo": reply_to })),
            crate::util::now_ms(),
        )?;
        hosted
            .main()?
            .submit(
                WriteSubmissionDraft {
                    request_id: Some(format!("agent-reply-owed:{id}")),
                    entry,
                },
                &BACKGROUND_CONTEXT,
            )
            .await?;
        Ok(())
    }

    /// Deliver this session's latest owed reply in the background (a run
    /// ended, or the session just opened with a run already answered).
    pub(crate) fn deliver_owed_reply(&self) {
        let replies = Arc::clone(&self.agent_replies);
        let core = Arc::clone(&self.core);
        tokio::spawn(async move { replies.deliver_latest(&core).await });
    }

    /// `agent_reply`: commit an agent's answer to this session's user as
    /// the `agent_reply` row, once per `replyId` (a redelivery answers the
    /// first row). A write never starts a turn: the row lands at once
    /// when idle, else at the running turn's next boundary.
    pub(crate) async fn handle_agent_reply(&self, payload: &Value) -> DaemonResponse {
        const NAME: &str = "agent_reply";
        let hosted = match self.hosted(NAME) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let field = |key: &str| payload.get(key).and_then(Value::as_str);
        let (Some(from), Some(text), Some(reply_id)) =
            (field("from"), field("text"), field("replyId"))
        else {
            return response_failure(
                None,
                NAME,
                "agent_reply needs from, text, and replyId",
                None,
            );
        };
        let written = async {
            let entry = custom_entry_draft(
                AGENT_REPLY_CUSTOM_TYPE,
                UserContent::Text(create_agent_reply_prompt(from, text)),
                true,
                Some(json!({ "id": reply_id, "from": from, "message": text })),
                crate::util::now_ms(),
            )?;
            hosted
                .main()?
                .submit(
                    WriteSubmissionDraft {
                        request_id: Some(format!("agent-reply:{reply_id}")),
                        entry,
                    },
                    &BACKGROUND_CONTEXT,
                )
                .await?;
            anyhow::Ok(())
        }
        .await;
        match written {
            Ok(()) => response_success(None, NAME, None),
            Err(error) => response_failure(None, NAME, &format!("{error:#}"), None),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn owed(id: &str) -> Value {
        json!({ "role": "custom", "customType": AGENT_REPLY_OWED_CUSTOM_TYPE, "display": false,
                "content": "", "details": { "id": id, "replyTo": "root" } })
    }

    fn user(text: &str) -> Value {
        json!({ "role": "user", "content": text })
    }

    fn assistant(text: &str, stop: &str) -> Value {
        json!({ "role": "assistant", "stopReason": stop,
                "content": [{ "type": "text", "text": text }] })
    }

    /// The latest owed reply's answer is the last stopped assistant text of
    /// the run its input started: tool-use turns are not answers, and the
    /// next input closes the window.
    #[test]
    fn the_answer_is_the_last_stop_text_before_the_next_input() {
        let reply = |id: &str| OwedReply {
            id: id.to_string(),
            reply_to: "root".to_string(),
        };
        let cases = [
            vec![],
            vec![owed("r1"), user("what number?")],
            vec![
                owed("r1"),
                user("what number?"),
                assistant("checking", "toolUse"),
                assistant("I reported 42.", "stop"),
                user("unrelated"),
                assistant("later answer", "stop"),
            ],
            vec![
                owed("r1"),
                user("old"),
                assistant("old answer", "stop"),
                owed("r2"),
                user("new"),
                assistant("  ", "stop"),
            ],
        ];
        assert_eq!(
            cases
                .iter()
                .map(|messages| latest_owed_reply(messages))
                .collect::<Vec<_>>(),
            vec![
                None,
                Some((reply("r1"), None)),
                Some((reply("r1"), Some("I reported 42.".to_string()))),
                Some((reply("r2"), None)),
            ]
        );
    }
}
