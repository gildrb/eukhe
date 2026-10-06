//! The open-time chat-view fetch (`OptChat` spec section 10: "On start, print the view,
//! so you see what the agent sees"): every session open -- new, resume,
//! switch, reconnect -- asks the daemon for the chat memory's view in the
//! background, off the first-paint path, and the landed view joins the
//! transcript as the collapsed `chat_view_block` row.

use eukhe_types::daemon::{ChatViewReply, ChatViewSnapshot, CHAT_VIEW_CAPABILITY};

use super::{
    AgentView, ChatEntry, DaemonCommand, Duration, Map, SessionUi, StatusKind,
    UI_REQUEST_TIMEOUT_MS,
};

/// A landed `get_chat_view` fetch. A response from an older fetch (a
/// rebind raced it) never applies -- the epoch drops it.
pub(crate) struct ChatViewUpdate {
    pub epoch: u64,
    /// The view (`None`: the session keeps no chat memory), or why the
    /// fetch failed.
    pub view: Result<Option<ChatViewSnapshot>, String>,
}

impl SessionUi {
    /// Fetch the chat memory's view for the session just attached, in the
    /// background: the attach and the first frame never wait on it. A
    /// daemon without the `chat_view` lane is never asked.
    pub(super) fn spawn_chat_view_fetch(&mut self) {
        if !self.client.supports_server_capability(CHAT_VIEW_CAPABILITY) {
            return;
        }
        self.chat_view_epoch += 1;
        let epoch = self.chat_view_epoch;
        let updates = self.chat_view_updates.clone();
        let client = self.client.clone();
        let active_session_id = self.active_session_id.clone();
        tokio::spawn(async move {
            let request = DaemonCommand::GetChatView {
                id: None,
                active_session_id,
                rest: Map::default(),
            };
            let fetched = tokio::time::timeout(
                Duration::from_millis(UI_REQUEST_TIMEOUT_MS),
                client.request_ok(request),
            )
            .await;
            let view = match fetched {
                Ok(Ok(data)) => serde_json::from_value::<ChatViewReply>(data)
                    .map(|reply| reply.view)
                    .map_err(|error| format!("malformed get_chat_view reply: {error}")),
                Ok(Err(error)) => Err(format!("{error:#}")),
                Err(_) => Err(format!(
                    "get_chat_view did not answer within {UI_REQUEST_TIMEOUT_MS} ms"
                )),
            };
            // The run loop owns the receiver; a closed loop has no
            // transcript left to fold the view into.
            let _ = updates.send(ChatViewUpdate { epoch, view });
        });
    }

    /// Fold a landed chat-view fetch into the transcript: the view as the
    /// collapsed block, a failure as a warning row, nothing for a session
    /// without the chat memory or with an empty view (the agent sees
    /// nothing, so there is nothing to print).
    pub(crate) fn apply_chat_view(&mut self, update: ChatViewUpdate, view: &mut AgentView) {
        if update.epoch < self.chat_view_epoch {
            return;
        }
        match update.view {
            Ok(Some(snapshot)) if snapshot.lines > 0 || snapshot.messages > 0 => {
                view.push_entry(ChatEntry::ChatView(Box::new(snapshot)));
                self.last_status_index = None;
                self.dirty = true;
            }
            Ok(Some(_) | None) => {}
            Err(error) => {
                self.note_as(
                    &format!("Chat view unavailable: {error}"),
                    StatusKind::Warning,
                    view,
                );
            }
        }
    }
}
