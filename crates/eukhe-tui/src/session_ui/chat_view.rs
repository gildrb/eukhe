//! The open-time chat-view fetch (`OptChat` spec section 10: "On start, print the view,
//! so you see what the agent sees"): every session open -- new, resume,
//! switch, reconnect -- asks the daemon for the chat memory's view in the
//! background, off the first-paint path, and the landed view joins the
//! transcript as the collapsed `chat_view_block` row. The same fetch reads
//! the memory's status (`get_memory`) to seed the status line's `mem`
//! gauge.

use eukhe_types::daemon::{
    ChatViewReply, ChatViewSnapshot, MemoryReply, MemoryStatusSnapshot, CHAT_VIEW_CAPABILITY,
    MEMORY_CAPABILITY,
};

use super::{
    AgentView, ChatEntry, DaemonCommand, Duration, Map, SessionUi, StatusKind,
    UI_REQUEST_TIMEOUT_MS,
};
use crate::daemon_client::DaemonClient;

/// A landed open-time fetch. A response from an older fetch (a rebind
/// raced it) never applies -- the epoch drops it.
pub(crate) struct ChatViewUpdate {
    pub epoch: u64,
    /// The view (`Ok(None)`: the session keeps no chat memory), or why the
    /// fetch failed; `None` when the daemon lacks the `chat_view` lane.
    pub view: Option<Result<Option<ChatViewSnapshot>, String>>,
    /// The memory's status (`Ok(None)`: no chat memory), or why the fetch
    /// failed; `None` when the daemon lacks the `memory` lane.
    pub memory: Option<Result<Option<MemoryStatusSnapshot>, String>>,
}

/// One bounded daemon request decoded as `T` (the open-time fetch and the
/// `/memory` tree's level fetches).
pub(super) async fn fetch<T: serde::de::DeserializeOwned>(
    client: &DaemonClient,
    request: DaemonCommand,
    name: &str,
) -> Result<T, String> {
    let fetched = tokio::time::timeout(
        Duration::from_millis(UI_REQUEST_TIMEOUT_MS),
        client.request_ok(request),
    )
    .await;
    match fetched {
        Ok(Ok(data)) => serde_json::from_value::<T>(data)
            .map_err(|error| format!("malformed {name} reply: {error}")),
        Ok(Err(error)) => Err(format!("{error:#}")),
        Err(_) => Err(format!(
            "{name} did not answer within {UI_REQUEST_TIMEOUT_MS} ms"
        )),
    }
}

impl SessionUi {
    /// Fetch the chat memory's view and status for the session just
    /// attached, in the background: the attach and the first frame never
    /// wait on it. A daemon without a lane is never asked for it.
    pub(super) fn spawn_chat_view_fetch(&mut self) {
        let wants_view = self.client.supports_server_capability(CHAT_VIEW_CAPABILITY);
        let wants_memory = self.client.supports_server_capability(MEMORY_CAPABILITY);
        if !wants_view && !wants_memory {
            return;
        }
        self.chat_view_epoch += 1;
        let epoch = self.chat_view_epoch;
        let updates = self.chat_view_updates.clone();
        let client = self.client.clone();
        let active_session_id = self.active_session_id.clone();
        tokio::spawn(async move {
            let view = async {
                if !wants_view {
                    return None;
                }
                let request = DaemonCommand::GetChatView {
                    id: None,
                    active_session_id: active_session_id.clone(),
                    rest: Map::default(),
                };
                Some(
                    fetch::<ChatViewReply>(&client, request, "get_chat_view")
                        .await
                        .map(|reply| reply.view),
                )
            };
            let memory = async {
                if !wants_memory {
                    return None;
                }
                let request = DaemonCommand::GetMemory {
                    id: None,
                    active_session_id: active_session_id.clone(),
                    zoom: None,
                    rest: Map::default(),
                };
                Some(
                    fetch::<MemoryReply>(&client, request, "get_memory")
                        .await
                        .map(|reply| reply.memory.map(|memory| memory.status)),
                )
            };
            let (view, memory) = tokio::join!(view, memory);
            // The run loop owns the receiver; a closed loop has no
            // transcript left to fold the view into.
            let _ = updates.send(ChatViewUpdate {
                epoch,
                view,
                memory,
            });
        });
    }

    /// Fold a landed open-time fetch: the view as the collapsed block, the
    /// memory's view size into the gauge, a failure as a warning row;
    /// nothing for a session without the chat memory or with an empty
    /// view (the agent sees nothing, so there is nothing to print).
    pub(crate) fn apply_chat_view(&mut self, update: ChatViewUpdate, view: &mut AgentView) {
        if update.epoch < self.chat_view_epoch {
            return;
        }
        match update.view {
            Some(Ok(Some(snapshot))) if snapshot.lines > 0 || snapshot.messages > 0 => {
                view.push_entry(ChatEntry::ChatView(Box::new(snapshot)));
                self.last_status_index = None;
                self.dirty = true;
            }
            Some(Ok(Some(_) | None)) | None => {}
            Some(Err(error)) => {
                self.note_as(
                    &format!("Chat view unavailable: {error}"),
                    StatusKind::Warning,
                    view,
                );
            }
        }
        match update.memory {
            Some(Ok(Some(status))) => self.set_memory_gauge(
                crate::memory_block::MemoryGauge::seeded(status.view_bytes),
                view,
            ),
            Some(Ok(None)) | None => {}
            Some(Err(error)) => {
                self.note_as(
                    &format!("Chat memory status unavailable: {error}"),
                    StatusKind::Warning,
                    view,
                );
            }
        }
    }
}
