//! The chat memory in the interactive client: `/memory` prints the memory's
//! status and the view the agent sees (or one zoom) as inline transcript
//! rows, every live `memory_update` lands as one row, and both keep the
//! status line's `mem` gauge current. All of it is display only.

use eukhe_types::daemon::{MemoryReply, MemoryUpdate, MemoryZoom, MEMORY_CAPABILITY};

use super::{AgentView, ChatEntry, DaemonCommand, Duration, Map, SessionUi, UI_REQUEST_TIMEOUT_MS};
use crate::memory_block::{memory_update_view_bytes, MemoryViewRow};

const MEMORY_USAGE: &str = "Usage: /memory [zoom <id> <n>]";

/// What `/memory` asks for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MemoryRequest {
    /// The status and the whole view.
    View,
    /// `zoom(id, n)`: the messages under one view line, a level down.
    Zoom(MemoryZoom),
}

/// `/memory`'s arguments: none, or `zoom <id> <n>` (`n` positive); `None`
/// for anything else.
fn parse_memory_args(args: &str) -> Option<MemoryRequest> {
    let words: Vec<&str> = args.split_whitespace().collect();
    match words.as_slice() {
        [] => Some(MemoryRequest::View),
        ["zoom", id, count] => {
            let id = id.parse().ok()?;
            let count = count.parse().ok().filter(|count: &u64| *count > 0)?;
            Some(MemoryRequest::Zoom(MemoryZoom { id, count }))
        }
        _ => None,
    }
}

impl SessionUi {
    /// `/memory [zoom <id> <n>]`: ask the daemon for the chat memory and
    /// print the answer inline. Bad arguments keep the text in the editor
    /// with the usage; a daemon without the `memory` lane says so.
    pub(super) async fn handle_memory_command(
        &mut self,
        args: &str,
        text: &str,
        view: &mut AgentView,
    ) {
        let Some(request) = parse_memory_args(args) else {
            view.editor.set_text(text);
            self.error_row(MEMORY_USAGE, view);
            return;
        };
        if !self.client.supports_server_capability(MEMORY_CAPABILITY) {
            self.error_row(
                "this daemon does not serve the chat memory; restart it to update",
                view,
            );
            return;
        }
        let zoom = match request {
            MemoryRequest::View => None,
            MemoryRequest::Zoom(zoom) => Some(zoom),
        };
        let reply = self
            .bounded_request(
                Duration::from_millis(UI_REQUEST_TIMEOUT_MS),
                DaemonCommand::GetMemory {
                    id: None,
                    active_session_id: self.active_session_id.clone(),
                    zoom,
                    rest: Map::default(),
                },
            )
            .await
            .and_then(|data| {
                serde_json::from_value::<MemoryReply>(data)
                    .map_err(|error| anyhow::anyhow!("malformed get_memory reply: {error}"))
            });
        match reply {
            Ok(MemoryReply { memory: None }) => {
                self.note("This session keeps no chat memory.", view);
            }
            Ok(MemoryReply {
                memory: Some(snapshot),
            }) => {
                self.set_memory_view_bytes(snapshot.status.view_bytes, view);
                view.push_entry(ChatEntry::MemoryView(Box::new(MemoryViewRow {
                    zoom,
                    snapshot,
                })));
                self.last_status_index = None;
                self.dirty = true;
            }
            Err(error) => self.error_row(&format!("{error:#}"), view),
        }
    }

    /// One live `memory_update`: its transcript row (whether or not a turn
    /// runs; folded into the previous memory row while that is still the
    /// transcript's last entry) and the gauge's new view size.
    pub(super) fn apply_memory_update(&mut self, update: MemoryUpdate, view: &mut AgentView) {
        self.set_memory_view_bytes(memory_update_view_bytes(&update), view);
        view.push_memory_update(update);
        self.last_status_index = None;
        self.dirty = true;
    }

    /// The gauge's reading for this session, mirrored into the chrome.
    pub(super) fn set_memory_view_bytes(&mut self, bytes: u64, view: &mut AgentView) {
        self.memory_view_bytes = Some(bytes);
        view.chrome.memory_view_bytes = Some(bytes);
        self.dirty = true;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn memory_args_parse_the_view_or_one_zoom() {
        assert_eq!(
            ["", "  ", "zoom 40 8", " zoom  0 1 "].map(parse_memory_args),
            [
                Some(MemoryRequest::View),
                Some(MemoryRequest::View),
                Some(MemoryRequest::Zoom(MemoryZoom { id: 40, count: 8 })),
                Some(MemoryRequest::Zoom(MemoryZoom { id: 0, count: 1 })),
            ]
        );
    }

    #[test]
    fn malformed_memory_args_are_refused() {
        assert_eq!(
            [
                "zoom",
                "zoom 40",
                "zoom 40 0",
                "zoom x 8",
                "zoom 40 8 9",
                "view",
                "zoom -1 2"
            ]
            .map(parse_memory_args),
            [None; 7]
        );
    }
}
