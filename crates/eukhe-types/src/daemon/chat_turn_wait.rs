//! The `chat_turn_wait` session event (Rust-native, ephemeral): a root
//! turn of the endless chat waits for the chat's turn lease while another
//! window's turn runs, and the waiting window shows it until the lease is
//! granted or the wait ends.

use serde::{Deserialize, Serialize};

/// The line a waiting window shows (the TUI loader note, the print
/// mode's stderr line).
pub const CHAT_TURN_WAIT_NOTICE: &str = "Waiting for another window's turn…";

/// One `chat_turn_wait` event: `waiting` is `true` when the turn starts
/// waiting for another window's turn, `false` when that wait ends.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type", rename = "chat_turn_wait")]
pub struct ChatTurnWaitEvent {
    pub waiting: bool,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn chat_turn_wait_event_roundtrip() {
        crate::daemon::rt::<ChatTurnWaitEvent>(r#"{"type":"chat_turn_wait","waiting":true}"#);
        crate::daemon::rt::<ChatTurnWaitEvent>(r#"{"type":"chat_turn_wait","waiting":false}"#);
    }
}
