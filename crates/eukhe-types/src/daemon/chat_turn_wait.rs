//! The `chat_turn_wait` session event (Rust-native, ephemeral): a root
//! turn of the endless chat waits for the chat's turn lease while another
//! window's turn runs, and the waiting window shows it until the lease is
//! granted or the wait ends.

/// The line a waiting window shows (the TUI loader note, the print
/// mode's stderr line).
pub const CHAT_TURN_WAIT_NOTICE: &str = "Waiting for another window's turn...";
