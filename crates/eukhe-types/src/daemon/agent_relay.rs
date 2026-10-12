//! The `agent_relay` session event (Rust-native, display-only): when two
//! non-root agents of one family exchange an agent message, the family
//! root's session receives this copy so the user sees the mesh traffic.
//! It is never sent to any model and never enters chat memory.

use serde::{Deserialize, Serialize};

/// One relayed peer message: `from`/`to` are the agents' display names
/// (the session name, else the active session id).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type", rename = "agent_relay")]
pub struct AgentRelayEvent {
    pub from: String,
    pub to: String,
    pub text: String,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn agent_relay_event_roundtrip() {
        crate::daemon::rt::<AgentRelayEvent>(
            r#"{"type":"agent_relay","from":"scout","to":"builder","text":"the api is in core"}"#,
        );
    }
}
