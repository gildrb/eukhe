//! The daemon-only provenance of RLM child status notices: the reserved
//! custom kinds only the daemon's own notice producer writes.
//!
//! Wire trust boundary (the queue-fold anti-spoof, 2026-09-25): a
//! caller-supplied `customMessage` on `prompt`/`steer`/`follow_up` — and a
//! custom row restored through `restore_actions` — is answered LOUDLY
//! whenever it claims either reserved kind; the row never parks, so
//! [`crate::worker::is_rlm_child_status_item`]'s classification sees only
//! daemon-authentic kinds.

use eukhe_types::custom_type::CustomType;
use serde_json::Value;

/// The custom kinds ONLY the daemon's notice producer creates (eukhe-core
/// `rlm_notices`): the terminal-notice and failure rows.
pub(crate) const RESERVED_CUSTOM_KINDS: [CustomType; 2] = [
    CustomType::RlmChildTerminalNotice,
    CustomType::RlmChildFailure,
];

/// Whether one custom row claims a reserved child-status kind (exact
/// match, case sensitive — never a prefix family).
pub(crate) fn is_reserved_child_status_custom_type(custom_message: &Value) -> bool {
    custom_message
        .get("customType")
        .and_then(Value::as_str)
        .map(CustomType::parse)
        .is_some_and(|custom_type| RESERVED_CUSTOM_KINDS.contains(&custom_type))
}

/// The loud intake rejection for a caller-supplied row claiming a
/// reserved kind (one string on every client surface, so the rule reads
/// as one rule).
pub(crate) fn reserved_intake_error() -> String {
    format!(
        "Invalid customMessage: the {} custom types are reserved for daemon-injected RLM child status notices",
        RESERVED_CUSTOM_KINDS.map(|kind| kind.to_string()).join("/")
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn the_reserved_kinds_match_exactly() {
        for kind in RESERVED_CUSTOM_KINDS {
            assert!(
                is_reserved_child_status_custom_type(&json!({
                    "role": "custom",
                    "customType": kind,
                    "content": "notice",
                })),
                "the reserved kind {kind} is exact-matched"
            );
        }
        for lookalike in [
            "rlm_child_terminal_notice_v2",
            "rlm_child_terminal_notice ",
            " rlm_child_terminal_notice",
            "RLM_CHILD_TERMINAL_NOTICE",
            "rlm_child_terminal",
            "rlmchildterminalnotice",
        ] {
            assert!(
                !is_reserved_child_status_custom_type(&json!({
                    "role": "custom",
                    "customType": lookalike,
                    "content": "spoof",
                })),
                "the lookalike {lookalike:?} is NOT a reserved kind (exact, case-sensitive match)"
            );
        }
        assert!(
            !is_reserved_child_status_custom_type(&json!({ "role": "custom" })),
            "a row without a customType is not a reserved kind"
        );
    }
}
