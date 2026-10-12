//! The custom types of the RLM child status rows (TS
//! `rlm_child_terminal_notice` / `rlm_child_failure`). The report text a
//! parent receives is [`super::notice`]'s.

/// A child run that failed (TS `rlm_child_failure`).
pub const RLM_CHILD_FAILURE_CUSTOM_TYPE: &str = "rlm_child_failure";
/// A child run that ended without an explicit reply or was cancelled
/// (TS `rlm_child_terminal_notice`).
pub const RLM_CHILD_TERMINAL_NOTICE_CUSTOM_TYPE: &str = "rlm_child_terminal_notice";
