//! Escape on the empty global view entered from a chat (agents-back or
//! bare `/resume`) returns to that chat; a startup launch exits.

use super::*;

#[test]
fn escape_returns_to_the_chat_the_view_was_entered_from() {
    let mut mode = mode_with_parent_and_child();
    mode.options.return_active_session_id = Some("p-live".to_string());
    let selected_row_identity = mode.selected_identity.clone().unwrap_or_default();
    let selected_key = mode.selected_key.clone().unwrap_or_default();
    mode.handle_key("escape");
    assert_eq!(
        mode.opened,
        Some(OpenedRow {
            selection: SessionSelection::Attach("p-live".to_string()),
            expanded_ancestors: Vec::new(),
            selected_row_identity,
            selected_key,
            rlm_depth: Some(0),
            has_children: true,
            status_message: None,
            cwd: None,
        })
    );
    assert!(!mode.running);
}

#[test]
fn escape_without_a_return_chat_exits_the_view() {
    let mut mode = mode_with_parent_and_child();
    mode.handle_key("escape");
    assert_eq!(mode.opened, None);
    assert!(!mode.running);
}

/// F5: opening another session than the chat the view was entered from
/// leaves that chat (its finish detaches it as a switch); Escape back to
/// it, or opening its own row, leaves nothing.
#[test]
fn opening_another_session_leaves_the_return_chat() {
    // Escape returns to the chat: nothing left.
    let mut back = mode_with_parent_and_child();
    back.options.return_active_session_id = Some("p-live".to_string());
    back.handle_key("escape");
    // Enter on the selected parent row, the chat's own session.
    let mut same = mode_with_parent_and_child();
    same.options.return_active_session_id = Some("p-live".to_string());
    same.handle_key("enter");
    // Enter on the parent row from the child's chat: another session.
    let mut other = mode_with_parent_and_child();
    other.options.return_active_session_id = Some("c-live".to_string());
    other.handle_key("enter");
    // A startup launch has no chat to leave.
    let mut startup = mode_with_parent_and_child();
    startup.handle_key("enter");
    assert_eq!(
        (
            back.left_return_chat(),
            same.left_return_chat(),
            other.left_return_chat(),
            startup.left_return_chat(),
        ),
        (None, None, Some("c-live".to_string()), None)
    );
}
