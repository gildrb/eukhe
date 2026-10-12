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
