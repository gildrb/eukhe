//! A rebuilt command table under an open menu: the session's skill
//! catalog (`get_commands`) and the argument lists land whenever their
//! fetch answers, so the user may already have a menu open. Rather than
//! keep the open list as it was until the next keystroke, the open
//! slash menu reads its rows again from the new table and stays open.

use super::{Editor, EditorEvent};
use crate::autocomplete::{CombinedAutocompleteProvider, CompletionItem, SlashCommandEntry};

fn command(name: &str) -> SlashCommandEntry {
    SlashCommandEntry {
        name: name.to_string(),
        aliases: Vec::new(),
        description: None,
        argument_hint: None,
        takes_argument: false,
        source_tag: None,
        subcommands: &[],
        subcommand_optional: false,
    }
}

fn item(value: &str) -> CompletionItem {
    CompletionItem {
        value: value.to_string(),
        label: value.to_string(),
        description: None,
        argument_hint: None,
        source_tag: None,
        path_row: None,
    }
}

/// An editor over three builtin commands and the given skills.
fn ed(skills: &[&str]) -> Editor {
    let mut e = Editor::new();
    e.set_autocomplete_provider(Box::new(CombinedAutocompleteProvider::new(
        vec![command("session"), command("settings"), command("skills")],
        std::env::current_dir().unwrap_or_default(),
    )));
    e.set_autocomplete_skill_commands(skills.iter().map(|name| command(name)).collect());
    e
}

/// Keys typed with a pause after each (the parked menu request
/// materializes between keys, as at a real keyboard).
fn type_slowly(e: &mut Editor, text: &str) {
    for c in text.chars() {
        e.handle_input(&c.to_string());
        e.materialize_autocomplete();
    }
}

fn menu_values(e: &Editor) -> Vec<String> {
    e.autocomplete_state()
        .map(|state| state.items.iter().map(|item| item.value.clone()).collect())
        .unwrap_or_default()
}

fn selected(e: &Editor) -> Option<String> {
    e.autocomplete_state()
        .and_then(crate::autocomplete::AutocompleteState::selected_item)
        .map(|item| item.value)
}

fn menu_closed(e: &mut Editor) -> bool {
    e.take_events()
        .iter()
        .any(|event| matches!(event, EditorEvent::AutocompleteToggled(false)))
}

/// The regression: `/s` typed right after the TUI start, then the skill
/// catalog lands. The menu stays open, lists the new skill, keeps the
/// row the user moved to, and every row names its place in the new
/// table.
#[test]
fn an_open_slash_menu_stays_open_when_the_skill_catalog_lands() {
    let mut e = ed(&[]);
    type_slowly(&mut e, "/s");
    assert_eq!(menu_values(&e).len(), 3, "the three builtins match `/s`");
    e.handle_input("down");
    let moved_to = selected(&e).expect("a selected row");
    e.take_events();

    e.set_autocomplete_skill_commands(vec![command("skill:scan")]);

    assert!(e.is_showing_autocomplete(), "the menu stays open");
    assert!(!menu_closed(&mut e), "no close event");
    let values = menu_values(&e);
    assert_eq!(
        values.len(),
        4,
        "the builtins and the new skill: {values:?}"
    );
    assert!(values.contains(&"skill:scan".to_string()), "{values:?}");
    assert_eq!(selected(&e), Some(moved_to), "the selection stays");
    let table = e.command_table().expect("the command table");
    for item in &e.autocomplete_state().expect("open menu").items {
        assert_eq!(
            item.path_row,
            table.place(&[item.value.to_lowercase()]),
            "{} names its place in the new table",
            item.value
        );
    }
}

/// The selected row is gone from the new catalog: the menu stays open
/// on the rows that remain, with one of them selected.
#[test]
fn a_selected_row_the_new_catalog_drops_moves_the_selection() {
    let mut e = ed(&["skill:scan", "skill:web"]);
    type_slowly(&mut e, "/skill:");
    let before = menu_values(&e);
    assert!(before.contains(&"skill:web".to_string()), "{before:?}");
    while selected(&e).as_deref() != Some("skill:web") {
        e.handle_input("down");
    }
    e.take_events();

    e.set_autocomplete_skill_commands(vec![command("skill:scan")]);

    assert!(e.is_showing_autocomplete(), "the menu stays open");
    let after = menu_values(&e);
    assert!(!after.contains(&"skill:web".to_string()), "{after:?}");
    let selected = selected(&e).expect("a selected row");
    assert!(
        after.contains(&selected),
        "{selected} is a row of {after:?}"
    );
}

/// No row of the new catalog matches the typed text: the menu closes
/// (and says so).
#[test]
fn a_menu_with_no_row_in_the_new_catalog_closes() {
    let mut e = ed(&["skill:web"]);
    type_slowly(&mut e, "/skill:w");
    assert_eq!(menu_values(&e), ["skill:web"]);
    e.take_events();

    e.set_autocomplete_skill_commands(Vec::new());

    assert!(!e.is_showing_autocomplete(), "nothing left to list");
    assert!(menu_closed(&mut e), "the close event fires");
}

/// A file menu has no table rows: the catalog leaves it as it is.
#[test]
fn an_open_file_menu_is_untouched_by_the_skill_catalog() {
    let mut e = ed(&[]);
    e.handle_input(".");
    e.handle_input("/");
    e.handle_input("tab");
    e.materialize_autocomplete();
    let before = menu_values(&e);
    assert!(before.len() > 1, "the cwd lists as a file menu: {before:?}");
    e.handle_input("down");
    let moved_to = selected(&e);
    e.take_events();

    e.set_autocomplete_skill_commands(vec![command("skill:scan")]);

    assert_eq!(menu_values(&e), before, "the same rows");
    assert_eq!(selected(&e), moved_to, "the same selection");
    assert!(!menu_closed(&mut e), "no close event");
}

/// A changed argument list rebuilds the table too (`/tier`'s tiers
/// follow the model): the open menu shows the new list.
#[test]
fn an_open_argument_menu_follows_a_changed_argument_list() {
    let mut e = Editor::new();
    e.set_autocomplete_argument_completions("tier", vec![item("default"), item("priority")]);
    type_slowly(&mut e, "/tier ");
    assert_eq!(menu_values(&e), ["default", "priority"]);
    e.handle_input("down");
    assert_eq!(selected(&e).as_deref(), Some("priority"));
    e.take_events();

    e.set_autocomplete_argument_completions(
        "tier",
        vec![item("default"), item("flex"), item("priority")],
    );

    assert_eq!(menu_values(&e), ["default", "flex", "priority"]);
    assert_eq!(selected(&e).as_deref(), Some("priority"));
    assert!(!menu_closed(&mut e), "no close event");
}
