//! The command paths at the keys (`command_paths`;
//! `laws/command.bend`): a typed path runs itself, Tab and Enter on a menu row
//! descend into its children, Enter submits only a complete path.

use super::{Editor, EditorEvent};

fn ed() -> Editor {
    Editor::new()
}

/// Keys typed with a pause after each: the parked menu request
/// materializes between keys, as at a real keyboard.
fn type_slowly(e: &mut Editor, keys: &[&str]) {
    for key in keys {
        e.handle_input(key);
        e.materialize_autocomplete();
    }
}

fn submitted(e: &mut Editor) -> Vec<String> {
    e.take_events()
        .into_iter()
        .filter_map(|event| match event {
            EditorEvent::Submitted(text) => Some(text),
            _ => None,
        })
        .collect()
}

fn menu_values(e: &Editor) -> Vec<String> {
    e.autocomplete_state()
        .map(|state| state.items.iter().map(|item| item.value.clone()).collect())
        .unwrap_or_default()
}

fn chars(text: &str) -> Vec<&str> {
    text.char_indices()
        .map(|(at, c)| &text[at..at + c.len_utf8()])
        .collect()
}

/// The user's bug: `/memory`, a space, `model`, Enter ran `/memory` (the
/// menu closed at the space, and `model` was the memory view's text). It
/// submits `/memory model`, with or without the pauses.
#[test]
fn memory_space_model_enter_submits_memory_model() {
    let mut e = ed();
    type_slowly(&mut e, &chars("/memory"));
    type_slowly(&mut e, &[" "]);
    assert_eq!(
        menu_values(&e),
        ["view", "model"],
        "the space opens memory's subcommands"
    );
    type_slowly(&mut e, &chars("model"));
    assert_eq!(menu_values(&e), ["model"]);
    e.handle_input("enter");
    assert_eq!(submitted(&mut e), ["/memory model"]);

    let mut burst = ed();
    for key in chars("/memory model") {
        burst.handle_input(key);
    }
    burst.handle_input("enter");
    assert_eq!(submitted(&mut burst), ["/memory model"]);
}

/// Tab on a command row completes it and opens its subcommands at once;
/// Tab on a subcommand row completes it in turn.
#[test]
fn tab_chains_from_the_command_to_its_subcommands() {
    let mut e = ed();
    type_slowly(&mut e, &chars("/mem"));
    type_slowly(&mut e, &["tab"]);
    assert_eq!(e.get_text(), "/memory ");
    assert_eq!(menu_values(&e), ["view", "model"]);
    type_slowly(&mut e, &["m"]);
    type_slowly(&mut e, &["tab"]);
    assert_eq!(e.get_text(), "/memory model");
    assert!(!e.is_showing_autocomplete(), "a leaf has no menu");
    assert!(submitted(&mut e).is_empty(), "Tab never submits");
}

/// Enter on a subcommand row typed in part completes and runs it
/// (`/memory mo` runs memory model); Enter on a command row typed in part
/// opens its subcommands instead of running it.
#[test]
fn enter_on_a_row_completes_then_descends_or_runs() {
    let mut e = ed();
    type_slowly(&mut e, &chars("/memory mo"));
    e.handle_input("enter");
    assert_eq!(submitted(&mut e), ["/memory model"]);

    let mut e = ed();
    type_slowly(&mut e, &chars("/mem"));
    e.handle_input("enter");
    e.materialize_autocomplete();
    assert!(submitted(&mut e).is_empty());
    assert_eq!(e.get_text(), "/memory ");
    assert_eq!(menu_values(&e), ["view", "model"]);
}

/// Enter on a bare command typed in full runs its default; a command
/// without subcommands typed in part completes into its text.
#[test]
fn enter_runs_a_full_path_and_completes_a_partial_one() {
    let mut e = ed();
    type_slowly(&mut e, &chars("/memory"));
    assert!(e.is_showing_autocomplete());
    e.handle_input("enter");
    assert_eq!(submitted(&mut e), ["/memory"]);

    let mut e = ed();
    type_slowly(&mut e, &chars("/go"));
    e.handle_input("enter");
    assert!(submitted(&mut e).is_empty());
    assert_eq!(e.get_text(), "/goal ");
}

/// An unknown subcommand is submitted as typed (the dispatch reports it
/// and runs nothing); a bare path with no default never submits: its
/// menu opens.
#[test]
fn enter_submits_only_a_complete_path() {
    let mut e = ed();
    for key in chars("/memory x") {
        e.handle_input(key);
    }
    e.handle_input("enter");
    assert_eq!(submitted(&mut e), ["/memory x"]);

    let mut e = ed();
    let sizes = ["small", "medium", "large"]
        .into_iter()
        .map(|size| crate::autocomplete::CompletionItem {
            value: size.to_string(),
            label: size.to_string(),
            description: None,
            argument_hint: None,
            source_tag: None,
            path_row: None,
        })
        .collect();
    e.set_autocomplete_argument_completions("dynamic-workflow --size", sizes);
    for key in chars("/dynamic-workflow --size") {
        e.handle_input(key);
    }
    e.handle_input("enter");
    e.materialize_autocomplete();
    assert!(submitted(&mut e).is_empty());
    assert_eq!(e.get_text(), "/dynamic-workflow --size ");
    assert_eq!(menu_values(&e), ["small", "medium", "large"]);
}

/// The ghost hint names the rest of the selected row and its usage.
#[test]
fn the_ghost_hint_shows_the_selected_rows_rest_and_usage() {
    let mut e = ed();
    type_slowly(&mut e, &chars("/workflows s"));
    assert_eq!(e.ghost_hint().as_deref(), Some("ize [small|medium|large]"));
}
