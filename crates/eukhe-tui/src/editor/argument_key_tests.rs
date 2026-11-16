//! The argument text of a slash command at the keys
//! (`eukhe_types::slash_arguments`): its rows open as it is typed, Tab
//! completes the token and opens the next place's rows, Enter runs a
//! line typed in full, and the ghost hint names what a place expects.

use eukhe_types::slash_arguments::LiveValues;

use super::{Editor, EditorEvent};

/// Keys typed with a pause after each: the parked menu request
/// materializes between keys, as at a real keyboard.
fn type_slowly(e: &mut Editor, text: &str) {
    for (at, c) in text.char_indices() {
        e.handle_input(&text[at..at + c.len_utf8()]);
        e.materialize_autocomplete();
    }
}

fn key(e: &mut Editor, key: &str) {
    e.handle_input(key);
    e.materialize_autocomplete();
}

fn menu_values(e: &Editor) -> Vec<String> {
    e.autocomplete_state()
        .map(|state| state.items.iter().map(|item| item.value.clone()).collect())
        .unwrap_or_default()
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

#[test]
fn budget_words_then_keys_complete_with_tab() {
    let mut e = Editor::new();
    type_slowly(&mut e, "/bud");
    key(&mut e, "tab");
    assert_eq!(
        (e.get_text(), menu_values(&e)),
        (
            "/budget ".to_string(),
            ["set", "add", "audit", "on", "off"]
                .map(String::from)
                .to_vec()
        )
    );
    type_slowly(&mut e, "s");
    key(&mut e, "tab");
    assert_eq!(
        (e.get_text(), menu_values(&e)),
        (
            "/budget set ".to_string(),
            ["cost=", "tokens=", "time=", "calls=", "requests="]
                .map(String::from)
                .to_vec()
        )
    );
    type_slowly(&mut e, "ti");
    key(&mut e, "tab");
    assert_eq!(
        (e.get_text(), e.is_showing_autocomplete(), e.ghost_hint()),
        (
            "/budget set time=".to_string(),
            false,
            Some("<duration>".to_string())
        )
    );
    type_slowly(&mut e, "10m");
    key(&mut e, "enter");
    assert_eq!(submitted(&mut e), ["/budget set time=10m"]);
}

#[test]
fn a_flag_shows_what_its_value_is() {
    let mut e = Editor::new();
    type_slowly(&mut e, "/loop 7 --u");
    assert_eq!(menu_values(&e), ["--until"]);
    assert_eq!(
        e.ghost_hint().as_deref(),
        Some("ntil '<command>'|<condition in words>")
    );
    key(&mut e, "tab");
    assert_eq!(
        (e.get_text(), e.ghost_hint()),
        (
            "/loop 7 --until ".to_string(),
            Some("'<command>'|<condition in words>".to_string())
        )
    );
}

#[test]
fn enter_runs_a_word_typed_in_full_and_completes_a_partial_one() {
    let mut e = Editor::new();
    type_slowly(&mut e, "/budget audit");
    assert_eq!(menu_values(&e), ["audit"]);
    key(&mut e, "enter");
    assert_eq!(submitted(&mut e), ["/budget audit"]);

    let mut partial = Editor::new();
    type_slowly(&mut partial, "/accept cm");
    key(&mut partial, "enter");
    assert_eq!(
        (partial.get_text(), menu_values(&partial)),
        (
            "/accept cmd ".to_string(),
            ["--expect", "--timeout", "--protect"]
                .map(String::from)
                .to_vec()
        )
    );
}

#[test]
fn effect_ids_complete_from_the_live_ledger_in_their_case() {
    let mut e = Editor::new();
    let row = |id: &str| crate::autocomplete::CompletionItem {
        value: id.to_string(),
        label: id.to_string(),
        description: Some("bash: make test".to_string()),
        argument_hint: None,
        source_tag: None,
        path_row: None,
    };
    e.set_autocomplete_live_values(
        LiveValues::OpenEffects,
        vec![row("toolu_01AbC"), row("job:7")],
    );
    type_slowly(&mut e, "/effects ran ");
    assert_eq!(menu_values(&e), ["toolu_01AbC", "job:7"]);
    type_slowly(&mut e, "T");
    key(&mut e, "tab");
    assert_eq!(e.get_text(), "/effects ran toolu_01AbC ");
}

#[test]
fn a_command_without_words_shows_its_usage_after_the_space() {
    let mut e = Editor::new();
    type_slowly(&mut e, "/compact ");
    assert_eq!(e.ghost_hint().as_deref(), Some("[instructions]"));
    type_slowly(&mut e, "keep");
    assert_eq!(e.ghost_hint(), None);
}
