use super::*;
use crate::theme::ColorMode;

fn kb() -> KeybindingsManager {
    KeybindingsManager::new()
}

fn model(provider: &str, id: &str, name: &str) -> Model {
    serde_json::from_value(serde_json::json!({
        "id": id, "name": name, "api": "openai-completions", "provider": provider,
        "baseUrl": "https://x.test", "reasoning": false, "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 1000, "maxTokens": 100
    }))
    .expect("model")
}

fn catalog() -> Vec<Model> {
    vec![
        model("anthropic", "claude-haiku-5-5", "Claude Haiku 5.5"),
        model("anthropic", "claude-sonnet-5", "Claude Sonnet 5"),
        model("openai-codex", "gpt-6-sol", "GPT-6 Sol"),
    ]
}

fn keys(list: &[&str]) -> Vec<String> {
    list.iter().map(ToString::to_string).collect()
}

fn only(list: &[&str]) -> Scope {
    Scope::Only(keys(list))
}

fn all() -> Vec<String> {
    keys(&[
        "anthropic/claude-haiku-5-5",
        "anthropic/claude-sonnet-5",
        "openai-codex/gpt-6-sol",
    ])
}

/// Toggling from "every model" leaves the others; toggling the last one
/// back collapses to "every model"; reordering moves within the list.
#[test]
fn scope_edits() {
    let all = all();
    let scope = toggled(&Scope::All, &all, "anthropic/claude-sonnet-5");
    assert_eq!(
        scope,
        only(&["anthropic/claude-haiku-5-5", "openai-codex/gpt-6-sol"])
    );
    assert_eq!(
        toggled(&scope, &all, "anthropic/claude-sonnet-5"),
        Scope::All
    );
    assert_eq!(
        moved(&scope, "openai-codex/gpt-6-sol", Step::Earlier),
        only(&["openai-codex/gpt-6-sol", "anthropic/claude-haiku-5-5"])
    );
    assert_eq!(moved(&scope, "openai-codex/gpt-6-sol", Step::Later), scope);
    assert_eq!(
        with_disabled(&Scope::All, &all, &keys(&["openai-codex/gpt-6-sol"])),
        only(&["anthropic/claude-haiku-5-5", "anthropic/claude-sonnet-5"])
    );
    assert_eq!(
        with_enabled(&only(&["x/gone"]), &all, &all),
        only(&[
            "x/gone",
            "anthropic/claude-haiku-5-5",
            "anthropic/claude-sonnet-5",
            "openai-codex/gpt-6-sol"
        ])
    );
    assert_eq!(
        listed_keys(&only(&["openai-codex/gpt-6-sol", "x/gone"]), &all),
        keys(&[
            "openai-codex/gpt-6-sol",
            "x/gone",
            "anthropic/claude-haiku-5-5",
            "anthropic/claude-sonnet-5"
        ])
    );
}

/// The keys: Enter toggles the selected row, the provider key switches
/// a provider's models together, the reorder keys move the enabled
/// selection, the save key reports the scope, Esc closes.
#[test]
fn keys_edit_the_scope() {
    let mut selector = ScopedModelsSelector::new(catalog(), Scope::All, HashMap::new(), 30);
    assert_eq!(
        selector.handle_key("enter", &kb()),
        ScopedModelsAction::Changed(only(&[
            "anthropic/claude-sonnet-5",
            "openai-codex/gpt-6-sol"
        ]))
    );
    // The provider key on a row of a provider not wholly enabled
    // enables it, appended in catalog order.
    assert_eq!(
        selector.handle_key("ctrl+p", &kb()),
        ScopedModelsAction::Changed(Scope::All)
    );
    selector.handle_key("ctrl+x", &kb());
    assert_eq!(selector.scope(), &Scope::Only(Vec::new()));
    // Select the codex row (the third listed) and enable it, then
    // Haiku; move Haiku first.
    selector.handle_key("down", &kb());
    selector.handle_key("down", &kb());
    selector.handle_key("enter", &kb());
    assert_eq!(selector.scope(), &only(&["openai-codex/gpt-6-sol"]));
    selector.handle_key("down", &kb());
    selector.handle_key("enter", &kb());
    assert_eq!(
        selector.scope(),
        &only(&["openai-codex/gpt-6-sol", "anthropic/claude-haiku-5-5"])
    );
    assert_eq!(
        selector.handle_key("alt+up", &kb()),
        ScopedModelsAction::Changed(only(&[
            "anthropic/claude-haiku-5-5",
            "openai-codex/gpt-6-sol"
        ]))
    );
    assert_eq!(
        selector.handle_key("ctrl+s", &kb()),
        ScopedModelsAction::Save(only(&[
            "anthropic/claude-haiku-5-5",
            "openai-codex/gpt-6-sol"
        ]))
    );
    assert_eq!(
        selector.handle_key("escape", &kb()),
        ScopedModelsAction::Close
    );
}

/// The frame: title with the count, note, search field, a checked row
/// per enabled model with its provider, the selected key, the hint; an
/// edit marks the count unsaved.
#[test]
fn renders_rows_and_hint() {
    let theme = Theme::builtin("eukhe", ColorMode::TrueColor);
    let mut selector = ScopedModelsSelector::new(
        catalog(),
        only(&["openai-codex/gpt-6-sol", "x/gone"]),
        HashMap::new(),
        30,
    );
    let text = |selector: &ScopedModelsSelector| -> Vec<String> {
        selector
            .render(&theme, 80, &kb())
            .iter()
            .map(|line| {
                line.iter()
                    .map(|span| span.content.as_str())
                    .collect::<String>()
                    .trim_end()
                    .to_string()
            })
            .collect()
    };
    let rows = text(&selector);
    assert_eq!(rows[0], " Scoped models  1/3 enabled, 1 unavailable");
    assert_eq!(
        rows[1],
        " Applies to this session; Ctrl+S saves it to settings."
    );
    assert_eq!(
        rows[5],
        format!("> [x] GPT-6 Sol{}openai-codex", " ".repeat(53))
    );
    assert_eq!(
        rows[6],
        format!("  [ ] x/gone{}unavailable", " ".repeat(57))
    );
    assert_eq!(
        rows[7],
        format!("  [ ] Claude Haiku 5.5{}anthropic", " ".repeat(49))
    );
    assert_eq!(rows[9], "  openai-codex/gpt-6-sol");
    assert!(rows[10].starts_with(" Enter toggle - "), "{}", rows[10]);
    selector.handle_key("down", &kb());
    selector.handle_key("down", &kb());
    selector.handle_key("enter", &kb());
    let rows = text(&selector);
    assert_eq!(
        rows[0],
        " Scoped models  2/3 enabled, 1 unavailable (unsaved)"
    );
}
