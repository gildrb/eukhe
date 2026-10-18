use super::*;

fn cfg(entries: &[(&str, &[&str])]) -> KeybindingsConfig {
    entries
        .iter()
        .map(|(id, keys)| {
            (
                id.to_string(),
                keys.iter().map(ToString::to_string).collect::<Vec<_>>(),
            )
        })
        .collect()
}

/// A manager over an agent dir whose `binds.cfg` is `script`.
fn with_binds_cfg(script: &str) -> (tempfile::TempDir, KeybindingsManager) {
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(dir.path().join("binds.cfg"), script).unwrap();
    let kb = KeybindingsManager::create(dir.path());
    (dir, kb)
}

fn action(id: &str) -> Command {
    Command::Action { id: id.to_string() }
}

#[test]
fn defaults_match_ts() {
    let kb = KeybindingsManager::new();
    assert!(kb.matches("ctrl+o", "app.tools.expand"));
    assert!(kb.matches("escape", "app.input.clear"));
    assert!(kb.matches("ctrl+w", "tui.editor.deleteWordBackward"));
    assert!(kb.matches("alt+backspace", "tui.editor.deleteWordBackward"));
    assert!(kb.matches("ctrl+-", "tui.editor.undo"));
    assert!(kb.matches("shift+enter", "tui.input.newLine"));
    assert!(!kb.matches("ctrl+o", "app.clear"));
}

/// The definitions sharing a default key share its bind: a press of the
/// key runs every one of their actions (the screen picks its own); an
/// unbound key runs nothing.
#[test]
fn shared_default_keys_run_every_action() {
    let kb = KeybindingsManager::new();
    assert_eq!(
        kb.press("ctrl+o"),
        Ok(vec![
            action("app.tools.expand"),
            action("app.agents.program"),
            action("app.tree.filter.cycleForward"),
        ])
    );
    assert_eq!(kb.press("f9"), Ok(Vec::new()));
}

/// The thinking-level cycles own their default keys alone: no other
/// definition binds shift+tab or shift+alt+tab (the settings menu's
/// shift+tab tab switch is its own raw key, which the menu takes first).
#[test]
fn the_thinking_cycle_keys_have_no_other_action() {
    let kb = KeybindingsManager::new();
    assert_eq!(
        kb.press("shift+tab"),
        Ok(vec![action("app.thinking.cycleForward")])
    );
    assert_eq!(
        kb.press("shift+alt+tab"),
        Ok(vec![action("app.thinking.cycleBackward")])
    );
}

#[test]
fn user_rebind_supersedes_scope_default() {
    let kb = KeybindingsManager::with_user_bindings(&cfg(&[("app.tools.expand", &["ctrl+e"])]));
    assert!(kb.matches("ctrl+e", "app.tools.expand"));
    // ctrl+e is also editor cursorLineEnd default in the same scope:
    // claimed => removed there.
    assert!(!kb.matches("ctrl+e", "tui.editor.cursorLineEnd"));
    assert!(kb.matches("end", "tui.editor.cursorLineEnd"));
    // The rebound action leaves its default key; the key's other
    // actions keep it.
    assert!(!kb.matches("ctrl+o", "app.tools.expand"));
    assert!(kb.matches("ctrl+o", "app.agents.program"));
}

#[test]
fn keeps_shared_defaults_when_user_binding_repeats_own_default() {
    let kb = KeybindingsManager::with_user_bindings(&cfg(&[(
        "tui.input.submit",
        &["enter", "ctrl+enter"],
    )]));
    assert_eq!(
        kb.get_keys("tui.input.submit"),
        vec!["enter".to_string(), "ctrl+enter".to_string()]
    );
    assert_eq!(kb.get_keys("tui.select.confirm"), vec!["enter".to_string()]);
}

#[test]
fn keeps_shared_cursor_defaults_when_user_binding_repeats_own_default() {
    let kb = KeybindingsManager::with_user_bindings(&cfg(&[("tui.select.up", &["up", "ctrl+p"])]));
    assert_eq!(
        kb.get_keys("tui.select.up"),
        vec!["up".to_string(), "ctrl+p".to_string()]
    );
    assert_eq!(kb.get_keys("tui.editor.cursorUp"), vec!["up".to_string()]);
}

#[test]
fn evicts_defaults_claimed_as_added_user_binding() {
    let kb =
        KeybindingsManager::with_user_bindings(&cfg(&[("tui.editor.cursorUp", &["up", "ctrl+b"])]));
    assert_eq!(
        kb.get_keys("tui.editor.cursorUp"),
        vec!["up".to_string(), "ctrl+b".to_string()]
    );
    // cursorLeft loses its ctrl+b default (same editor scope, added claim).
    assert_eq!(
        kb.get_keys("tui.editor.cursorLeft"),
        vec!["left".to_string()]
    );
}

/// Two legacy entries claiming one key both keep it: the imported bind
/// runs both actions.
#[test]
fn legacy_entries_sharing_a_key_share_its_bind() {
    let kb = KeybindingsManager::with_user_bindings(&cfg(&[
        ("tui.editor.cursorUp", &["up", "ctrl+b"]),
        ("tui.editor.cursorLeft", &["left", "ctrl+b"]),
    ]));
    assert_eq!(
        kb.press("ctrl+b"),
        Ok(vec![
            action("tui.editor.cursorUp"),
            action("tui.editor.cursorLeft"),
        ])
    );
    assert_eq!(
        kb.get_keys("tui.editor.cursorLeft"),
        vec!["left".to_string(), "ctrl+b".to_string()]
    );
}

#[test]
fn empty_user_array_disables_binding() {
    let kb = KeybindingsManager::with_user_bindings(&cfg(&[("app.tools.expand", &[])]));
    assert!(kb.get_keys("app.tools.expand").is_empty());
    assert!(!kb.matches("ctrl+o", "app.tools.expand"));
    // The other actions of ctrl+o keep it.
    assert!(kb.matches("ctrl+o", "app.agents.program"));
}

#[test]
fn unknown_user_ids_bind_nothing() {
    assert_eq!(
        legacy_binds(&cfg(&[("not.a.binding", &["ctrl+q"])])),
        Vec::new()
    );
    let kb = KeybindingsManager::with_user_bindings(&cfg(&[("not.a.binding", &["ctrl+q"])]));
    assert!(kb.get_keys("not.a.binding").is_empty());
    assert_eq!(
        kb.get_keys("tui.editor.cursorLineStart"),
        vec![
            "home".to_string(),
            "ctrl+a".to_string(),
            "super+left".to_string()
        ]
    );
}

/// The prompt-editor-keybinds additions (documented divergence from
/// the TS table): redo, the selection families, the doc/paragraph
/// jumps, cut/copy, and transpose resolve with their defaults, and a
/// user override replaces them like any other binding.
#[test]
fn editor_keybind_parity_defaults_resolve() {
    let kb = KeybindingsManager::new();
    assert!(kb.matches("ctrl+shift+z", "tui.editor.redo"));
    assert!(kb.matches("shift+left", "tui.editor.selectLeft"));
    assert!(kb.matches("shift+down", "tui.editor.selectDown"));
    assert!(kb.matches("shift+alt+right", "tui.editor.selectWordRight"));
    assert!(kb.matches("shift+end", "tui.editor.selectLineEnd"));
    assert!(kb.matches("shift+ctrl+down", "tui.editor.selectParagraphDown"));
    assert!(kb.matches("ctrl+t", "tui.editor.transposeChars"));
    assert!(kb.matches("ctrl+x", "tui.editor.cutSelection"));
    assert!(kb.matches("ctrl+shift+c", "tui.editor.copySelection"));
    assert!(kb.matches("ctrl+home", "tui.editor.cursorDocStart"));
    assert!(kb.matches("ctrl+end", "tui.editor.cursorDocEnd"));
    assert!(kb.matches("super+home", "tui.editor.cursorDocStart"));
    assert!(kb.matches("super+end", "tui.editor.cursorDocEnd"));
    // A user rebind replaces the default set.
    let rebound = KeybindingsManager::with_user_bindings(&cfg(&[("tui.editor.redo", &["ctrl+r"])]));
    assert!(rebound.matches("ctrl+r", "tui.editor.redo"));
    assert!(!rebound.matches("ctrl+shift+z", "tui.editor.redo"));
}

/// The list-edge jump defaults (the operator's top/bottom
/// navigation): home/end and their ctrl/super variants select the
/// first/last row. The agents view handles them; home/end stay line
/// motion for every editor-scope consumer.
#[test]
fn list_edge_jump_defaults_resolve() {
    let kb = KeybindingsManager::new();
    for key in ["home", "ctrl+home", "super+home", "super+up"] {
        assert!(
            kb.matches(key, "tui.select.top"),
            "{key} selects the first row"
        );
    }
    for key in ["end", "ctrl+end", "super+end", "super+down"] {
        assert!(
            kb.matches(key, "tui.select.bottom"),
            "{key} selects the last row"
        );
    }
    assert!(kb.matches("home", "tui.editor.cursorLineStart"));
    assert!(kb.matches("end", "tui.editor.cursorLineEnd"));
}

/// The heartbeats shortcut is gone (the operator's 2026-09-24
/// directive: "Remove the shortcut of ctrl+r for heartbeats btw"):
/// ctrl+r binds nothing by default (the /heartbeats command and the
/// activity dock's heartbeats group own the open paths).
#[test]
fn ctrl_r_is_unbound_by_default() {
    let kb = KeybindingsManager::new();
    assert!(kb.get_keys("app.heartbeats.open").is_empty());
    assert!(!kb.matches("ctrl+r", "app.heartbeats.open"));
}

#[test]
fn matching_is_case_and_order_insensitive() {
    let kb = KeybindingsManager::with_user_bindings(&cfg(&[("app.tools.expand", &["Ctrl+O"])]));
    assert!(kb.matches("ctrl+o", "app.tools.expand"));
    // A ctrl+shift binding matches the event id with shift first.
    assert!(kb.matches("shift+ctrl+z", "tui.editor.redo"));
    // "esc" and "escape" name the same key (TS matchesKey).
    assert!(kb.matches("esc", "tui.select.cancel"));
    assert!(kb.matches("escape", "tui.select.cancel"));
    // An empty or trailing-modifier id never matches.
    assert!(!kb.matches("", "app.tools.expand"));
    assert!(!kb.matches("ctrl+", "app.tools.expand"));
    // A binds.cfg key is normalized the same way before binding; the
    // hint keeps its spelling.
    let (_dir, kb) = with_binds_cfg("bind Shift+Ctrl+Q \"action app.clear\"\n");
    assert!(kb.matches("ctrl+shift+q", "app.clear"));
    assert_eq!(
        kb.get_keys("app.clear"),
        vec!["ctrl+c".to_string(), "Shift+Ctrl+Q".to_string()]
    );
}

#[test]
fn migrate_renames_legacy_ids_and_orders() {
    let mut raw = serde_json::Map::new();
    raw.insert("expandTools".to_string(), serde_json::json!("ctrl+x"));
    raw.insert("cursorUp".to_string(), serde_json::json!(["up", "ctrl+p"]));
    raw.insert(
        "app.message.dequeue".to_string(),
        serde_json::json!("alt+u"),
    );
    assert_eq!(
        migrate_keybindings_config(&raw),
        vec![
            (
                "tui.editor.cursorUp".to_string(),
                serde_json::json!(["up", "ctrl+p"])
            ),
            ("app.tools.expand".to_string(), serde_json::json!("ctrl+x")),
            (
                "app.message.navigateOlder".to_string(),
                serde_json::json!("alt+u")
            ),
        ]
    );
}

#[test]
fn migrate_keeps_current_name_when_both_exist() {
    let mut raw = serde_json::Map::new();
    raw.insert("expandTools".to_string(), serde_json::json!("ctrl+x"));
    raw.insert("app.tools.expand".to_string(), serde_json::json!("ctrl+y"));
    assert_eq!(
        migrate_keybindings_config(&raw),
        vec![("app.tools.expand".to_string(), serde_json::json!("ctrl+y"))]
    );
}

/// The one-time import: with no `binds.cfg`, the legacy
/// `keybindings.json` (legacy names migrated, malformed values dropped)
/// is written as `binds.cfg`, and the JSON file stays in place.
#[test]
fn imports_keybindings_json_into_binds_cfg() {
    let dir = tempfile::tempdir().unwrap();
    let legacy = r#"{
  "cursorUp": ["up", "ctrl+b"],
  "app.tools.expand": [],
  "app.subagents.focus": "alt+g",
  "app.model.select": 5
}"#;
    std::fs::write(dir.path().join("keybindings.json"), legacy).unwrap();
    let kb = KeybindingsManager::create(dir.path());
    assert_eq!(
        std::fs::read_to_string(dir.path().join("binds.cfg")).unwrap(),
        "# Key binds, imported from keybindings.json.\n\
         bind alt+g \"action app.subagents.focus\"\n\
         bind ctrl+b \"action tui.editor.cursorUp\"\n\
         bind ctrl+o \"action app.agents.program; action app.tree.filter.cycleForward\"\n\
         bind alt+a \"\"\n"
    );
    assert_eq!(
        std::fs::read_to_string(dir.path().join("keybindings.json")).unwrap(),
        legacy
    );
    assert!(kb.matches("alt+g", "app.subagents.focus"));
    assert!(!kb.matches("alt+a", "app.subagents.focus"));
    assert!(kb.matches("ctrl+l", "app.model.select"));
}

/// Once `binds.cfg` exists it is the only source: a changed
/// `keybindings.json` is never imported again.
#[test]
fn never_reimports_once_binds_cfg_exists() {
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(
        dir.path().join("keybindings.json"),
        r#"{"app.tools.expand": "ctrl+e"}"#,
    )
    .unwrap();
    let mut kb = KeybindingsManager::create(dir.path());
    assert!(kb.matches("ctrl+e", "app.tools.expand"));
    std::fs::write(
        dir.path().join("keybindings.json"),
        r#"{"app.tools.expand": "ctrl+t"}"#,
    )
    .unwrap();
    kb.reload();
    assert!(kb.matches("ctrl+e", "app.tools.expand"));
    assert!(!kb.matches("ctrl+t", "app.tools.expand"));
}

#[test]
fn missing_or_malformed_legacy_file_loads_defaults() {
    let empty = tempfile::tempdir().unwrap();
    let kb = KeybindingsManager::create(empty.path());
    assert!(kb.matches("ctrl+o", "app.tools.expand"));
    assert!(!empty.path().join("binds.cfg").exists());

    for legacy in ["not json", r#"["app.tools.expand"]"#] {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(dir.path().join("keybindings.json"), legacy).unwrap();
        let kb = KeybindingsManager::create(dir.path());
        assert!(kb.matches("ctrl+o", "app.tools.expand"));
        assert_eq!(
            std::fs::read_to_string(dir.path().join("binds.cfg")).unwrap(),
            "# Key binds, imported from keybindings.json.\n"
        );
    }
}

/// Regression: a `binds.cfg` that exists but cannot be read (here: a
/// directory) silently dropped every user bind, and a failed import write
/// was discarded. Both are now warnings; the binds stay as before.
#[cfg(unix)]
#[test]
fn unreadable_binds_cfg_and_failed_import_are_warnings() {
    let dir = tempfile::tempdir().unwrap();
    let binds = dir.path().join("binds.cfg");
    std::fs::create_dir(&binds).unwrap();
    std::fs::write(
        dir.path().join("keybindings.json"),
        r#"{"app.tools.expand": "ctrl+e"}"#,
    )
    .unwrap();
    let kb = KeybindingsManager::create(dir.path());
    assert!(!kb.matches("ctrl+e", "app.tools.expand"));
    assert_eq!(
        kb.warnings(),
        [format!(
            "{} could not be read (Is a directory (os error 21)): no user key bind applies",
            binds.display()
        )]
    );

    // A dangling symlink: absent to the read, present to the import's
    // create-new write, which fails.
    let dir = tempfile::tempdir().unwrap();
    let binds = dir.path().join("binds.cfg");
    std::os::unix::fs::symlink(dir.path().join("gone"), &binds).unwrap();
    std::fs::write(
        dir.path().join("keybindings.json"),
        r#"{"app.tools.expand": "ctrl+e"}"#,
    )
    .unwrap();
    let kb = KeybindingsManager::create(dir.path());
    assert!(kb.matches("ctrl+e", "app.tools.expand"));
    assert_eq!(
        kb.warnings(),
        [format!(
            "the keybindings.json binds could not be written to {} (File exists (os error 17)): they apply to this run only",
            binds.display()
        )]
    );
}

/// `/reload` re-reads `binds.cfg`.
#[test]
fn reload_picks_up_binds_cfg_changes() {
    let (dir, mut kb) = with_binds_cfg("bind ctrl+e \"action app.tools.expand\"\n");
    assert!(kb.matches("ctrl+e", "app.tools.expand"));
    std::fs::write(
        dir.path().join("binds.cfg"),
        "bind ctrl+t \"action app.tools.expand\"\n",
    )
    .unwrap();
    kb.reload();
    assert!(kb.matches("ctrl+t", "app.tools.expand"));
    assert!(!kb.matches("ctrl+e", "app.tools.expand"));
}

/// The first bind of a key wins: a user bind shadows every default
/// action of its key, and the actions keep their other keys.
#[test]
fn first_user_bind_wins_over_defaults() {
    let (_dir, kb) = with_binds_cfg(
        "bind ctrl+o \"action app.model.select\"\n\
         bind ctrl+o \"action app.clear\"\n",
    );
    assert_eq!(kb.press("ctrl+o"), Ok(vec![action("app.model.select")]));
    assert!(!kb.matches("ctrl+o", "app.tools.expand"));
    assert!(!kb.matches("ctrl+o", "app.clear"));
    assert_eq!(
        kb.get_keys("app.model.select"),
        vec!["ctrl+l".to_string(), "ctrl+o".to_string()]
    );
    assert!(kb.get_keys("app.tools.expand").is_empty());
}

#[test]
fn empty_bind_disables_a_default() {
    let (_dir, kb) = with_binds_cfg("bind ctrl+o \"\"\n");
    assert_eq!(kb.press("ctrl+o"), Ok(Vec::new()));
    assert!(!kb.matches("ctrl+o", "app.tools.expand"));
    assert!(!kb.matches("ctrl+o", "app.agents.program"));
    assert_eq!(kb.key_text("app.tools.expand"), "");
}

/// A press runs its bind's commands in order, the aliases of `binds.cfg`
/// expanded: the cvar commands for the daemon and the action for the
/// client.
#[test]
fn press_runs_set_and_action() {
    let (_dir, kb) = with_binds_cfg(
        "alias quiet \"set compaction.enabled false\"\n\
         bind f5 \"quiet; toggle retry.enabled; action app.tools.expand\"\n",
    );
    assert_eq!(
        kb.press("f5"),
        Ok(vec![
            Command::Set {
                id: "compaction.enabled".to_string(),
                value: "false".to_string(),
            },
            Command::Toggle {
                id: "retry.enabled".to_string(),
            },
            action("app.tools.expand"),
        ])
    );
    assert!(kb.matches("f5", "app.tools.expand"));
}

/// The dictation actions have no default key; a `binds.cfg` bind gives
/// each its key, and the alias form binds the same way.
#[test]
fn dictation_actions_bind_only_through_binds_cfg() {
    let defaults = KeybindingsManager::new();
    let (_dir, kb) = with_binds_cfg(
        "alias talk \"action app.stt.pushToTalk\"\n\
         bind f8 \"action app.stt.toggle\"\n\
         bind ctrl+space talk\n",
    );
    assert_eq!(
        (
            defaults.get_keys("app.stt.pushToTalk"),
            defaults.get_keys("app.stt.toggle"),
            kb.get_keys("app.stt.pushToTalk"),
            kb.get_keys("app.stt.toggle"),
            kb.press("ctrl+space"),
            kb.matches("ctrl+space", "app.stt.pushToTalk"),
            kb.matches("f8", "app.stt.toggle"),
            kb.matches("f8", "app.stt.pushToTalk"),
        ),
        (
            Vec::<String>::new(),
            Vec::<String>::new(),
            vec!["ctrl+space".to_string()],
            vec!["f8".to_string()],
            Ok(vec![action("app.stt.pushToTalk")]),
            true,
            true,
            false,
        )
    );
}

/// An alias cycle or an unknown alias is reported by the press, and the
/// key runs nothing (not even the action before the bad run).
#[test]
fn press_reports_cycle_and_runs_nothing() {
    let (_dir, kb) = with_binds_cfg(
        "alias a \"action app.tools.expand; b\"\n\
         alias b \"a\"\n\
         bind f6 \"a\"\n\
         bind f7 \"action app.tools.expand; missing\"\n",
    );
    assert_eq!(
        kb.press("f6"),
        Err(ExpandError::Cycle {
            alias: "b".to_string()
        })
    );
    assert!(!kb.matches("f6", "app.tools.expand"));
    assert_eq!(
        kb.press("f7"),
        Err(ExpandError::Unknown {
            alias: "missing".to_string()
        })
    );
    assert!(!kb.matches("f7", "app.tools.expand"));
}

#[test]
fn effective_config_covers_every_definition() {
    let kb = KeybindingsManager::new();
    let effective = kb.get_effective_config();
    assert_eq!(
        effective.len(),
        TUI_KEYBINDINGS.len() + APP_KEYBINDINGS.len()
    );
    assert_eq!(
        effective.get("tui.editor.selectParagraphDown"),
        Some(&vec!["shift+ctrl+down".to_string()])
    );
}

#[test]
fn formats_key_text() {
    assert_eq!(format_key_text("ctrl+o"), "Ctrl+O");
    assert_eq!(format_key_text("shift+alt+up"), "Shift+Alt+up");
    assert_eq!(format_key_text("escape"), "Esc");
    assert_eq!(format_key_text("ctrl+o/alt+o"), "Ctrl+O/Alt+O");
}

#[test]
fn formats_alt_label_per_platform() {
    // TS formatKeyPart: darwin renders `alt` as `Option` (the macOS
    // keyboard row), every other platform keeps `Alt`.
    assert_eq!(
        format_key_text_on("alt+b", LabelPlatform::Macos),
        "Option+B"
    );
    assert_eq!(format_key_text_on("alt+b", LabelPlatform::Other), "Alt+B");
    assert_eq!(
        format_key_text_on("shift+alt+left", LabelPlatform::Macos),
        "Shift+Option+left"
    );
    // Multiple bindings split by `/` keep their platform label per part,
    // and control is never relabeled as Cmd.
    assert_eq!(
        format_key_text_on("alt+o/ctrl+o", LabelPlatform::Macos),
        "Option+O/Ctrl+O"
    );
}
