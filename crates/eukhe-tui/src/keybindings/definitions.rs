use super::KeybindingDefinition;
/// TUI-level bindings (`TUI_KEYBINDINGS`).
pub const TUI_KEYBINDINGS: &[(&str, KeybindingDefinition)] = &[
    ("tui.editor.cursorUp", def!(&["up"], scope "editor")),
    ("tui.editor.cursorDown", def!(&["down"], scope "editor")),
    (
        "tui.editor.cursorLeft",
        def!(&["left", "ctrl+b"], scope "editor"),
    ),
    (
        "tui.editor.cursorRight",
        def!(&["right", "ctrl+f"], scope "editor"),
    ),
    (
        "tui.editor.cursorWordLeft",
        def!(&["alt+left", "ctrl+left", "alt+b"], scope "editor"),
    ),
    (
        "tui.editor.cursorWordRight",
        def!(&["alt+right", "ctrl+right", "alt+f"], scope "editor"),
    ),
    (
        "tui.editor.cursorLineStart",
        // "super+left" is the macOS Cmd+Left line-start key (a prompt-
        // editor-keybinds addition; see the divergence note above).
        def!(
            &["home", "ctrl+a", "super+left"],
            scope "editor"
        ),
    ),
    (
        "tui.editor.cursorLineEnd",
        def!(
            &["end", "ctrl+e", "super+right"],
            scope "editor"
        ),
    ),
    ("tui.editor.jumpForward", def!(&["ctrl+]"], scope "editor")),
    (
        "tui.editor.jumpBackward",
        def!(&["ctrl+alt+]"], scope "editor"),
    ),
    ("tui.editor.pageUp", def!(&["pageUp"], scope "editor")),
    ("tui.editor.pageDown", def!(&["pageDown"], scope "editor")),
    (
        "tui.editor.deleteCharBackward",
        def!(&["backspace"], scope "editor"),
    ),
    (
        "tui.editor.deleteCharForward",
        def!(&["delete", "ctrl+d"], scope "editor"),
    ),
    (
        "tui.editor.deleteWordBackward",
        def!(&["ctrl+w", "alt+backspace"], scope "editor"),
    ),
    (
        "tui.editor.deleteWordForward",
        def!(&["alt+d", "alt+delete"], scope "editor"),
    ),
    (
        "tui.editor.deleteToLineStart",
        def!(&["ctrl+u"], scope "editor"),
    ),
    (
        "tui.editor.deleteToLineEnd",
        def!(&["ctrl+k"], scope "editor"),
    ),
    ("tui.editor.yank", def!(&["ctrl+y"], scope "editor")),
    ("tui.editor.yankPop", def!(&["alt+y"], scope "editor")),
    (
        "tui.editor.undo",
        def!(&["ctrl+-", "super+z"], scope "editor"),
    ),
    // SANCTIONED DIVERGENCE from TS (operator ask 2026-09-24, documented
    // per the #289 precedent): the ids below have no TS counterpart -- the
    // TS editor's key set stops at the bindings above. The prompt bar
    // carries the full standard text-editing set instead: redo, selection
    // (shift+arrow families, select-all), document/paragraph jumps, word
    // selection, cut/copy of the selection, and character transposition.
    // The `super+` defaults are the macOS Cmd keys (the kitty protocol
    // delivers them as the SUPER modifier); every binding stays
    // user-configurable through binds.cfg exactly like the rest.
    (
        "tui.editor.redo",
        def!(
            &["ctrl+shift+z", "super+shift+z"],
            scope "editor"
        ),
    ),
    (
        "tui.editor.cursorDocStart",
        def!(
            &["ctrl+home", "super+home", "super+up"],
            scope "editor"
        ),
    ),
    (
        "tui.editor.cursorDocEnd",
        def!(
            &["ctrl+end", "super+end", "super+down"],
            scope "editor"
        ),
    ),
    (
        "tui.editor.cursorParagraphUp",
        def!(&["ctrl+up"], scope "editor"),
    ),
    (
        "tui.editor.cursorParagraphDown",
        def!(&["ctrl+down"], scope "editor"),
    ),
    (
        "tui.editor.selectAll",
        def!(&["super+a", "ctrl+shift+a"], scope "editor"),
    ),
    (
        "tui.editor.selectLeft",
        def!(&["shift+left"], scope "editor"),
    ),
    (
        "tui.editor.selectRight",
        def!(&["shift+right"], scope "editor"),
    ),
    ("tui.editor.selectUp", def!(&["shift+up"], scope "editor")),
    (
        "tui.editor.selectDown",
        def!(&["shift+down"], scope "editor"),
    ),
    (
        "tui.editor.selectWordLeft",
        def!(
            &["shift+alt+left", "shift+ctrl+left"],
            scope "editor"
        ),
    ),
    (
        "tui.editor.selectWordRight",
        def!(
            &["shift+alt+right", "shift+ctrl+right"],
            scope "editor"
        ),
    ),
    (
        "tui.editor.selectLineStart",
        def!(&["shift+home"], scope "editor"),
    ),
    (
        "tui.editor.selectLineEnd",
        def!(&["shift+end"], scope "editor"),
    ),
    (
        "tui.editor.selectParagraphUp",
        def!(&["shift+ctrl+up"], scope "editor"),
    ),
    (
        "tui.editor.selectParagraphDown",
        def!(&["shift+ctrl+down"], scope "editor"),
    ),
    (
        "tui.editor.selectDocStart",
        def!(
            &["shift+ctrl+home", "super+shift+up"],
            scope "editor"
        ),
    ),
    (
        "tui.editor.selectDocEnd",
        def!(
            &["shift+ctrl+end", "super+shift+down"],
            scope "editor"
        ),
    ),
    (
        "tui.editor.transposeChars",
        def!(&["ctrl+t"], scope "editor"),
    ),
    (
        "tui.editor.cutSelection",
        def!(
            &["ctrl+x", "super+x"],
            scope "editor"
        ),
    ),
    (
        "tui.editor.copySelection",
        def!(
            &["ctrl+shift+c", "super+c"],
            scope "editor"
        ),
    ),
    ("tui.input.newLine", def!(&["shift+enter"], scope "editor")),
    ("tui.input.submit", def!(&["enter"], scope "editor")),
    ("tui.input.tab", def!(&["tab"], scope "editor")),
    ("tui.input.copy", def!(&["ctrl+c"], scope "editor")),
    // The fullscreen transcript window (`terminal.fullscreen`); inline
    // mode leaves these keys to the editor.
    ("tui.viewport.pageUp", def!(&["pageUp"])),
    ("tui.viewport.pageDown", def!(&["pageDown"])),
    ("tui.viewport.top", def!(&["ctrl+home"])),
    ("tui.viewport.bottom", def!(&["ctrl+end"])),
    ("tui.select.up", def!(&["up"])),
    ("tui.select.down", def!(&["down"])),
    ("tui.select.pageUp", def!(&["pageUp"])),
    ("tui.select.pageDown", def!(&["pageDown"])),
    (
        "tui.select.top",
        def!(&["home", "ctrl+home", "super+home", "super+up"]),
    ),
    (
        "tui.select.bottom",
        def!(&["end", "ctrl+end", "super+end", "super+down"]),
    ),
    ("tui.select.confirm", def!(&["enter"])),
    ("tui.select.cancel", def!(&["escape", "ctrl+c"])),
];

/// App-level bindings (`KEYBINDINGS` additions in coding-agent).
pub const APP_KEYBINDINGS: &[(&str, KeybindingDefinition)] = &[
    ("app.interrupt", def!(&[])),
    ("app.clear", def!(&["ctrl+c"])),
    ("app.input.clear", def!(&["escape"])),
    ("app.exit", def!(&["ctrl+d"])),
    ("app.suspend", def!(&["ctrl+z"])),
    ("app.model.select", def!(&["ctrl+l"])),
    ("app.model.toggleScope", def!(&["alt+s"])),
    ("app.model.cycleForward", def!(&["alt+m"])),
    ("app.model.cycleBackward", def!(&["shift+alt+m"])),
    (
        "app.thinking.cycleForward",
        def!(&["shift+tab"], scope "editor"),
    ),
    (
        "app.thinking.cycleBackward",
        def!(&["shift+alt+tab"], scope "editor"),
    ),
    ("app.tools.expand", def!(&["ctrl+o"], scope "editor")),
    ("app.subagents.focus", def!(&["alt+a"])),
    // The focused dock's expand key: the pinned agents block opens in full
    // or folds to its first rows.
    ("app.subagents.pinned", def!(&["space"])),
    // The worker pane (`crate::worker_pane`): show or hide it, and its
    // full view (Esc returns from the full view).
    ("app.worker.toggle", def!(&["alt+w"])),
    ("app.worker.full", def!(&["shift+alt+w"])),
    ("app.heartbeats.openSelected", def!(&["right"])),
    ("app.memory.expand", def!(&["right"])),
    ("app.editor.external", def!(&["ctrl+g"])),
    ("app.prompt.stash", def!(&["ctrl+s"])),
    ("app.message.followUp", def!(&["alt+enter"])),
    ("app.message.navigateOlder", def!(&["alt+up"])),
    ("app.message.navigateNewer", def!(&["alt+down"])),
    ("app.message.moveEarlier", def!(&["ctrl+alt+up"])),
    ("app.message.moveLater", def!(&["ctrl+alt+down"])),
    ("app.clipboard.pasteImage", def!(&["ctrl+v"])),
    ("app.clipboard.copyLoginUrl", def!(&["c", "alt+c"])),
    ("app.session.new", def!(&[])),
    ("app.session.tree", def!(&[])),
    ("app.session.fork", def!(&[])),
    ("app.session.resume", def!(&[])),
    // Dictation (S9): no default key; `binds.cfg` binds them.
    ("app.stt.pushToTalk", def!(&[])),
    ("app.stt.toggle", def!(&[])),
    ("app.agents.back", def!(&["left"])),
    ("app.agents.open", def!(&["right"])),
    ("app.modal.back", def!(&["left"])),
    ("app.agents.reply", def!(&["space"])),
    ("app.agents.new", def!(&["ctrl+n"])),
    ("app.agents.delete", def!(&["ctrl+x"])),
    ("app.agents.program", def!(&["ctrl+o"])),
    ("app.agents.rename", def!(&["ctrl+r"])),
    ("app.agents.expand", def!(&["alt+right"])),
    ("app.tree.foldOrUp", def!(&["ctrl+left", "alt+left"])),
    ("app.tree.unfoldOrDown", def!(&["ctrl+right", "alt+right"])),
    ("app.tree.editLabel", def!(&["shift+l"])),
    ("app.tree.toggleLabelTimestamp", def!(&["shift+t"])),
    ("app.tree.filter.default", def!(&["ctrl+d"])),
    ("app.tree.filter.noTools", def!(&["ctrl+t"])),
    ("app.tree.filter.userOnly", def!(&["ctrl+u"])),
    ("app.tree.filter.labeledOnly", def!(&["ctrl+l"])),
    ("app.tree.filter.all", def!(&["ctrl+a"])),
    ("app.tree.filter.cycleForward", def!(&["ctrl+o"])),
    ("app.tree.filter.cycleBackward", def!(&["shift+ctrl+o"])),
];
