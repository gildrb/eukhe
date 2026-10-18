//! Headless e2e for the tray model label's effort suffix (TS
//! `getModelContextLabel`'s `model:effort` arm): a mock supervisor serves
//! one attached session whose state reports the model's reasoning and the
//! live thinking level, and the plan drives `/effort` through the same
//! editor submit path a user's keystrokes take.
//!
//! Verifies the parity contract: the tray under the prompt bar renders
//! `model:effort` while the session's model supports reasoning, keeps the
//! bare model id when it does not, and the label follows a `/effort`
//! switch live.
//!
//! Also verifies the thinking-level cycle keys (`app.thinking.cycleForward`
//! on shift+tab, `app.thinking.cycleBackward` on shift+alt+tab): the mock
//! answers `cycle_thinking_level` as the daemon does (the next or previous
//! level of the offered ladder, with wrap; `null` for fewer than two
//! levels), and the settings menu keeps shift+tab for its tab switch.
// Pedantic-gate exceptions (every other pedantic warning in this crate is
// fixed in place; each exception carries its one-line justification):
// - the casts: terminal-layout arithmetic narrows structurally bounded
//   values (screen coordinates, byte counts, timestamps); guarded
//   conversions would add panic paths the bounds guarantee away.
#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::cast_precision_loss
)]
// - the render routes are flat tables (one arm per route); splitting them
//   would add indirection without changing the flow.
#![allow(clippy::too_many_lines)]
// - widget state structs carry independent flag bits; a nested struct
//   would add indirection without changing the shape.
#![allow(clippy::struct_excessive_bools, clippy::fn_params_excessive_bools)]
// - the futures are bounded by the surface's lifetime; boxing them would
//   add an allocation to the steady-state loop.
#![allow(clippy::large_futures)]
// - the wrappers preserve a uniform Result-returning API surface; unwrap
//   removals would ripple through the callers without changing behavior.
#![allow(clippy::unnecessary_wraps)]

use crossterm::event::{KeyCode, KeyEvent, KeyModifiers};
use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::PathBuf;

use eukhe_tui::interactive::{
    run_interactive, HeadlessPlan, HeadlessStep, InteractiveOptions, ModelSelection,
    SessionSelection, UiMode,
};
use serde_json::{json, Value};

/// The session the mock serves: the `model` state block (with its
/// `reasoning` flag), the available thinking levels, and the live level
/// (the value `set_thinking_level` moves). `fail_state_after_switch`
/// makes every state read AFTER a thinking switch fail, pinning the
/// client's failed-read fallback (no stale suffix survives a switch).
struct MockSession {
    model: Value,
    levels: Vec<String>,
    level: String,
    fail_state_after_switch: bool,
}

/// A reasoning model at the default level (the engine's `medium`, TS
/// `DEFAULT_THINKING_LEVEL`).
fn reasoning_session() -> MockSession {
    MockSession {
        model: json!({ "id": "glm-5.3", "name": "GLM 5.3", "provider": "zai", "reasoning": true }),
        levels: vec![
            "off".to_string(),
            "minimal".to_string(),
            "low".to_string(),
            "medium".to_string(),
            "high".to_string(),
        ],
        level: "medium".to_string(),
        fail_state_after_switch: false,
    }
}

/// A model without reasoning: the daemon clamps its level to "off".
fn plain_session() -> MockSession {
    MockSession {
        model: json!({
            "id": "gpt-4o-mini",
            "name": "GPT 4o mini",
            "provider": "openai",
            "reasoning": false
        }),
        levels: vec!["off".to_string()],
        level: "off".to_string(),
        fail_state_after_switch: false,
    }
}

/// The Elpis `qwen3.8` model: its thinking level map offers the ladder
/// off, low, medium, xhigh. The session starts at `low`.
fn elpis_session() -> MockSession {
    MockSession {
        model: json!({ "id": "qwen3.8", "name": "Qwen 3.8", "provider": "elpis", "reasoning": true }),
        levels: vec![
            "off".to_string(),
            "low".to_string(),
            "medium".to_string(),
            "xhigh".to_string(),
        ],
        level: "low".to_string(),
        fail_state_after_switch: false,
    }
}

impl MockSession {
    fn bind(self, socket: &std::path::Path) -> MockSupervisor {
        MockSupervisor {
            listener: UnixListener::bind(socket).expect("bind mock socket"),
            session: self,
        }
    }
}

/// One mock supervisor serving a single attached session: the state
/// blocks report the session's model and live level, and
/// `set_thinking_level` and `cycle_thinking_level` move that level so the
/// client's state re-reads observe the switch.
struct MockSupervisor {
    listener: UnixListener,
    session: MockSession,
}

impl MockSupervisor {
    /// Serve one connection: attach an empty session, then answer the
    /// state reads and the thinking switches off the live level. Returns
    /// the `direction` field of each `cycle_thinking_level` command, in
    /// arrival order (`null` when the command has no direction).
    fn serve(mut self) -> Vec<Value> {
        let mut cycles = Vec::new();
        // Armed by `set_thinking_level` when the session pins the
        // failed-read fallback: every later state read refuses.
        let mut state_reads_fail = false;
        let (stream, _) = self.listener.accept().expect("accept");
        let write_stream = stream.try_clone().expect("clone mock socket");
        let mut writer = write_stream;
        let mut reader = BufReader::new(stream);

        let hello = json!({
            "type": "daemon_hello",
            "protocol": { "name": "eukhe.daemon", "version": 7 },
            "serverCapabilities": [],
            "clientId": "mock",
        });
        write_json(&mut writer, &hello);

        let mut line = String::new();
        loop {
            line.clear();
            match reader.read_line(&mut line) {
                Ok(0) | Err(_) => break,
                Ok(_) => {}
            }
            let Ok(envelope) = serde_json::from_str::<Value>(line.trim()) else {
                continue;
            };
            let id = envelope.get("id").and_then(Value::as_str).unwrap_or("");
            let command = envelope.get("command").cloned().unwrap_or(Value::Null);
            let command_type = command
                .get("type")
                .and_then(Value::as_str)
                .unwrap_or_default()
                .to_string();
            match command_type.as_str() {
                "create" => {
                    write_json(
                        &mut writer,
                        &json!({
                            "type": "response",
                            "id": id,
                            "command": "create",
                            "success": true,
                            "data": {
                                "activeSessionId": "s1",
                                "id": "s1",
                                "sessionId": "sess-1",
                                "sessionFile": "/tmp/sess-1.jsonl",
                            },
                        }),
                    );
                }
                "attach" => {
                    write_json(&mut writer, &self.attach_data(id));
                }
                "get_state" | "get_connection_state" => {
                    if state_reads_fail {
                        write_json(
                            &mut writer,
                            &json!({
                                "type": "response",
                                "id": id,
                                "command": command_type,
                                "success": false,
                                "error": "the state read failed",
                            }),
                        );
                    } else {
                        write_json(&mut writer, &self.state_data(id, &command_type));
                    }
                }
                "set_thinking_level" => {
                    if let Some(level) = command.get("level").and_then(Value::as_str) {
                        self.session.level = level.to_string();
                    }
                    state_reads_fail = self.session.fail_state_after_switch;
                    write_json(
                        &mut writer,
                        &json!({
                            "type": "response",
                            "id": id,
                            "command": "set_thinking_level",
                            "success": true,
                            "data": null,
                        }),
                    );
                }
                // The daemon's answer: `null` when the model offers fewer
                // than two levels (nothing changes), else the next (or, for
                // `backward`, the previous) level of the ladder, with wrap.
                // The live level moves to it.
                "cycle_thinking_level" => {
                    let direction = command.get("direction").cloned().unwrap_or(Value::Null);
                    let levels = &self.session.levels;
                    let data = if levels.len() < 2 {
                        Value::Null
                    } else {
                        let count = levels.len();
                        let at = levels
                            .iter()
                            .position(|level| *level == self.session.level)
                            .expect("the live level is on the ladder");
                        let next = if direction.as_str() == Some("backward") {
                            (at + count - 1) % count
                        } else {
                            (at + 1) % count
                        };
                        self.session.level = levels[next].clone();
                        json!({ "level": self.session.level })
                    };
                    cycles.push(direction);
                    write_json(
                        &mut writer,
                        &json!({
                            "type": "response",
                            "id": id,
                            "command": "cycle_thinking_level",
                            "success": true,
                            "data": data,
                        }),
                    );
                }
                "detach" => {
                    write_json(
                        &mut writer,
                        &json!({
                            "type": "response",
                            "id": id,
                            "command": "detach",
                            "success": true,
                        }),
                    );
                }
                _ => {
                    write_json(
                        &mut writer,
                        &json!({
                            "type": "response",
                            "id": id,
                            "command": command_type,
                            "success": true,
                            "data": {},
                        }),
                    );
                }
            }
        }
        cycles
    }

    /// The slim attach result: one empty session whose state reports the
    /// model and its thinking level (the tray label's inputs).
    fn attach_data(&self, id: &str) -> Value {
        json!({
            "type": "response",
            "id": id,
            "command": "attach",
            "success": true,
            "data": {
                "protocol": { "name": "eukhe.daemon", "version": 7 },
                "activeSessionId": "s1",
                "snapshot": {
                    "activeSessionId": "s1",
                    "summary": { "id": "s1", "cwd": "/tmp" },
                    "state": {
                        "activeSessionId": "s1",
                        "cwd": "/tmp",
                        "sessionId": "sess-1",
                        "sessionName": "effort session",
                        "model": self.session.model,
                        "thinkingLevel": self.session.level,
                        "availableThinkingLevels": self.session.levels,
                        "serviceTier": "auto",
                        "isStreaming": false,
                        "isCompacting": false,
                        "sessionActions": { "queuedCount": 0, "steering": [], "followUps": [] },
                    },
                    "messages": [],
                    "lastEventSequence": 0,
                    "lastEventCursor": null,
                },
                "client": { "id": "mock", "capabilities": [] },
                "lastEventSequence": 0,
                "lastEventCursor": null,
            },
        })
    }

    /// The live session state (the `get_state`/`get_connection_state`
    /// data block): the model with its reasoning flag and the level
    /// `/effort` writes.
    fn state_data(&self, id: &str, command: &str) -> Value {
        json!({
            "type": "response",
            "id": id,
            "command": command,
            "success": true,
            "data": {
                "model": self.session.model,
                "thinkingLevel": self.session.level,
                "availableThinkingLevels": self.session.levels,
                "isStreaming": false,
                "isCompacting": false,
                "sessionActions": { "queuedCount": 0, "steering": [], "followUps": [] },
            },
        })
    }
}

fn write_json(writer: &mut UnixStream, value: &Value) {
    let mut line = serde_json::to_string(value).expect("serialize mock frame");
    line.push('\n');
    writer.write_all(line.as_bytes()).expect("write mock frame");
    writer.flush().expect("flush mock frame");
}

fn options(socket: PathBuf) -> InteractiveOptions {
    InteractiveOptions {
        models: None,
        socket_path: socket,
        cwd: PathBuf::from("/tmp"),
        session_dir: None,
        script_path: None,
        model_selection: ModelSelection::default(),
        model_catalog: Vec::new(),
        model_configured_providers: std::collections::HashSet::default(),
        model_recent_models: Vec::new(),
        default_thinking_level: None,
        no_session: false,
        session: SessionSelection::New,
        initial_message: None,
        show_images: true,
        screen_mode: eukhe_tui::screen_mode::ScreenMode::Inline,
        theme: "eukhe".to_string(),
        code_block_indent: "  ".to_string(),
        tree_filter_mode: String::new(),
        branch_summary_skip_prompt: false,
        version: "0.0.0".to_string(),
        onboarding: None,
        client_auth: None,
        provider_auth: None,
        keybindings: eukhe_tui::keybindings::KeybindingsManager::new(),
        session_rlm_depth: None,
        prompt_stash: std::sync::Arc::default(),
        session_has_children: false,
        restore_dock_focus: false,
        client_settings: None,
        dictation: None,
    }
}

/// Run the headless plan against a fresh mock supervisor and return the
/// captured frames and the directions of the cycle requests that the
/// mock received.
fn run_plan(session: MockSession, steps: Vec<HeadlessStep>) -> (Vec<String>, Vec<Value>) {
    std::env::remove_var("TMUX");
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("tui.sock");
    let supervisor = session.bind(&socket);
    let handle = std::thread::spawn(move || supervisor.serve());

    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .expect("tokio runtime");
    let plan = HeadlessPlan {
        steps,
        width: 100,
        height: 30,
    };
    let outcome = runtime
        .block_on(run_interactive(options(socket), UiMode::Headless(plan)))
        .expect("interactive run");
    let cycles = handle.join().expect("mock supervisor finished");
    (outcome.frames, cycles)
}

/// `/effort` moves the status line's thinking label live: the attach
/// state seeds `[med]`, the switch's level lands as `[high]`, and the
/// frame that reports the switch carries the new label only.
#[test]
fn effort_command_moves_the_tray_model_label() {
    let steps = vec![
        HeadlessStep::Submit("/effort high".to_string()),
        HeadlessStep::WaitRender {
            needle: HIGH.to_string(),
            timeout_ms: 10_000,
        },
        HeadlessStep::WaitMs(200),
    ];
    let (frames, _) = run_plan(reasoning_session(), steps);
    assert!(
        frames.iter().any(|frame| frame.contains(MEDIUM)),
        "the attach state seeds the level suffix:\n{}",
        frames.join("\n---\n")
    );
    let switched = frames
        .iter()
        .rev()
        .find(|frame| frame.contains("Thinking level: high"))
        .expect("the switch's status note rendered");
    assert!(
        switched.contains(HIGH),
        "the tray label follows the switch:\n{switched}"
    );
    assert!(
        !switched.contains(MEDIUM),
        "the pre-switch label is gone:\n{switched}"
    );
}

/// A successful `/effort` switch whose state re-read fails still moves the
/// label: the requested level renders (TS `applyThinkingLevel` patches the
/// connection state with the requested level), never the previous model's
/// stale suffix.
#[test]
fn effort_switch_with_failed_state_read_never_keeps_the_stale_suffix() {
    let mut session = reasoning_session();
    session.fail_state_after_switch = true;
    let steps = vec![
        HeadlessStep::Submit("/effort high".to_string()),
        HeadlessStep::WaitRender {
            needle: "Thinking level: high".to_string(),
            timeout_ms: 10_000,
        },
        HeadlessStep::WaitMs(200),
    ];
    let (frames, _) = run_plan(session, steps);
    let switched = frames
        .iter()
        .rev()
        .find(|frame| frame.contains("Thinking level: high"))
        .expect("the switch's status note rendered");
    assert!(
        switched.contains(HIGH),
        "the failed read falls back to the requested level:\n{switched}"
    );
    assert!(
        !switched.contains(MEDIUM),
        "the pre-switch suffix never survives a switch:\n{switched}"
    );
}

/// A model without reasoning renders the bare id: the state's level is
/// "off" but the status line never carries a thinking label.
#[test]
fn tray_label_stays_bare_without_reasoning() {
    let steps = vec![HeadlessStep::WaitRender {
        needle: "[M] gpt-4o-mini".to_string(),
        timeout_ms: 10_000,
    }];
    let (frames, _) = run_plan(plain_session(), steps);
    let all = frames.join("\n---\n");
    assert!(
        frames.iter().any(|frame| frame.contains("[M] gpt-4o-mini")),
        "the bare model id renders on the status line:\n{all}"
    );
    assert!(
        !all.contains("[M] gpt-4o-mini - ["),
        "a model without reasoning never carries a thinking label:\n{all}"
    );
}

/// The status line's model segment at each thinking level (the session
/// reports the `auto` service tier, the badge after the model).
const MEDIUM: &str = "[M] glm-5.3 auto - [med]";
const HIGH: &str = "[M] glm-5.3 auto - [high]";

/// The status line's model segment of the Elpis session at each level.
const ELPIS_OFF: &str = "[M] qwen3.8 auto - [ ] off";
const ELPIS_LOW: &str = "[M] qwen3.8 auto - [low]";
const ELPIS_MEDIUM: &str = "[M] qwen3.8 auto - [med]";
const ELPIS_XHIGH: &str = "[M] qwen3.8 auto - [xhi]";

/// Shift+Tab as the input reader decodes `\x1b[Z`.
fn shift_tab() -> HeadlessStep {
    HeadlessStep::Key(KeyEvent::new(KeyCode::BackTab, KeyModifiers::SHIFT))
}

/// Shift+Alt+Tab (the meta-wrapped `ESC ESC [ Z`).
fn shift_alt_tab() -> HeadlessStep {
    HeadlessStep::Key(KeyEvent::new(
        KeyCode::BackTab,
        KeyModifiers::SHIFT | KeyModifiers::ALT,
    ))
}

fn wait_render(needle: &str) -> HeadlessStep {
    HeadlessStep::WaitRender {
        needle: needle.to_string(),
        timeout_ms: 10_000,
    }
}

/// The Elpis tray labels in the order the frames show them (one entry per
/// change of the label).
fn elpis_label_sequence(frames: &[String]) -> Vec<&'static str> {
    let mut sequence: Vec<&'static str> = Vec::new();
    for frame in frames {
        let label = [ELPIS_OFF, ELPIS_LOW, ELPIS_MEDIUM, ELPIS_XHIGH]
            .into_iter()
            .find(|label| frame.contains(label));
        if let Some(label) = label {
            if sequence.last() != Some(&label) {
                sequence.push(label);
            }
        }
    }
    sequence
}

/// The first frame that shows `note` also shows `label`: the tray follows
/// the level in the same paint as the status note.
fn assert_note_with_label(frames: &[String], note: &str, label: &str) {
    let frame = frames
        .iter()
        .find(|frame| frame.contains(note))
        .unwrap_or_else(|| panic!("no frame shows {note:?}:\n{}", frames.join("\n---\n")));
    assert!(
        frame.contains(label),
        "{note:?} without {label:?}:\n{frame}"
    );
}

/// Shift+Tab steps the Elpis ladder forward with wrap: low, medium,
/// xhigh, off, low. Each press sends one forward cycle, and the tray
/// label follows each applied level.
#[test]
fn shift_tab_cycles_the_offered_ladder_forward() {
    let steps = vec![
        wait_render(ELPIS_LOW),
        shift_tab(),
        wait_render(ELPIS_MEDIUM),
        shift_tab(),
        wait_render(ELPIS_XHIGH),
        shift_tab(),
        wait_render(ELPIS_OFF),
        shift_tab(),
        wait_render(ELPIS_LOW),
        HeadlessStep::WaitMs(200),
    ];
    let (frames, cycles) = run_plan(elpis_session(), steps);
    assert_eq!(cycles, vec![json!("forward"); 4]);
    assert_eq!(
        elpis_label_sequence(&frames),
        vec![ELPIS_LOW, ELPIS_MEDIUM, ELPIS_XHIGH, ELPIS_OFF, ELPIS_LOW]
    );
    assert_note_with_label(&frames, "Thinking level: medium", ELPIS_MEDIUM);
    assert_note_with_label(&frames, "Thinking level: xhigh", ELPIS_XHIGH);
    assert_note_with_label(&frames, "Thinking level: off", ELPIS_OFF);
    assert_note_with_label(&frames, "Thinking level: low", ELPIS_LOW);
}

/// Shift+Alt+Tab steps the ladder backward with wrap: low, off, xhigh.
#[test]
fn shift_alt_tab_cycles_the_offered_ladder_backward() {
    let steps = vec![
        wait_render(ELPIS_LOW),
        shift_alt_tab(),
        wait_render(ELPIS_OFF),
        shift_alt_tab(),
        wait_render(ELPIS_XHIGH),
        HeadlessStep::WaitMs(200),
    ];
    let (frames, cycles) = run_plan(elpis_session(), steps);
    assert_eq!(cycles, vec![json!("backward"); 2]);
    assert_eq!(
        elpis_label_sequence(&frames),
        vec![ELPIS_LOW, ELPIS_OFF, ELPIS_XHIGH]
    );
    assert_note_with_label(&frames, "Thinking level: off", ELPIS_OFF);
    assert_note_with_label(&frames, "Thinking level: xhigh", ELPIS_XHIGH);
}

/// `/effort` lists exactly the offered levels, in ladder order, and marks
/// the effective level only.
#[test]
fn effort_picker_lists_the_offered_levels_with_the_effective_one_marked() {
    let steps = vec![
        wait_render(ELPIS_LOW),
        HeadlessStep::Submit("/effort".to_string()),
        wait_render("Thinking Level"),
        HeadlessStep::WaitMs(100),
    ];
    let (frames, cycles) = run_plan(elpis_session(), steps);
    assert_eq!(cycles, Vec::<Value>::new());
    let picker = frames
        .iter()
        .rev()
        .find(|frame| frame.contains("Thinking Level"))
        .expect("the picker rendered");
    // Each level row reads `[x] <level>` or `[ ] <level>` (the status
    // line at `low` carries no checkbox).
    let rows: Vec<(bool, String)> = picker
        .lines()
        .filter_map(|row| {
            let (checked, at) = match (row.find("[x] "), row.find("[ ] ")) {
                (Some(at), _) => (true, at),
                (None, Some(at)) => (false, at),
                (None, None) => return None,
            };
            let level = row[at + 4..].split_whitespace().next()?;
            Some((checked, level.to_string()))
        })
        .collect();
    assert_eq!(
        rows,
        vec![
            (false, "off".to_string()),
            (true, "low".to_string()),
            (false, "medium".to_string()),
            (false, "xhigh".to_string()),
        ],
        "{picker}"
    );
}

/// An `off`-only ladder: Shift+Tab asks the daemon once, the `null`
/// answer changes nothing, and a short note says so.
#[test]
fn shift_tab_on_an_off_only_ladder_changes_nothing() {
    let steps = vec![
        wait_render("[M] gpt-4o-mini"),
        shift_tab(),
        wait_render("Current model offers no other thinking level"),
        HeadlessStep::WaitMs(200),
    ];
    let (frames, cycles) = run_plan(plain_session(), steps);
    assert_eq!(cycles, vec![json!("forward")]);
    let all = frames.join("\n---\n");
    assert!(!all.contains("Thinking level:"), "{all}");
    let noted = frames
        .iter()
        .find(|frame| frame.contains("Current model offers no other thinking level"))
        .expect("the note rendered");
    // The path segment follows the tier directly: no thinking label.
    assert!(noted.contains("[M] gpt-4o-mini auto - [T] /tmp"), "{noted}");
}

/// An unset session level (the state reports `default` before the
/// session has an explicit level) never shows as `off`: the tray keeps
/// the bare model id, and `/effort` marks no row as current.
#[test]
fn an_unset_level_never_shows_as_off() {
    let mut session = elpis_session();
    session.level = "default".to_string();
    let steps = vec![
        wait_render("[M] qwen3.8 auto - [T] /tmp"),
        HeadlessStep::Submit("/effort".to_string()),
        wait_render("Thinking Level"),
        HeadlessStep::WaitMs(100),
    ];
    let (frames, cycles) = run_plan(session, steps);
    assert_eq!(cycles, Vec::<Value>::new());
    let all = frames.join("\n---\n");
    assert!(!all.contains(ELPIS_OFF), "{all}");
    let picker = frames
        .iter()
        .rev()
        .find(|frame| frame.contains("Thinking Level"))
        .expect("the picker rendered");
    assert!(!picker.contains("[x] "), "{picker}");
    for level in ["off", "low", "medium", "xhigh"] {
        assert!(picker.contains(&format!("[ ] {level}")), "{picker}");
    }
}

/// The open settings menu takes Shift+Tab first: it switches the tab
/// back (Models to General), and no cycle request reaches the daemon.
#[test]
fn settings_menu_keeps_shift_tab_for_its_tabs() {
    let steps = vec![
        wait_render(ELPIS_LOW),
        HeadlessStep::Submit("/settings".to_string()),
        wait_render("General"),
        HeadlessStep::Key(KeyEvent::new(KeyCode::Tab, KeyModifiers::NONE)),
        wait_render("Transport"),
        shift_tab(),
        wait_render("Auto-compact"),
        HeadlessStep::WaitMs(200),
    ];
    let (frames, cycles) = run_plan(elpis_session(), steps);
    assert_eq!(cycles, Vec::<Value>::new());
    let last = frames.last().expect("the run captured frames");
    assert!(last.contains("Auto-compact"), "{last}");
    assert!(!last.contains("Transport"), "{last}");
    assert!(!frames.join("\n").contains("Thinking level:"));
}
