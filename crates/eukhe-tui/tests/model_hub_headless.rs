//! Headless e2e for the `/model` hub: the roles list with each role's
//! value and source, a memory pick that saves `memory` through the
//! settings seam (never the session), a chat pick that switches the live
//! session through `set_model`, a cleared role that falls back, and the
//! all-roles model: `/model --all` switches with `allRoles`, every LLM
//! role runs on it, and the note names what a project still sets.
// - the futures are bounded by the surface's lifetime; boxing them would
//   add an allocation to the steady-state loop.
#![allow(clippy::large_futures)]
// - the mock daemon and the plan are flat tables (one arm per command,
//   one step per key); splitting them would add indirection.
#![allow(clippy::too_many_lines)]

use std::collections::HashMap;
use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use anyhow::Result;
use crossterm::event::{KeyCode, KeyEvent, KeyModifiers};
use eukhe_tui::client_settings::{AllRolesOverride, ModelRoleSource, ModelRoleValue};
use eukhe_tui::interactive::{
    run_interactive, HeadlessPlan, HeadlessStep, InteractiveOptions, ModelSelection,
    SessionSelection, UiMode,
};
use eukhe_types::model_roles::ModelRole;
use serde_json::{json, Value};

fn catalog_entry(provider: &str, id: &str) -> Value {
    json!({
        "id": id,
        "name": id,
        "api": "openai-completions",
        "provider": provider,
        "baseUrl": "https://example.invalid/v1",
        "reasoning": false,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 128_000,
        "maxTokens": 4096,
        "thinkingLevels": ["off"],
        "serviceTiers": ["default"],
    })
}

fn catalog() -> Vec<Value> {
    vec![
        catalog_entry("prov", "alpha"),
        catalog_entry("prov", "beta"),
    ]
}

fn write_json(writer: &mut UnixStream, value: &Value) {
    let mut line = serde_json::to_string(value).expect("serialize mock frame");
    line.push('\n');
    writer.write_all(line.as_bytes()).expect("write mock frame");
    writer.flush().expect("flush mock frame");
}

fn respond(writer: &mut UnixStream, id: &str, command: &str, data: &Value) {
    write_json(
        writer,
        &json!({ "type": "response", "id": id, "command": command, "success": true, "data": data }),
    );
}

/// The mock daemon: one empty session; every command it gets is recorded.
/// A `set_model` with `allRoles` saves the all-roles model and clears each
/// LLM role's own global setting like the daemon (in the settings seam's
/// store); a project's setting stays.
fn serve(listener: &UnixListener, commands: &Mutex<Vec<Value>>, settings: &HubSettings) {
    let (stream, _) = listener.accept().expect("accept");
    let mut writer = stream.try_clone().expect("clone mock socket");
    let mut reader = BufReader::new(stream);
    write_json(
        &mut writer,
        &json!({
            "type": "daemon_hello",
            "protocol": { "name": "eukhe.daemon", "version": 7 },
            "serverCapabilities": [],
            "clientId": "mock",
        }),
    );
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
        let kind = command
            .get("type")
            .and_then(Value::as_str)
            .unwrap_or_default()
            .to_string();
        commands.lock().expect("commands").push(command.clone());
        if kind == "set_model" && command.get("allRoles") == Some(&Value::Bool(true)) {
            *settings.all.lock().expect("all") = Some(format!(
                "{}/{}",
                command["provider"].as_str().unwrap_or_default(),
                command["modelId"].as_str().unwrap_or_default()
            ));
            settings.roles.lock().expect("roles").retain(|role, _| {
                [ModelRole::Speech.id(), ModelRole::Dictation.id()].contains(role)
            });
        }
        let data = match kind.as_str() {
            "create" => json!({
                "activeSessionId": "s1", "id": "s1", "sessionId": "sess-1",
                "sessionFile": "/tmp/sess-1.jsonl",
            }),
            "get_commands" => json!({ "commands": [] }),
            "get_model_catalog" => json!({ "models": catalog(), "configuredProviders": ["prov"] }),
            "attach" => json!({
                "protocol": { "name": "eukhe.daemon", "version": 7 },
                "activeSessionId": "s1",
                "snapshot": {
                    "activeSessionId": "s1",
                    "summary": { "id": "s1", "cwd": "/tmp" },
                    "state": {
                        "activeSessionId": "s1", "cwd": "/tmp", "sessionId": "sess-1",
                        "sessionName": "hub session",
                        "model": { "provider": "prov", "id": "beta" },
                        "isStreaming": false, "isCompacting": false,
                        "sessionActions": { "queuedCount": 0, "steering": [], "followUps": [] },
                    },
                    "messages": [],
                    "lastEventSequence": 0,
                    "lastEventCursor": null,
                },
                "client": { "id": "mock", "capabilities": [] },
                "lastEventSequence": 0,
                "lastEventCursor": null,
            }),
            _ => json!({}),
        };
        respond(&mut writer, id, &kind, &data);
    }
}

/// The settings seam over an in-memory role table (global and project
/// settings) and all-roles model; every write is logged.
#[derive(Default)]
struct HubSettings {
    roles: Mutex<HashMap<&'static str, String>>,
    project: Mutex<HashMap<&'static str, String>>,
    all: Mutex<Option<String>>,
    writes: Mutex<Vec<String>>,
}

impl HubSettings {
    fn log(&self) -> Vec<String> {
        self.writes.lock().expect("writes").clone()
    }
}

/// The project file the stub's project settings live in.
const PROJECT_CFG: &str = "/p/config.cfg";

impl eukhe_tui::client_settings::ClientSettings for HubSettings {
    /// A role's own setting (the project's, then the global one), else the
    /// all-roles model (every role but speech and dictation), else its
    /// fallback.
    fn model_role(&self, role: ModelRole, _session_model: &str) -> Option<ModelRoleValue> {
        let project = self
            .project
            .lock()
            .expect("project")
            .get(role.id())
            .cloned();
        let own = self.roles.lock().expect("roles").get(role.id()).cloned();
        let all = self
            .all
            .lock()
            .expect("all")
            .clone()
            .filter(|_| !matches!(role, ModelRole::Speech | ModelRole::Dictation));
        let (selector, source) = match (project, own, all) {
            (Some(project), _, _) => (Some(project), ModelRoleSource::Project),
            (None, Some(own), _) => (Some(own), ModelRoleSource::Global),
            (None, None, Some(all)) => (Some(all), ModelRoleSource::AllRoles),
            (None, None, None) => (None, ModelRoleSource::Unset),
        };
        Some(ModelRoleValue {
            selector,
            source,
            fallback: format!("fallback-of-{}", role.id()),
            thinking: None,
        })
    }
    fn all_roles_overrides(&self, selector: &str) -> Vec<AllRolesOverride> {
        let project = self.project.lock().expect("project");
        ModelRole::ALL
            .into_iter()
            .filter_map(|role| {
                let kept = project.get(role.id()).filter(|kept| *kept != selector)?;
                Some(AllRolesOverride {
                    role,
                    selector: kept.clone(),
                    setting: format!("{}.model", role.id()),
                    file: PROJECT_CFG.to_owned(),
                })
            })
            .collect()
    }
    fn all_roles_model(&self) -> Option<ModelRoleValue> {
        let selector = self.all.lock().expect("all").clone();
        Some(ModelRoleValue {
            source: if selector.is_some() {
                ModelRoleSource::Global
            } else {
                ModelRoleSource::Unset
            },
            selector,
            fallback: "each role's default".to_owned(),
            thinking: None,
        })
    }
    fn clear_all_roles_model(&self) -> Result<()> {
        *self.all.lock().expect("all") = None;
        self.writes
            .lock()
            .expect("writes")
            .push("clear all".to_owned());
        Ok(())
    }
    fn set_model_role(
        &self,
        role: ModelRole,
        selector: &str,
        _thinking: Option<eukhe_types::ai::ModelThinkingLevel>,
    ) -> Result<()> {
        self.roles
            .lock()
            .expect("roles")
            .insert(role.id(), selector.to_string());
        self.writes
            .lock()
            .expect("writes")
            .push(format!("set {}={selector}", role.id()));
        Ok(())
    }
    fn clear_model_role(&self, role: ModelRole) -> Result<()> {
        self.roles.lock().expect("roles").remove(role.id());
        self.writes
            .lock()
            .expect("writes")
            .push(format!("clear {}", role.id()));
        Ok(())
    }
    fn theme(&self) -> Option<String> {
        None
    }
    fn set_theme(&self, _theme: &str) -> Result<()> {
        Ok(())
    }
    fn theme_sources(&self) -> eukhe_theme::ThemeSources {
        eukhe_theme::ThemeSources::default()
    }
    fn log_theme_warning(&self, _message: &str) {}
    fn log_render_error(&self, _message: &str) {}
    fn show_images(&self) -> bool {
        true
    }
    fn set_show_images(&self, _enabled: bool) -> Result<()> {
        Ok(())
    }
    fn clear_on_shrink(&self) -> bool {
        false
    }
    fn set_clear_on_shrink(&self, _enabled: bool) -> Result<()> {
        Ok(())
    }
    fn show_terminal_progress(&self) -> bool {
        false
    }
    fn set_show_terminal_progress(&self, _enabled: bool) -> Result<()> {
        Ok(())
    }
    fn fullscreen(&self) -> bool {
        false
    }
    fn set_fullscreen(&self, _enabled: bool) -> Result<()> {
        Ok(())
    }
    fn image_auto_resize(&self) -> bool {
        true
    }
    fn set_image_auto_resize(&self, _enabled: bool) -> Result<()> {
        Ok(())
    }
    fn block_images(&self) -> bool {
        false
    }
    fn set_block_images(&self, _blocked: bool) -> Result<()> {
        Ok(())
    }
    fn image_model(&self) -> Option<String> {
        None
    }
    fn enable_skill_commands(&self) -> bool {
        true
    }
    fn set_enable_skill_commands(&self, _enabled: bool) -> Result<()> {
        Ok(())
    }
    fn enable_builtin_skills(&self) -> bool {
        true
    }
    fn set_enable_builtin_skills(&self, _enabled: bool) -> Result<()> {
        Ok(())
    }
    fn show_hardware_cursor(&self) -> bool {
        false
    }
    fn set_show_hardware_cursor(&self, _enabled: bool) -> Result<()> {
        Ok(())
    }
    fn stream_pace(&self) -> eukhe_tui::pace::PaceRate {
        eukhe_tui::pace::PaceRate::DEFAULT
    }
    fn editor_padding_x(&self) -> u64 {
        0
    }
    fn set_editor_padding_x(&self, _padding: u64) -> Result<()> {
        Ok(())
    }
    fn autocomplete_max_visible(&self) -> u64 {
        5
    }
    fn set_autocomplete_max_visible(&self, _max_visible: u64) -> Result<()> {
        Ok(())
    }
    fn quiet_startup(&self) -> bool {
        false
    }
    fn set_quiet_startup(&self, _quiet: bool) -> Result<()> {
        Ok(())
    }
    fn idle_eviction_minutes(&self) -> String {
        "90".to_string()
    }
    fn set_idle_eviction_minutes(&self, _value: &str) -> Result<()> {
        Ok(())
    }
    fn mermaid_rendering_mode(&self) -> String {
        "streaming".to_string()
    }
    fn set_mermaid_rendering_mode(&self, _mode: &str) -> Result<()> {
        Ok(())
    }
    fn workflow_size(&self) -> String {
        "medium".to_string()
    }
    fn set_workflow_size(&self, _size: &str) -> Result<()> {
        Ok(())
    }
    fn tree_filter_mode(&self) -> String {
        "user-only".to_string()
    }
    fn set_tree_filter_mode(&self, _mode: &str) -> Result<()> {
        Ok(())
    }
    fn default_service_tier(&self) -> String {
        "default".to_string()
    }
    fn set_default_service_tier(&self, _tier: &str) -> Result<()> {
        Ok(())
    }
    fn chat_detail(&self) -> String {
        "details".to_string()
    }
    fn set_chat_detail(&self, _detail: &str) -> Result<()> {
        Ok(())
    }
    fn factory_enabled(&self) -> bool {
        false
    }
    fn set_factory_enabled(&self, _enabled: bool) -> Result<()> {
        Ok(())
    }
    fn warnings_anthropic_extra_usage(&self) -> bool {
        true
    }
    fn set_warnings_anthropic_extra_usage(&self, _enabled: bool) -> Result<()> {
        Ok(())
    }
}

fn options(socket: PathBuf, settings: Arc<HubSettings>) -> InteractiveOptions {
    InteractiveOptions {
        budget: None,
        models: None,
        socket_path: socket,
        cwd: PathBuf::from("/tmp"),
        session_dir: None,
        script_path: None,
        model_selection: ModelSelection::default(),
        model_catalog: catalog()
            .into_iter()
            .map(|entry| serde_json::from_value(entry).expect("catalog entry"))
            .collect(),
        model_configured_providers: std::iter::once("prov".to_string()).collect(),
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
        prompt_stash: Arc::default(),
        session_has_children: false,
        restore_dock_focus: false,
        client_settings: Some(settings),
        dictation: None,
        daemon_launcher: None,
    }
}

fn key(code: KeyCode) -> HeadlessStep {
    HeadlessStep::Key(KeyEvent::new(code, KeyModifiers::NONE))
}

fn wait_for(needle: &str) -> HeadlessStep {
    HeadlessStep::WaitRender {
        needle: needle.to_string(),
        timeout_ms: 5000,
    }
}

/// The first frame that contains `needle`.
fn first_frame_with<'a>(frames: &'a [String], needle: &str) -> &'a str {
    frames
        .iter()
        .find(|frame| frame.contains(needle))
        .unwrap_or_else(|| panic!("no frame contains {needle:?}"))
}

#[test]
fn the_hub_lists_assigns_switches_and_clears_roles() {
    std::env::remove_var("TMUX");
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("tui.sock");
    let listener = UnixListener::bind(&socket).expect("bind mock socket");
    let commands: Arc<Mutex<Vec<Value>>> = Arc::default();
    let recorded = Arc::clone(&commands);
    let settings = Arc::new(HubSettings::default());
    let served = Arc::clone(&settings);
    let handle = std::thread::spawn(move || serve(&listener, &recorded, &served));
    let steps = vec![
        HeadlessStep::WaitMs(300),
        HeadlessStep::Submit("/model".to_string()),
        wait_for("Model roles"),
        // Memory: pick the first model; it saves through the seam.
        key(KeyCode::Down),
        key(KeyCode::Enter),
        wait_for("Model for Memory compactor"),
        key(KeyCode::Enter),
        wait_for("saved globally"),
        // Chat: pick a model; the live session switches.
        key(KeyCode::Up),
        key(KeyCode::Enter),
        wait_for("Model for Chat"),
        key(KeyCode::Enter),
        wait_for("Model: "),
        // Titles (the ninth role, eight rows below chat): clear it; it
        // falls back.
        key(KeyCode::Down),
        key(KeyCode::Down),
        key(KeyCode::Down),
        key(KeyCode::Down),
        key(KeyCode::Down),
        key(KeyCode::Down),
        key(KeyCode::Down),
        key(KeyCode::Down),
        key(KeyCode::Backspace),
        wait_for("Titles: cleared, runs on fallback-of-titles"),
        key(KeyCode::Esc),
        HeadlessStep::WaitGone {
            needle: "Model roles".to_string(),
            timeout_ms: 5000,
        },
    ];
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .expect("tokio runtime");
    let outcome = runtime
        .block_on(run_interactive(
            options(socket, Arc::clone(&settings)),
            UiMode::Headless(HeadlessPlan {
                steps,
                width: 120,
                height: 30,
            }),
        ))
        .expect("interactive run");
    handle.join().expect("mock daemon finished");
    let frames = outcome.frames;

    // Every role shows (the list scrolls: 13 roles and the all-roles row
    // need more rows than the viewport), the chat row with the session's
    // model, an unset role with its fallback.
    for role in ModelRole::ALL {
        assert!(
            frames
                .iter()
                .any(|frame| frame.contains("Model roles") && frame.contains(role.label())),
            "{} in a roles frame",
            role.id()
        );
    }
    let roles = first_frame_with(&frames, "Model roles");
    assert!(roles.contains("prov/beta"), "chat shows the session model");
    assert!(roles.contains("auto: fallback-of-memory"), "{roles}");
    // After the memory pick its row shows the saved model and source.
    let saved = frames
        .iter()
        .find(|frame| frame.contains("saved globally") && frame.contains("Model roles"))
        .expect("the roles after the memory pick");
    let memory_row = saved
        .lines()
        .find(|line| line.contains("Memory compactor") && !line.contains("saved"))
        .expect("the memory row");
    assert!(
        memory_row.contains("global") && memory_row.contains("prov/"),
        "{memory_row}"
    );

    let log = settings.log();
    let memory = log
        .iter()
        .find(|entry| entry.starts_with("set memory=prov/"))
        .unwrap_or_else(|| panic!("memory saved globally: {log:?}"));
    assert_eq!(
        log.iter()
            .filter(|entry| entry.starts_with("set chat"))
            .count(),
        0,
        "chat never writes through the role seam"
    );
    assert!(log.contains(&"clear titles".to_string()), "{log:?}");
    let switches: Vec<Value> = commands
        .lock()
        .expect("commands")
        .iter()
        .filter(|command| command.get("type").and_then(Value::as_str) == Some("set_model"))
        .cloned()
        .collect();
    assert_eq!(switches.len(), 1, "one live switch: {switches:?}");
    assert_eq!(switches[0]["provider"], "prov");
    // The memory pick never touched the session.
    assert!(memory.starts_with("set memory=prov/"));
}

/// `/model --all prov/alpha` switches the session with `allRoles`: every
/// LLM role runs on it (a role's own global model is cleared), and the
/// note names only what the project still sets, with the edit that clears
/// it (never speech or dictation); the hub then shows the all-roles row
/// and each role's source; clearing the all-roles row clears it through
/// the settings seam.
#[test]
fn the_all_roles_model_switches_and_shows_each_roles_source() {
    std::env::remove_var("TMUX");
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("tui.sock");
    let listener = UnixListener::bind(&socket).expect("bind mock socket");
    let commands: Arc<Mutex<Vec<Value>>> = Arc::default();
    let recorded = Arc::clone(&commands);
    let settings = Arc::new(HubSettings::default());
    settings
        .roles
        .lock()
        .expect("roles")
        .insert(ModelRole::Image.id(), "prov/img".to_owned());
    settings
        .project
        .lock()
        .expect("project")
        .insert(ModelRole::Memory.id(), "prov/own".to_owned());
    let served = Arc::clone(&settings);
    let handle = std::thread::spawn(move || serve(&listener, &recorded, &served));
    let steps = vec![
        HeadlessStep::WaitMs(300),
        HeadlessStep::Submit("/model --all prov/alpha".to_string()),
        wait_for("All roles: prov/alpha"),
        HeadlessStep::Submit("/model".to_string()),
        wait_for("Model roles"),
        // Up from the first row wraps to the all-roles row, the last.
        key(KeyCode::Up),
        wait_for("> All roles"),
        key(KeyCode::Backspace),
        wait_for("All roles: cleared"),
        key(KeyCode::Esc),
        HeadlessStep::WaitGone {
            needle: "Model roles".to_string(),
            timeout_ms: 5000,
        },
    ];
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .expect("tokio runtime");
    let outcome = runtime
        .block_on(run_interactive(
            options(socket, Arc::clone(&settings)),
            UiMode::Headless(HeadlessPlan {
                steps,
                width: 200,
                height: 30,
            }),
        ))
        .expect("interactive run");
    handle.join().expect("mock daemon finished");
    let frames = outcome.frames;

    let switches: Vec<Value> = commands
        .lock()
        .expect("commands")
        .iter()
        .filter(|command| command.get("type").and_then(Value::as_str) == Some("set_model"))
        .cloned()
        .collect();
    assert_eq!(
        switches,
        [json!({
            "type": "set_model",
            "activeSessionId": "s1",
            "provider": "prov",
            "modelId": "alpha",
            "allRoles": true,
        })]
    );
    let outcome_frame = first_frame_with(&frames, "All roles: prov/alpha");
    let kept = format!(
        "Still set by the project: Memory compactor (prov/own); remove memory.model from {PROJECT_CFG} to use prov/alpha there too"
    );
    assert!(outcome_frame.contains(&kept), "{kept} in {outcome_frame}");
    for gone in ["Own model kept", "Not covered", "Speech", "Dictation"] {
        assert!(!outcome_frame.contains(gone), "{gone} in {outcome_frame}");
    }

    // The rows of the hub before the clear: the first roles frame (the
    // top of the list) and the frame on the all-roles row (its bottom).
    // A row is `<marker> <label>  <source> - <value>`.
    let shown: Vec<&str> = [
        first_frame_with(&frames, "Model roles"),
        first_frame_with(&frames, "> All roles"),
    ]
    .into_iter()
    .flat_map(str::lines)
    .collect();
    let labels: Vec<&str> = ModelRole::ALL
        .iter()
        .map(|role| role.label())
        .chain(["All roles"])
        .collect();
    let rows: Vec<(&str, String)> = labels
        .iter()
        .map(|label| {
            let rest = shown
                .iter()
                .rev()
                .find_map(|line| {
                    line.get(2..)?
                        .strip_prefix(label)
                        .filter(|rest| rest.starts_with("  "))
                })
                .map_or_default(|rest| rest.split_whitespace().collect::<Vec<_>>().join(" "));
            (*label, rest)
        })
        .collect();
    let row = |role: ModelRole, rest: &str| (role.label(), rest.to_owned());
    let on_all = |role: ModelRole| row(role, "all roles - prov/alpha");
    assert_eq!(
        rows,
        [
            row(ModelRole::Chat, "session - prov/alpha"),
            row(ModelRole::Memory, "project - prov/own"),
            on_all(ModelRole::Auxiliary),
            on_all(ModelRole::Image),
            on_all(ModelRole::Subagent),
            on_all(ModelRole::Worker),
            on_all(ModelRole::Gateway),
            on_all(ModelRole::Query),
            on_all(ModelRole::Titles),
            on_all(ModelRole::Judge),
            on_all(ModelRole::Translate),
            row(ModelRole::Speech, "default - auto: fallback-of-speech"),
            row(
                ModelRole::Dictation,
                "default - auto: fallback-of-dictation"
            ),
            ("All roles", "global - prov/alpha".to_owned()),
        ]
    );
    assert_eq!(
        (settings.log(), settings.all.lock().expect("all").clone()),
        (vec!["clear all".to_owned()], None)
    );
}
