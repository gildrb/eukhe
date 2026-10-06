//! Turn rendering verifiers: streamed throughput, keybindings from
//! settings, the queue strip, model resolution, and scoped model cycling.

use super::*;

/// Streaming-throughput verifier: two big (~12k-token) unpaced faux turns
/// must render at the producer's rate, not at a fixed frame-rate ceiling.
/// The worker coalesces provider deltas into latest-snapshot frames (at
/// most one per flush tick), so a burst of ~3000 deltas lands as a handful
/// of wire frames and the turn settles within seconds. The pre-fix
/// regression broadcast one wire frame per delta and the TUI starved at
/// the tick rate: a single turn rendered for over a minute.
#[tokio::test]
async fn tui_big_streamed_turns_render_at_the_producer_rate() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let supervisor = spawn_supervisor(dir.path());

    // Two ~12k-token fillers (chars/4 estimate), unpaced: the faux provider
    // streams each as ~3000 full-partial deltas as fast as it can. Every
    // ~250-word segment carries a MARK-nn marker so mid-turn frames prove
    // the applied content progressed instead of jumping once at turn end.
    let mut filler = String::new();
    for segment in 0..24 {
        let _ = write!(filler, "MARK-{segment:02} ");
        filler.push_str(&"history ".repeat(250));
    }
    // Paced at 3000 tokens/second so the ~12k-token turn streams for
    // ~4s: the mid-turn marker-progression assertion needs several wire
    // updates inside the turn (an unpaced faux finishes in ~0.3s and the
    // whole stream lands in a handful of frames). The 45s settle bound is
    // calibrated against the producer pace with a load-realistic margin: a
    // healthy render settles in seconds even on a loaded box, while the
    // pre-fix starvation pipeline (one ~4-token delta per 50ms tick) took
    // 150+ seconds per turn — an order of magnitude past the bound.
    let script = serde_json::json!({
        "engine": "faux",
        "tokensPerSecond": 3_000,
        "responses": [
            { "text": filler.clone() },
            { "text": format!("{filler}second big turn done, tail marker intact") },
        ],
    });
    std::fs::write(dir.path().join("script.json"), script.to_string()).expect("write script");
    let options = eukhe_tui::interactive::InteractiveOptions {
        models: None,
        socket_path: supervisor.socket.clone(),
        cwd: dir.path().to_path_buf(),
        session_dir: Some(session_dir.clone()),
        script_path: Some(dir.path().join("script.json")),
        model_selection: eukhe_tui::interactive::ModelSelection::default(),
        model_catalog: Vec::new(),
        model_configured_providers: std::collections::HashSet::default(),
        model_recent_models: Vec::new(),
        default_thinking_level: None,
        no_session: false,
        session: eukhe_tui::interactive::SessionSelection::New,
        show_images: true,
        initial_message: None,
        theme: "eukhe".to_string(),
        code_block_indent: "  ".to_string(),

        tree_filter_mode: String::new(),
        branch_summary_skip_prompt: false,
        version: "0.0.0".to_string(),
        onboarding: None,
        telemetry_disabled: None,
        client_auth: None,
        traces: None,
        provider_auth: None,
        telemetry: None,
        keybindings: eukhe_tui::keybindings::KeybindingsManager::new(),
        session_rlm_depth: None,
        prompt_stash: std::sync::Arc::default(),
        session_has_children: false,
        restore_dock_focus: false,
        client_settings: None,
    };
    // 45s per turn is the throughput bound: the producer finishes each
    // turn in ~4s, so 45s tolerates real box load (sibling e2e binaries,
    // daemons from other suites) while a starved render — 150+ seconds per
    // turn before the fix — still expires the barrier with margin.
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            eukhe_tui::interactive::HeadlessStep::Submit("first".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 45_000 },
            eukhe_tui::interactive::HeadlessStep::Submit("second".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 45_000 },
        ],
        width: 100,
        height: 30,
    };
    let started = Instant::now();
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");
    let wall = started.elapsed();

    // Verification seam: dump the captured frames for manual frame-diffing
    // against the TS product (EUKHE_TUI_DUMP_FRAMES=<dir>).
    if let Ok(dump) = std::env::var("EUKHE_TUI_DUMP_FRAMES") {
        for (index, frame) in outcome.frames.iter().enumerate() {
            let _ = std::fs::write(
                std::path::Path::new(&dump).join(format!("stream-frame-{index:03}.txt")),
                frame,
            );
        }
    }
    let rendered = outcome.frames.join("\n");
    assert!(
        !rendered.contains("timed out waiting for the turn to finish"),
        "a WaitIdle barrier expired; the render starved behind the stream:\n{rendered}"
    );
    // Both turns settled with their full text (the window follows the
    // tail, so the second turn's marker is the strongest full-render proof).
    assert!(
        rendered.contains("tail marker intact"),
        "the second big turn fully rendered:\n{rendered}"
    );
    assert_eq!(
        outcome.last_assistant_text.as_deref(),
        Some(format!("{filler}second big turn done, tail marker intact").as_str()),
        "the final assistant text is the full second turn"
    );
    // The applied content progressed mid-turn: the tail-following window
    // showed a growing run of segment markers while the turn streamed (a
    // starved pipeline shows the whole turn once at its end, so only the
    // final markers would ever appear).
    let marks: std::collections::BTreeSet<String> = outcome
        .frames
        .iter()
        .flat_map(|frame| frame.lines())
        .flat_map(|line| line.split_whitespace())
        .filter(|word| word.starts_with("MARK-"))
        .map(std::string::ToString::to_string)
        .collect();
    assert!(
        marks.len() >= 5,
        "only {len} segment markers ever rendered mid-turn (needs >= 5); the applied stream starved",
        len = marks.len()
    );
    assert!(
        wall < Duration::from_secs(100),
        "the whole run took {wall:?}; the turn render must keep up with the producer"
    );
    drop(supervisor);
}

/// User-keybinding verifier (TS `keybindings.json` parity, roadmap item
/// "keybinding customization"): a settings fixture rebinding
/// `app.tools.expand` from `ctrl+o` to `ctrl+alt+x` drives the whole
/// surface — the prompt-context hint renders the OVERRIDE key, the
/// override key fires the action, the default key no longer does, and
/// `/hotkeys` documents the effective binding instead of the default.
#[tokio::test]
async fn tui_renders_and_fires_user_keybindings_from_settings() {
    use crossterm::event::{KeyCode, KeyModifiers};

    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    // The settings fixture: one binding overridden exactly like a user's
    // `~/.eukhe/keybindings.json` would.
    std::fs::write(
        agent_dir.join("keybindings.json"),
        r#"{ "app.tools.expand": "ctrl+alt+x" }"#,
    )
    .expect("write keybindings.json");
    let supervisor = spawn_supervisor(dir.path());
    let script = serde_json::json!({
        "engine": "faux",
        "responses": [{ "text": "scripted reply", "delayMs": 10 }],
    });
    std::fs::write(dir.path().join("script.json"), script.to_string()).expect("write script");

    let options = eukhe_tui::interactive::InteractiveOptions {
        models: None,
        socket_path: supervisor.socket.clone(),
        cwd: dir.path().to_path_buf(),
        session_dir: Some(session_dir.clone()),
        script_path: Some(dir.path().join("script.json")),
        model_selection: eukhe_tui::interactive::ModelSelection::default(),
        model_catalog: Vec::new(),
        model_configured_providers: std::collections::HashSet::new(),
        model_recent_models: Vec::new(),
        default_thinking_level: None,
        no_session: false,
        session: eukhe_tui::interactive::SessionSelection::New,
        show_images: true,
        initial_message: None,
        theme: "eukhe".to_string(),
        code_block_indent: "  ".to_string(),
        tree_filter_mode: String::new(),
        branch_summary_skip_prompt: false,
        version: "0.0.0".to_string(),
        onboarding: None,
        telemetry_disabled: None,
        client_auth: None,
        traces: None,
        provider_auth: None,
        telemetry: None,
        // The exact load path the CLI uses: the fixture overrides the
        // default set.
        keybindings: eukhe_tui::keybindings::KeybindingsManager::create(&agent_dir),
        session_rlm_depth: None,
        prompt_stash: std::sync::Arc::default(),
        session_has_children: false,
        restore_dock_focus: false,
        client_settings: None,
    };
    let key = |code: KeyCode, modifiers: KeyModifiers| {
        eukhe_tui::interactive::HeadlessStep::Key(crossterm::event::KeyEvent::new(code, modifiers))
    };
    let ctrl_alt_x = key(
        KeyCode::Char('x'),
        KeyModifiers::CONTROL | KeyModifiers::ALT,
    );
    let ctrl_o = key(KeyCode::Char('o'), KeyModifiers::CONTROL);
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            // One scripted turn so the transcript holds a rendered reply.
            eukhe_tui::interactive::HeadlessStep::Submit("hello".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
            // The user's key fires the rebound action: overview -> details.
            ctrl_alt_x,
            // The default key must no longer fire it (a second cycle would
            // reach the "all" mode).
            ctrl_o,
            // The documentation surface renders the effective binding: the
            // read-only info panel mounts over the dock (the operator's
            // 2026-09-26 directive — the guide no longer floods the
            // transcript), End jumps the scrollable window to the
            // document's bottom, and Esc closes it back to the dock.
            eukhe_tui::interactive::HeadlessStep::Submit("/hotkeys".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitRender {
                needle: "Move cursor / browse history".to_string(),
                timeout_ms: 30_000,
            },
            eukhe_tui::interactive::HeadlessStep::Key(crossterm::event::KeyEvent::new(
                crossterm::event::KeyCode::End,
                crossterm::event::KeyModifiers::NONE,
            )),
            eukhe_tui::interactive::HeadlessStep::WaitRender {
                needle: "Slash commands".to_string(),
                timeout_ms: 30_000,
            },
            eukhe_tui::interactive::HeadlessStep::Key(crossterm::event::KeyEvent::new(
                crossterm::event::KeyCode::Esc,
                crossterm::event::KeyModifiers::NONE,
            )),
            eukhe_tui::interactive::HeadlessStep::WaitGone {
                needle: "scroll - Esc close".to_string(),
                timeout_ms: 30_000,
            },
        ],
        width: 120,
        // Tall enough that the `/hotkeys` info panel holds a real window
        // of the guide.
        height: 60,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");
    let rendered = outcome.frames.join("\n");

    // The hint renders the user's binding, not the default, at the
    // collapsed startup detail level (the overview mode; operator
    // directive 2026-09-28).
    assert!(
        rendered.contains("Collapsed mode (Ctrl+Alt+X to expand)"),
        "the prompt-context hint renders the override:\n{rendered}"
    );
    // The override key fired the action: the detail cycled to the
    // thinking-reveal level.
    assert!(
        rendered.contains("Details mode (Ctrl+Alt+X to expand)"),
        "the override key cycled conversation detail:\n{rendered}"
    );
    // The default key leaves the detail unchanged: the default ctrl+o is
    // no longer bound, so the level never reaches the expanded mode.
    assert!(
        !rendered.contains("Expanded mode (Ctrl+Alt+X to collapse)"),
        "the default ctrl+o must not cycle after the override:\n{rendered}"
    );
    // The scripted turn still ran under the custom bindings.
    assert!(
        rendered.contains("scripted reply"),
        "the scripted turn rendered:\n{rendered}"
    );
    // `/hotkeys` renders in the info panel: the guide's first window
    // rendered (the Navigation row), End jumped the scrollable window to
    // the document's bottom (the slash-commands row), and the override's
    // own row is covered by the hotkeys guide unit tests.
    assert!(
        rendered.contains("Move cursor / browse history"),
        "the hotkeys panel rendered the guide:\n{rendered}"
    );
    assert!(
        rendered.contains("Slash commands"),
        "the End key jumped the panel to the guide's bottom:\n{rendered}"
    );
    // The removed default key is gone (no other default binding uses
    // ctrl+o).
    assert!(
        !rendered.contains("Ctrl+O"),
        "the hotkeys guide must not show the removed default:\n{rendered}"
    );
    // The guide stayed out of the transcript (the operator's no-flooding
    // directive): after Esc closed the panel the last frame holds the
    // scripted reply and the dock, not the guide's rows.
    let last = outcome.frames.last().expect("frames");
    assert!(
        !last.contains("Move cursor / browse history"),
        "the hotkeys guide never lands in the transcript:\n{last}"
    );
    assert!(
        last.contains("Details mode (Ctrl+Alt+X to expand)"),
        "the dock returned after the panel closed:\n{last}"
    );
    drop(supervisor);
}

/// The visible follow-up queue (TS `queuedMessagesContainer`): prompts
/// submitted while a turn runs park on their lanes — Enter on the steering
/// lane, the follow-up key on the follow-up lane — and render as dim
/// preview rows above the prompt dock with the browse hint. The strip
/// clears as the queue drains behind the run.
#[tokio::test]
async fn tui_prompts_queued_behind_a_turn_render_the_queue_strip() {
    use crossterm::event::{KeyCode, KeyModifiers};
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let supervisor = spawn_supervisor(dir.path());

    // The first turn holds in flight for 1.5s (`delayMs`): the parked
    // submissions land inside that window, deterministically busy (the
    // runner flips `busy` when it pops the work, long before the 750ms
    // barrier below).
    let script_path = dir.path().join("script.json");
    let script = serde_json::json!({ "responses": [
        { "text": "first turn", "delayMs": 1500 },
        { "text": "steered delivery" },
        { "text": "followed up delivery" },
    ]});
    std::fs::write(&script_path, script.to_string()).expect("write script");

    let options = eukhe_tui::interactive::InteractiveOptions {
        models: None,
        socket_path: supervisor.socket.clone(),
        cwd: dir.path().to_path_buf(),
        session_dir: Some(session_dir.clone()),
        script_path: Some(script_path.clone()),
        model_selection: eukhe_tui::interactive::ModelSelection::default(),
        model_catalog: Vec::new(),
        model_configured_providers: std::collections::HashSet::default(),
        model_recent_models: Vec::new(),
        default_thinking_level: None,
        no_session: false,
        session: eukhe_tui::interactive::SessionSelection::New,
        show_images: true,
        initial_message: None,
        theme: "eukhe".to_string(),
        code_block_indent: "  ".to_string(),
        tree_filter_mode: String::new(),
        branch_summary_skip_prompt: false,
        version: "0.0.0".to_string(),
        onboarding: None,
        telemetry_disabled: None,
        client_auth: None,
        traces: None,
        provider_auth: None,
        telemetry: None,
        keybindings: eukhe_tui::keybindings::KeybindingsManager::new(),
        session_rlm_depth: None,
        prompt_stash: std::sync::Arc::default(),
        session_has_children: false,
        restore_dock_focus: false,
        client_settings: None,
    };
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            eukhe_tui::interactive::HeadlessStep::Submit("start the slow turn".to_string()),
            // Half-way through the scripted hold the turn is provably
            // running: the parked submissions below queue behind it.
            eukhe_tui::interactive::HeadlessStep::WaitMs(750),
            // Enter while the turn runs parks on the steering lane.
            eukhe_tui::interactive::HeadlessStep::Submit("steering prompt".to_string()),
            // The follow-up key (alt+enter) parks on the follow-up lane.
            eukhe_tui::interactive::HeadlessStep::Type("follow-up prompt".to_string()),
            eukhe_tui::interactive::HeadlessStep::Key(crossterm::event::KeyEvent::new(
                KeyCode::Enter,
                KeyModifiers::ALT,
            )),
            // The barrier holds until the queue drained behind the turn.
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 60_000 },
        ],
        width: 100,
        height: 30,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");

    assert!(!outcome.frames.is_empty(), "frames were captured");
    let rendered = outcome.frames.join("\n");
    // The queue strip rendered both parked previews and the browse hint.
    assert!(
        rendered.contains("Steering: steering prompt"),
        "the steering preview rendered:\n{rendered}"
    );
    assert!(
        rendered.contains("Follow-up: follow-up prompt"),
        "the follow-up preview rendered:\n{rendered}"
    );
    assert!(
        rendered.contains("to browse and edit queued messages"),
        "the browse hint rendered:\n{rendered}"
    );
    // The queued prompts delivered once the run went idle: their turns'
    // scripted responses rendered, and the strip cleared.
    assert!(
        rendered.contains("steered delivery"),
        "the steering prompt delivered:\n{rendered}"
    );
    assert!(
        rendered.contains("followed up delivery"),
        "the follow-up prompt delivered:\n{rendered}"
    );
    let last = outcome.frames.last().expect("a final frame");
    assert!(
        !last.contains("to browse and edit queued messages")
            && !last.contains("Steering: ")
            && !last.contains("Follow-up: "),
        "the queue strip cleared after delivery:\n{last}"
    );
    drop(supervisor);
}

/// The live-dogfood failure pair (Kevin's repro, 2026-09-21): a session
/// created with an explicit `--provider`/`--model` on a worker whose
/// registry has no configured credentials — the auth-scoped `available`
/// list is empty while the bundled catalog still carries the flagged
/// model. The pre-fix turn failed with "No models available" (the daemon
/// fed the resolver the auth-scoped list; TS `resolveCliModel` uses
/// `getAll()`), and a `/model` pick failed with "Model not found" leaving
/// the status label stale. The fixed contract is TS parity: the flagged
/// model resolves from the full catalog, the turn fails at the run-start
/// auth validation with the TS login-guidance message
/// (`_validateCanStartAgentRun`), and the pick of the unsigned provider
/// never surfaces the dead-end "Model not found" — the daemon's typed
/// refusal routes the sign-in flow (TS `ensureModelProviderConfigured`),
/// which in this headless composition (no provider-auth hook) lands the TS
/// external-config error; the failed pick keeps the label (nothing
/// switched).
#[tokio::test]
async fn tui_flagged_model_turn_reports_the_ts_preflight_error_without_credentials() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let supervisor = spawn_supervisor(dir.path());
    // The dogfood layout: no models.json, no stored credentials, and the
    // hermetic supervisor strips every ambient provider key, so the
    // worker's auth-scoped catalog is empty while the bundled catalog
    // carries the flagged model. The picker catalog is a client-side
    // snapshot (the same seam the composition root injects).
    let glm: eukhe_types::ai::Model = serde_json::from_value(serde_json::json!({
        "id": "z-ai/glm-5.3", "name": "GLM 5.3", "api": "openai-completions",
        "provider": "prime-inference", "baseUrl": "https://inference.example/v1",
        "reasoning": true, "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 128_000, "maxTokens": 8192
    }))
    .expect("catalog entry");
    let options = eukhe_tui::interactive::InteractiveOptions {
        models: None,
        socket_path: supervisor.socket.clone(),
        cwd: dir.path().to_path_buf(),
        session_dir: Some(session_dir.clone()),
        script_path: None,
        model_selection: eukhe_tui::interactive::ModelSelection {
            provider: Some("prime-inference".to_string()),
            model: Some("z-ai/glm-5.3".to_string()),
            ..Default::default()
        },
        model_catalog: vec![glm],
        model_configured_providers: std::collections::HashSet::default(),
        model_recent_models: Vec::new(),
        default_thinking_level: None,
        no_session: false,
        session: eukhe_tui::interactive::SessionSelection::New,
        show_images: true,
        client_settings: None,
        initial_message: None,
        theme: "eukhe".to_string(),
        code_block_indent: "  ".to_string(),
        tree_filter_mode: String::new(),
        branch_summary_skip_prompt: false,
        version: "0.0.0".to_string(),
        onboarding: None,
        telemetry_disabled: None,
        client_auth: None,
        traces: None,
        provider_auth: None,
        telemetry: None,
        keybindings: eukhe_tui::keybindings::KeybindingsManager::new(),
        session_rlm_depth: None,
        prompt_stash: std::sync::Arc::default(),
        session_has_children: false,
        restore_dock_focus: false,
    };
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
            eukhe_tui::interactive::HeadlessStep::Submit("/model".to_string()),
            eukhe_tui::interactive::HeadlessStep::Type("glm".to_string()),
            eukhe_tui::interactive::HeadlessStep::Type("\n".to_string()),
            eukhe_tui::interactive::HeadlessStep::Submit("hello".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 60_000 },
        ],
        width: 120,
        height: 36,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");
    let rendered = outcome.frames.join("\n");
    assert!(
        rendered.contains("must be configured externally") && rendered.contains("prime-inference"),
        "the pick against the empty auth-scoped catalog routes the sign-in flow (no provider-auth hook in this composition, so the TS external-config error):\n{rendered}"
    );
    assert!(
        !rendered.contains("Model not found: "),
        "the not-signed-in pick never surfaces the dead-end refusal (the typed sign-in class):\n{rendered}"
    );
    assert!(
        rendered.contains("No API key found for prime-inference"),
        "the turn resolves the flagged model from the full catalog and fails at the run-start auth validation with the TS message:\n{rendered}"
    );
    assert!(
        !rendered.contains("No models available"),
        "the auth-blind turn resolution must not report the resolver's empty-catalog error:\n{rendered}"
    );
    let last = outcome.frames.last().expect("a final frame");
    // The reasoning fixture renders its live effort suffix (TS
    // `getModelContextLabel`): the label the failed pick must hold is
    // `model:effort`, with the daemon's effective level for glm-5.3.
    assert!(
        last.contains("z-ai/glm-5.3:high -"),
        "the footer label holds the resolved flagged model (the failed pick switched nothing):\n{last}"
    );
    drop(supervisor);
}

/// The dogfood acceptance for a pick that CAN apply: a models.json provider
/// (its inline key configures auth) carries two models, the session starts
/// on the first, and a `/model` pick of the second must move the footer
/// label immediately and leave the next turn resolving the switched model
/// (the turn reaches the provider; the dead endpoint's retry banner is the
/// proof the run started, not a resolution failure).
#[tokio::test]
async fn tui_model_pick_refreshes_the_label_and_the_next_turn_resolves() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    std::fs::write(
        agent_dir.join("models.json"),
        serde_json::json!({
            "providers": {
                "test-provider": {
                    "api": "openai-completions",
                    "baseUrl": "http://127.0.0.1:9/v1",
                    "apiKey": "sk-test",
                    "models": [
                        { "id": "mock-1", "name": "Mock 1", "api": "openai-completions",
                          "baseUrl": "http://127.0.0.1:9/v1", "contextWindow": 128_000,
                          "maxTokens": 4096 },
                        { "id": "mock-2", "name": "Mock 2", "api": "openai-completions",
                          "baseUrl": "http://127.0.0.1:9/v1", "contextWindow": 128_000,
                          "maxTokens": 4096 }
                    ]
                }
            }
        })
        .to_string(),
    )
    .expect("write models.json");
    // Retries off (settings default is a 3-attempt retry chain whose
    // countdown holds the turn busy past the headless idle window): the
    // post-switch turn fails once at the dead endpoint and settles.
    std::fs::write(
        agent_dir.join("settings.json"),
        serde_json::json!({ "retry": { "enabled": false } }).to_string(),
    )
    .expect("write settings.json");
    let supervisor = spawn_supervisor(dir.path());
    // The client-side catalog snapshot over the same registry scope as the
    // daemon's (hermetic auth; the models.json key is the only configured
    // credential).
    let auth = eukhe_core::auth::AuthStorage::in_memory_without_env(
        &eukhe_core::auth::AuthStorageData::default(),
        std::sync::Arc::new(eukhe_core::auth::NoOAuth),
    );
    let mut registry =
        eukhe_core::models::ModelRegistry::create(auth, agent_dir.join("models.json"));
    registry.load_private_authorization_from_cache();
    let catalog: Vec<eukhe_types::ai::Model> =
        registry.get_available().into_iter().cloned().collect();
    assert_eq!(
        catalog.len(),
        2,
        "both models.json models resolve available"
    );
    let options = eukhe_tui::interactive::InteractiveOptions {
        models: None,
        socket_path: supervisor.socket.clone(),
        cwd: dir.path().to_path_buf(),
        session_dir: Some(session_dir.clone()),
        script_path: None,
        model_selection: eukhe_tui::interactive::ModelSelection::default(),
        model_catalog: catalog,
        model_configured_providers: ["test-provider".to_string()].into_iter().collect(),
        model_recent_models: Vec::new(),
        default_thinking_level: None,
        no_session: false,
        session: eukhe_tui::interactive::SessionSelection::New,
        show_images: true,
        client_settings: None,
        initial_message: None,
        theme: "eukhe".to_string(),
        code_block_indent: "  ".to_string(),
        tree_filter_mode: String::new(),
        branch_summary_skip_prompt: false,
        version: "0.0.0".to_string(),
        onboarding: None,
        telemetry_disabled: None,
        client_auth: None,
        traces: None,
        provider_auth: None,
        telemetry: None,
        keybindings: eukhe_tui::keybindings::KeybindingsManager::new(),
        session_rlm_depth: None,
        prompt_stash: std::sync::Arc::default(),
        session_has_children: false,
        restore_dock_focus: false,
    };
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
            eukhe_tui::interactive::HeadlessStep::Submit("/model".to_string()),
            eukhe_tui::interactive::HeadlessStep::Type("mock-2".to_string()),
            eukhe_tui::interactive::HeadlessStep::Type("\n".to_string()),
            eukhe_tui::interactive::HeadlessStep::Submit("turn after the switch".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 90_000 },
        ],
        width: 120,
        height: 36,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");
    let rendered = outcome.frames.join("\n");
    assert!(
        rendered.contains("Model: mock-2"),
        "the pick applied through the daemon set_model switch:\n{rendered}"
    );
    assert!(
        !rendered.contains("No models available"),
        "the switched model must resolve for the next turn:\n{rendered}"
    );
    assert!(
        rendered.contains("Error: Connection error."),
        "the post-switch turn reached the dead provider (not a resolution failure):\n{rendered}"
    );
    let last = outcome.frames.last().expect("a final frame");
    assert!(
        last.contains("mock-2 -"),
        "the footer label refreshed to the picked model:\n{last}"
    );
    drop(supervisor);
}

/// `--models` scope end to end: the create config's `models` patterns
/// reach the daemon session through the supervisor's durable create
/// (the scope rides the same allow-list a respawn replays), and the
/// declared cycle keys (TS `handleModelCycle`) walk the session's
/// scope order — not the catalog's: mock-2 sits between the scoped
/// pair in the catalog and must never appear, forward cycles
/// mock-1 -> mock-3, backward mock-3 -> mock-1, both with the
/// provider-qualified status row. The cycle arms had no dispatch site
/// on the base, so the test fails there at the first render barrier.
#[tokio::test]
async fn tui_scoped_models_cycle_through_the_session_scope() {
    use crossterm::event::{KeyCode, KeyModifiers};

    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    std::fs::write(
        agent_dir.join("models.json"),
        serde_json::json!({
            "providers": {
                "test-provider": {
                    "api": "openai-completions",
                    "baseUrl": "http://127.0.0.1:9/v1",
                    "apiKey": "sk-test",
                    "models": [
                        { "id": "mock-1", "name": "Mock 1", "api": "openai-completions",
                          "baseUrl": "http://127.0.0.1:9/v1", "contextWindow": 128_000,
                          "maxTokens": 4096 },
                        { "id": "mock-2", "name": "Mock 2", "api": "openai-completions",
                          "baseUrl": "http://127.0.0.1:9/v1", "contextWindow": 128_000,
                          "maxTokens": 4096 },
                        { "id": "mock-3", "name": "Mock 3", "api": "openai-completions",
                          "baseUrl": "http://127.0.0.1:9/v1", "contextWindow": 128_000,
                          "maxTokens": 4096 }
                    ]
                }
            }
        })
        .to_string(),
    )
    .expect("write models.json");
    let supervisor = spawn_supervisor(dir.path());
    let mut options = base_options(&supervisor, dir.path(), &session_dir);
    // No scripted engine: the real startup chain resolves the session's
    // model against the registry (the scripted engine answers no model
    // and the cycle would refuse to switch).
    options.script_path = None;
    options.models = Some(vec![
        "test-provider/mock-1".to_string(),
        "test-provider/mock-3".to_string(),
    ]);
    let key = |code: KeyCode, modifiers: KeyModifiers| {
        eukhe_tui::interactive::HeadlessStep::Key(crossterm::event::KeyEvent::new(code, modifiers))
    };
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            // The startup chain lands on the first scoped model; the
            // attach settles before the cycle.
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
            // alt+m cycles forward through the scope: mock-1 -> mock-3
            // (unscoped cycling would show mock-2, the next available).
            key(KeyCode::Char('m'), KeyModifiers::ALT),
            eukhe_tui::interactive::HeadlessStep::WaitRender {
                needle: "Model: test-provider/mock-3".to_string(),
                timeout_ms: 30_000,
            },
            // shift+alt+m cycles backward: mock-3 -> mock-1.
            key(KeyCode::Char('m'), KeyModifiers::SHIFT | KeyModifiers::ALT),
            eukhe_tui::interactive::HeadlessStep::WaitRender {
                needle: "Model: test-provider/mock-1".to_string(),
                timeout_ms: 30_000,
            },
        ],
        width: 120,
        height: 36,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");
    let rendered = outcome.frames.join("\n");
    assert!(
        rendered.contains("Model: test-provider/mock-3"),
        "alt+m cycled forward through the scope:\n{rendered}"
    );
    assert!(
        !rendered.contains("Model: test-provider/mock-2"),
        "the unscoped catalog order never surfaced:\n{rendered}"
    );
    assert!(
        rendered.contains("Model: test-provider/mock-1"),
        "shift+alt+m cycled backward through the scope:\n{rendered}"
    );
    drop(supervisor);
}
