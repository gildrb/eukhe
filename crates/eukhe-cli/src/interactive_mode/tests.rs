//! The interactive-mode unit battery (moved with its concern): the session
//! flag mapping, the continue-recent startup session, the onboarding gate and
//! settings sink, and the startup fork/select contracts.

use super::*;
// The sink's answers flow through the eukhe-tui trait; the tests call the
// trait methods directly (the impl header alone does not import them).
use eukhe_tui::interactive::OnboardingSink;

#[test]
fn session_flags_map_to_selections() {
    let mut session = crate::mode::SessionOptions::default();
    let dir = tempfile::TempDir::new().expect("temp dir");
    let session_dir = dir.path().join("sessions");
    std::fs::create_dir_all(&session_dir).expect("sessions dir");
    assert_eq!(
        session_selection(&session, Some(session_dir.as_path())),
        SessionSelection::New
    );
    // `--continue` resolves before this mapping
    // (`continue_startup_selection`): the flag alone maps nowhere here.
    session.continue_recent = true;
    assert_eq!(
        session_selection(&session, Some(session_dir.as_path())),
        SessionSelection::New
    );
    session.continue_recent = false;
    session.resume = Some("a1b2c3".to_string());
    // A bare selector that is not a file attaches a live session id.
    assert_eq!(
        session_selection(&session, Some(session_dir.as_path())),
        SessionSelection::Attach("a1b2c3".to_string())
    );
    // An id with a saved file under the sessions dir reopens the file.
    let saved = session_dir.join("deadbeefcafe.jsonl");
    std::fs::write(&saved, "{}\n").expect("write file");
    session.resume = Some("deadbeefcafe".to_string());
    assert_eq!(
        session_selection(&session, Some(session_dir.as_path())),
        SessionSelection::Resume(saved)
    );
    // An explicit file path reopens that session file.
    let file = dir.path().join("saved.jsonl");
    std::fs::write(&file, "{}\n").expect("write file");
    session.resume = Some(file.to_string_lossy().to_string());
    assert_eq!(
        session_selection(&session, Some(session_dir.as_path())),
        SessionSelection::Resume(file)
    );
}

fn run_options_for_continue(dir: &std::path::Path) -> RunOptions {
    use crate::mode::{AppMode, RuntimeConfig};
    RunOptions {
        app_mode: AppMode::Interactive,
        config: RuntimeConfig {
            cwd: dir.to_path_buf(),
            agent_dir: dir.join("agent"),
            ..Default::default()
        },
        session: crate::mode::SessionOptions::default(),
        messages: Vec::new(),
        file_args: Vec::new(),
        daemon_socket: None,
        list_models: None,
        initial_message: None,
        initial_images: Vec::new(),
        verbose: false,
        offline: false,
        agents_view_requested: false,
        attach_agent: None,
    }
}

/// Push every file of a durable storage to `at`: the listing's recency
/// is the newest file time of the storage.
fn touch_storage(dir: &std::path::Path, at: std::time::SystemTime) {
    for entry in std::fs::read_dir(dir).expect("read storage dir") {
        let path = entry.expect("storage entry").path();
        if path.is_file() {
            std::fs::File::options()
                .append(true)
                .open(&path)
                .expect("open storage file")
                .set_modified(at)
                .expect("set mtime");
        }
    }
}

/// P1: `--continue` reopens the newest saved session of the cwd (TS
/// `SessionManager.continueRecent`). Sessions live in durable
/// `<sessions>/<id>/` storages; another cwd's newer session never wins.
#[test]
fn continue_reopens_the_newest_durable_session_for_the_cwd() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let cwd = dir.path().join("project");
    let other = dir.path().join("other");
    let session_dir = dir.path().join("sessions");
    std::fs::create_dir_all(&cwd).expect("cwd");
    std::fs::create_dir_all(&other).expect("other cwd");
    std::fs::create_dir_all(&session_dir).expect("sessions dir");
    // Forks are durable storages of their cwd; the legacy sources go, so
    // only durable storages remain to pick from.
    let (source, id) = seed_session(&session_dir, &cwd, "first question");
    let older = fork(&fork_options(&cwd, &session_dir), &id);
    let newer = fork(&fork_options(&cwd, &session_dir), &id);
    std::fs::remove_file(source).expect("drop the legacy source");
    let (source, id) = seed_session(&session_dir, &other, "elsewhere");
    let foreign = fork(&fork_options(&other, &session_dir), &id);
    std::fs::remove_file(source).expect("drop the legacy source");
    let now = std::time::SystemTime::now();
    touch_storage(&older, now + std::time::Duration::from_mins(1));
    touch_storage(&newer, now + std::time::Duration::from_mins(2));
    touch_storage(&foreign, now + std::time::Duration::from_mins(3));

    let mut options = fork_options(&cwd, &session_dir);
    options.session.continue_recent = true;
    assert_eq!(
        continue_startup_selection(&options).expect("continue resolves"),
        Some(SessionSelection::Resume(newer.clone()))
    );
    // The whole launch opens it as the startup session.
    let tui = build_tui_options(
        &options,
        dir.path().join("d.sock"),
        std::sync::Arc::default(),
    )
    .expect("build the launch");
    assert_eq!(tui.session, SessionSelection::Resume(newer));
}

/// Without a saved session for the cwd, `--continue` falls through to the
/// fresh-session run (TS `continueRecent`'s own fallback); an explicit
/// `--resume` selector or `--no-session` owns the selection first (the TS
/// flag order), and a launch without the flag never continues.
#[test]
fn continue_falls_back_and_defers_to_resume_and_no_session() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let cwd = dir.path().join("project");
    let other = dir.path().join("other");
    let session_dir = dir.path().join("sessions");
    std::fs::create_dir_all(&cwd).expect("cwd");
    std::fs::create_dir_all(&other).expect("other cwd");
    std::fs::create_dir_all(&session_dir).expect("sessions dir");
    seed_session(&session_dir, &other, "elsewhere");

    let mut options = fork_options(&cwd, &session_dir);
    options.session.continue_recent = true;
    assert_eq!(
        continue_startup_selection(&options).expect("continue resolves"),
        None,
        "only another cwd's session: a fresh session"
    );
    seed_session(&session_dir, &cwd, "here");
    assert!(
        continue_startup_selection(&options)
            .expect("continue resolves")
            .is_some(),
        "a session of the cwd continues"
    );
    options.session.resume = Some("named-session".to_string());
    assert_eq!(
        continue_startup_selection(&options).expect("continue resolves"),
        None,
        "an explicit --resume selector wins over --continue"
    );
    options.session.resume = None;
    options.session.no_session = true;
    assert_eq!(
        continue_startup_selection(&options).expect("continue resolves"),
        None,
        "--no-session owns the launch: nothing to continue"
    );
    options.session.no_session = false;
    options.session.continue_recent = false;
    assert_eq!(
        continue_startup_selection(&options).expect("continue resolves"),
        None,
        "no --continue: nothing to continue"
    );
}

#[test]
fn onboarding_gate_follows_settings_and_auth() {
    use crate::mode::{AppMode, RuntimeConfig};

    fn run_options(dir: &std::path::Path) -> RunOptions {
        RunOptions {
            app_mode: AppMode::Interactive,
            config: RuntimeConfig {
                cwd: dir.to_path_buf(),
                agent_dir: dir.join("agent"),
                ..Default::default()
            },
            session: crate::mode::SessionOptions::default(),
            messages: Vec::new(),
            file_args: Vec::new(),
            daemon_socket: None,
            list_models: None,
            initial_message: None,
            initial_images: Vec::new(),
            verbose: false,
            offline: false,
            agents_view_requested: false,
            attach_agent: None,
        }
    }

    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent = dir.path().join("agent");
    std::fs::create_dir_all(&agent).expect("agent dir");

    // A completed onboarding never reopens, regardless of model state.
    let mut settings = eukhe_core::settings::SettingsManager::create(dir.path(), &agent);
    settings.set_onboarding_shown(true).expect("set flag");
    let options = run_options(dir.path());
    assert!(onboarding_task(&options, None).is_none());
    // Back to a first run for the readiness checks below.
    settings.set_onboarding_shown(false).expect("reset flag");

    // Flagless launch: a models.json provider key + saved default model
    // resolve the startup model, so the onboarding task mounts (TS
    // `isOnboardingModelReady` over the `findInitialModel` chain); on a
    // fresh home it completes silently.
    std::fs::write(
        agent.join("models.json"),
        r#"{ "providers": {
                "onboard-test": {
                    "baseUrl": "https://onboard.test", "apiKey": "sk-onboard",
                    "api": "openai-completions",
                    "models": [ { "id": "m1", "name": "M1" } ]
                },
                "onboard-naked": {
                    "baseUrl": "https://naked.test",
                    // Present (custom models require "apiKey", same as TS)
                    // but the `!command` resolves to no credential, so the
                    // provider stays unauthorized.
                    "apiKey": "!exit 1",
                    "api": "openai-completions",
                    "models": [ { "id": "m2", "name": "M2" } ]
                }
            } }"#,
    )
    .expect("models.json");
    let mut settings = eukhe_core::settings::SettingsManager::create(dir.path(), &agent);
    settings
        .set_default_model_and_provider("onboard-test", "m1")
        .expect("saved default")
        .applied()
        .expect("the value applies");
    let options = run_options(dir.path());
    let task = onboarding_task(&options, None).expect("the ready home mounts the flow");
    assert!(
        (task.model_ready)(),
        "the configured default model is ready (the question flow)"
    );

    // Explicit flags that resolve to a provider without configured
    // auth mount the task too (TS `shouldRunOnboarding`: the flag
    // alone), carrying the not-ready branch -- the full sign-in flow,
    // not the question. TS `validateConfig` requires an "apiKey" for
    // custom providers, but a `!command` key that fails resolves to
    // nothing (TS `resolveConfigValue`), so the provider stays
    // unauthenticated.
    let mut options = run_options(dir.path());
    options.config.provider = Some("onboard-naked".into());
    options.config.model = Some("m2".into());
    let task = onboarding_task(&options, None).expect("the flag alone mounts the flow");
    assert!(
        !(task.model_ready)(),
        "the naked provider leaves the model not ready (the full flow)"
    );
    assert!(
        task.current_model
            .as_ref()
            .is_some_and(|model| model.id == "m2"),
        "the resolved startup model rides the task (TS getCurrentModel)"
    );
}

/// The product sink's persistence over the real settings files: a fresh
/// home reads its missing flag through a fresh manager, and the
/// completion persists the flag the next launch's gate reads.
#[test]
fn settings_sink_persists_the_completion_flag() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    let sink = SettingsOnboardingSink {
        cwd: dir.path().to_path_buf(),
        agent_dir: agent_dir.clone(),
    };
    assert!(
        !sink.onboarding_shown(),
        "a fresh home has no completion flag yet"
    );
    sink.mark_onboarding_complete()
        .expect("complete onboarding");

    let settings = eukhe_core::settings::SettingsManager::create(dir.path(), &agent_dir);
    assert!(
        settings.get_onboarding_shown(),
        "the flow marked onboarding shown"
    );
}

/// `/resume <selector>` leaves a session run for the session it names (TS
/// switches in place): the request is followed whether or not the run
/// returns to the agents view, so the process never ends on it with a
/// resume hint. Agents-back opens the view; any other exit ends the run.
#[test]
fn a_resume_selection_opens_that_session_before_the_view_or_the_exit() {
    let selection = SessionSelection::Attach("01a1bda2-4a03-74ef-a56e-e1c160c4eb0d".to_owned());
    let mut outcome = eukhe_tui::interactive::InteractiveOutcome {
        selection_request: Some(selection.clone()),
        ..Default::default()
    };
    assert_eq!(after_session(&mut outcome), AfterSession::Open(selection));
    assert_eq!(
        after_session(&mut outcome),
        AfterSession::Exit,
        "the request is taken once"
    );
    outcome.return_to_agents_view = true;
    assert_eq!(after_session(&mut outcome), AfterSession::AgentsView);
}

#[test]
fn build_tui_options_reads_code_block_indent_settings() {
    // `markdown.codeBlockIndent` rides InteractiveOptions at startup
    // (TS `getCodeBlockIndent` -> `getMarkdownThemeWithSettings`); a
    // non-default value reaches the TUI, and no setting keeps the TS
    // default two spaces.
    fn run_options(dir: &std::path::Path) -> RunOptions {
        RunOptions {
            app_mode: crate::mode::AppMode::Interactive,
            config: crate::mode::RuntimeConfig {
                cwd: dir.to_path_buf(),
                agent_dir: dir.join("agent"),
                ..Default::default()
            },
            session: crate::mode::SessionOptions::default(),
            messages: Vec::new(),
            file_args: Vec::new(),
            daemon_socket: None,
            list_models: None,
            initial_message: None,
            initial_images: Vec::new(),
            verbose: false,
            offline: false,
            agents_view_requested: false,
            attach_agent: None,
        }
    }

    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent = dir.path().join("agent");
    std::fs::create_dir_all(&agent).expect("agent dir");
    std::fs::write(
        agent.join("settings.json"),
        r#"{ "markdown": { "codeBlockIndent": "    " } }"#,
    )
    .expect("settings.json");
    let options = build_tui_options(
        &run_options(dir.path()),
        dir.path().join("d.sock"),
        std::sync::Arc::default(),
    )
    .expect("options");
    assert_eq!(options.code_block_indent, "    ");

    // No markdown settings: the TS default.
    let bare = tempfile::TempDir::new().expect("temp dir");
    std::fs::create_dir_all(bare.path().join("agent")).expect("agent dir");
    let options = build_tui_options(
        &run_options(bare.path()),
        bare.path().join("d.sock"),
        std::sync::Arc::default(),
    )
    .expect("options");
    assert_eq!(options.code_block_indent, "  ");
}

/// A legacy session with one user/assistant exchange, written as the
/// JSONL rows a real run produced. Returns the file and its session id.
fn seed_session(
    session_dir: &std::path::Path,
    cwd: &std::path::Path,
    user_text: &str,
) -> (std::path::PathBuf, String) {
    let id = uuid::Uuid::now_v7().to_string();
    let at = "2026-01-01T00:00:00.000Z";
    let lines = [
        serde_json::json!({"type": "session", "version": 3, "id": id, "timestamp": at,
            "cwd": cwd.display().to_string()}),
        // The block shape a real run writes (the print runtime's
        // `content[0].text` rows), so the copy assertions read the same
        // shape the shipped sessions carry.
        serde_json::json!({"type": "message", "id": "u0", "parentId": null, "timestamp": at,
            "message": {"role": "user", "content": [{"type": "text", "text": user_text}],
                "timestamp": 0}}),
        serde_json::json!({"type": "message", "id": "a0", "parentId": "u0", "timestamp": at,
            "message": {"role": "assistant", "content": [{"type": "text", "text": "the answer"}],
                "api": "openai-completions", "provider": "openai", "model": "gpt-x",
                "usage": {"input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0,
                    "totalTokens": 0, "cost": {"input": 0, "output": 0, "cacheRead": 0,
                    "cacheWrite": 0, "total": 0}},
                "stopReason": "stop", "timestamp": 0}}),
    ];
    std::fs::create_dir_all(session_dir).expect("sessions dir");
    let path = session_dir.join(format!("{id}.jsonl"));
    let mut body = String::new();
    for line in &lines {
        body.push_str(&line.to_string());
        body.push('\n');
    }
    std::fs::write(&path, body).expect("write session file");
    (path, id)
}

/// Whether any file directly under the storage `dir` carries `needle`
/// (the forked conversation's rows land in the storage's JSONL files).
fn storage_contains(dir: &std::path::Path, needle: &str) -> bool {
    std::fs::read_dir(dir)
        .expect("read storage dir")
        .map(|entry| entry.expect("storage entry").path())
        .filter(|path| path.is_file())
        .any(|path| std::fs::read_to_string(path).is_ok_and(|text| text.contains(needle)))
}

fn fork_options(cwd: &std::path::Path, session_dir: &std::path::Path) -> RunOptions {
    let mut options = run_options_for_continue(cwd);
    options.session.session_dir = Some(session_dir.to_path_buf());
    options
}

fn fork(options: &RunOptions, selector: &str) -> std::path::PathBuf {
    let selection = fork_startup_selection(options, selector).expect("fork startup");
    let SessionSelection::Resume(fork) = selection else {
        panic!("the fork opens as a resume of the fork storage, got {selection:?}");
    };
    fork
}

#[test]
fn fork_startup_selection_copies_the_source_into_a_fresh_storage() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let cwd = dir.path().join("project");
    let session_dir = dir.path().join("sessions");
    std::fs::create_dir_all(&cwd).expect("cwd");
    std::fs::create_dir_all(&session_dir).expect("sessions dir");
    let (source, id) = seed_session(&session_dir, &cwd, "original question");
    let before = std::fs::read(&source).expect("read source");

    let fork = fork(&fork_options(&cwd, &session_dir), &id);

    assert!(fork.is_dir(), "the fork storage landed on disk");
    assert_eq!(fork.parent(), Some(session_dir.as_path()));
    assert_ne!(
        fork.file_name().and_then(|name| name.to_str()),
        Some(id.as_str()),
        "the fork is a new session"
    );
    assert!(storage_contains(&fork, "original question"));
    assert!(storage_contains(&fork, "the answer"));
    let after = std::fs::read(&source).expect("read source");
    assert_eq!(before, after, "the source file is unchanged");
}

#[test]
fn fork_startup_selection_imports_a_global_session_into_this_cwd() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let other_project = dir.path().join("other-project");
    let this_project = dir.path().join("this-project");
    let session_dir = dir.path().join("sessions");
    std::fs::create_dir_all(&other_project).expect("other project");
    std::fs::create_dir_all(&this_project).expect("this project");
    std::fs::create_dir_all(&session_dir).expect("sessions dir");
    let (source, id) = seed_session(&session_dir, &other_project, "global question");
    let before = std::fs::read(&source).expect("read source");

    let fork = fork(&fork_options(&this_project, &session_dir), &id);

    assert!(storage_contains(&fork, "global question"));
    assert!(
        storage_contains(&fork, &this_project.display().to_string()),
        "the fork adopts the TARGET cwd"
    );
    let after = std::fs::read(&source).expect("read source");
    assert_eq!(before, after, "the source file is unchanged");
}

#[test]
fn fork_startup_selection_reports_the_ts_contracts() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let cwd = dir.path().join("project");
    let session_dir = dir.path().join("sessions");
    std::fs::create_dir_all(&cwd).expect("cwd");
    std::fs::create_dir_all(&session_dir).expect("sessions dir");
    let options = fork_options(&cwd, &session_dir);

    // An empty source file: the `forkFrom` failure contract.
    let empty = session_dir.join("empty.jsonl");
    std::fs::write(&empty, "").expect("write empty file");
    let error = fork_startup_selection(&options, empty.to_str().expect("utf8 path"))
        .expect_err("an empty source cannot fork");
    assert!(
        error.to_string().contains(&format!(
            "Cannot fork: source session file is empty or invalid: {}",
            empty.display()
        )),
        "unexpected error: {error:#}"
    );

    // An unknown selector: the TS startup failure with the browse hint.
    let error = fork_startup_selection(&options, "does-not-exist")
        .expect_err("an unknown selector cannot fork");
    let rendered = format!("{error:#}");
    assert!(
        rendered.contains("No session found matching 'does-not-exist'"),
        "unexpected error: {rendered}"
    );
    assert!(
        rendered.contains("Open eukhe and press left-arrow to browse sessions."),
        "unexpected error: {rendered}"
    );
}

// The tilde selector expands a unix HOME path.
#[test]
fn fork_startup_selection_expands_a_tilde_selector() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let home = dir.path().join("home");
    let project = dir.path().join("project");
    let session_dir = dir.path().join("sessions");
    std::fs::create_dir_all(&home).expect("home");
    std::fs::create_dir_all(&project).expect("project");
    std::fs::create_dir_all(&session_dir).expect("sessions dir");
    let (source, id) = seed_session(&session_dir, &project, "tilde question");
    let home_sessions = home.join("sessions");
    std::fs::create_dir_all(&home_sessions).expect("home sessions dir");
    let home_file = home_sessions.join(format!("{id}.jsonl"));
    std::fs::rename(&source, &home_file).expect("move the source under home");
    let _env = crate::config::env_lock();
    let previous_home = std::env::var("HOME").ok();
    std::env::set_var("HOME", &home);
    let selector = format!("~/sessions/{id}.jsonl");
    let selection = fork_startup_selection(&fork_options(&project, &session_dir), &selector);
    match previous_home {
        Some(value) => std::env::set_var("HOME", value),
        None => std::env::remove_var("HOME"),
    }
    let SessionSelection::Resume(fork) = selection.expect("the tilde selector forks") else {
        panic!("the fork opens as a resume of the fork storage");
    };
    assert_eq!(
        fork.parent(),
        Some(session_dir.as_path()),
        "the fork lands in the requested session dir"
    );
    assert!(storage_contains(&fork, "tilde question"));
}

#[test]
fn fork_startup_selection_rejects_a_fifo_source_without_hanging() {
    // A FIFO with no writer blocks a read forever; the launch must error
    // instead.
    let dir = tempfile::TempDir::new().expect("temp dir");
    let project = dir.path().join("project");
    let session_dir = dir.path().join("sessions");
    std::fs::create_dir_all(&project).expect("project");
    std::fs::create_dir_all(&session_dir).expect("sessions dir");
    let fifo = session_dir.join("pipe.jsonl");
    nix::unistd::mkfifo(&fifo, nix::sys::stat::Mode::S_IRWXU).expect("mkfifo");
    let error = fork_startup_selection(
        &fork_options(&project, &session_dir),
        fifo.to_str().expect("utf8 path"),
    )
    .expect_err("a FIFO source cannot fork");
    assert!(
        error.to_string().contains(&format!(
            "Cannot fork: source session file is not a regular file: {}",
            fifo.display()
        )),
        "unexpected error: {error:#}"
    );
}

#[test]
fn build_tui_options_opens_a_fork_as_the_startup_session() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let cwd = dir.path().join("project");
    let session_dir = dir.path().join("sessions");
    std::fs::create_dir_all(&cwd).expect("cwd");
    std::fs::create_dir_all(&session_dir).expect("sessions dir");
    let (_, id) = seed_session(&session_dir, &cwd, "interactive question");

    let mut options = run_options_for_continue(dir.path());
    options.config.cwd = cwd;
    options.config.agent_dir = dir.path().join("agent");
    options.session.fork = Some(id);
    options.session.session_dir = Some(session_dir.clone());
    let tui = build_tui_options(
        &options,
        dir.path().join("d.sock"),
        std::sync::Arc::default(),
    )
    .expect("the interactive launch forks instead of refusing");

    let SessionSelection::Resume(fork) = &tui.session else {
        panic!(
            "the fork opens as a resume of the fork storage, got {:?}",
            tui.session
        );
    };
    assert_eq!(
        fork.parent(),
        Some(session_dir.as_path()),
        "the fork honors --session-dir"
    );
    assert!(storage_contains(fork, "interactive question"));
}

#[test]
fn a_fork_launch_never_opens_the_agents_view() {
    // TS `shouldOpenAgentsViewForDaemonInteractive`: `--fork` opens its
    // target directly -- even alongside an explicit `agents` request.
    let mut options = run_options_for_continue(std::path::Path::new("/does/not/matter"));
    options.agents_view_requested = true;
    assert!(
        should_open_agents_view(&options, /*onboarding_pending*/ false),
        "an explicit agents request still opens the view"
    );
    options.session.resume_bare = true;
    assert!(
        should_open_agents_view(&options, /*onboarding_pending*/ false),
        "a bare --resume still opens the view"
    );
    options.session.resume_bare = false;
    options.session.fork = Some("source".to_string());
    assert!(
        !should_open_agents_view(&options, /*onboarding_pending*/ false),
        "a fork opens its target, never the agents view"
    );
    options.session.fork = None;
    options.agents_view_requested = false;
    options.session.continue_recent = true;
    assert!(
        !should_open_agents_view(&options, /*onboarding_pending*/ false),
        "--continue opens its session, never the agents view"
    );
}
