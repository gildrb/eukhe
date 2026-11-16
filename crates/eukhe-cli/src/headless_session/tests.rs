use eukhe_chord::context::BACKGROUND_CONTEXT;

use super::*;
use crate::mode::{AppMode, RuntimeConfig, SessionOptions};

fn run_options(dir: &Path) -> RunOptions {
    RunOptions {
        app_mode: AppMode::Print,
        config: RuntimeConfig {
            cwd: dir.to_path_buf(),
            agent_dir: dir.join("agent"),
            ..RuntimeConfig::default()
        },
        session: SessionOptions::default(),
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

/// A fresh session whose runtime lease cannot be acquired (the lease root
/// is a regular file) fails closed: the open answers the lease error and
/// nothing is written under the sessions directory.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn fresh_session_without_a_lease_fails_closed() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let options = run_options(dir.path());
    std::fs::create_dir_all(&options.config.agent_dir).expect("agent dir");
    std::fs::write(options.config.agent_dir.join("session-leases"), "")
        .expect("block the lease root");

    let Err(error) = open_headless_session(
        &options,
        HeadlessTarget::New { cwd: None },
        &BACKGROUND_CONTEXT,
    )
    .await
    else {
        panic!("a fresh session must not open without its lease");
    };

    assert!(
        matches!(error, HeadlessSessionError::FreshLease { .. })
            && error
                .to_string()
                .starts_with("could not lease the fresh session "),
        "unexpected: {error}"
    );
    assert!(
        !sessions_dir(&options).exists(),
        "the session storage was written without a lease"
    );
}

/// `--budget-*` in a headless run: the session the run starts has the
/// limits as its budget before any prompt is sent.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn the_started_session_gets_the_budget_of_the_flags() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let limits = eukhe_types::budget::BudgetLimits {
        tokens: Some(200_000),
        tool_calls: Some(50),
        ..Default::default()
    };
    let mut options = run_options(dir.path());
    options.session.no_session = true;
    options.config.budget = Some(limits.into());
    // A configured model, not `EUKHE_FAUX_SCRIPT`: a process-wide variable
    // would reach the other tests of a `cargo test` run (one process).
    std::fs::create_dir_all(&options.config.agent_dir).expect("agent dir");
    std::fs::write(
        options.config.agent_dir.join("models.json"),
        r#"{ "providers": { "battery": {
            "baseUrl": "http://127.0.0.1:9/v1", "apiKey": "battery-key", "api": "openai-completions",
            "models": [ { "id": "think-a" } ]
        } } }"#,
    )
    .expect("write models.json");
    options.config.provider = Some("battery".to_owned());
    options.config.model = Some("think-a".to_owned());

    let opened = open_headless_session(&options, HeadlessTarget::Selected, &BACKGROUND_CONTEXT)
        .await
        .expect("the session opens");
    let gate = opened.session.budget();
    let report = tokio::task::spawn_blocking(move || gate.report())
        .await
        .expect("the budget report");

    assert_eq!(
        report.map(|report| (report.limits, report.phase)),
        Some((limits, eukhe_types::budget::BudgetPhase::Working))
    );
}

/// `--continue --model` without `--thinking`: the continued session's
/// level carries to the new model, as a model switch in a live session
/// does.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_flagged_model_keeps_the_continued_sessions_thinking_level() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let mut options = run_options(dir.path());
    std::fs::create_dir_all(&options.config.agent_dir).expect("agent dir");
    std::fs::write(
        options.config.agent_dir.join("models.json"),
        r#"{ "providers": { "battery": {
            "baseUrl": "http://127.0.0.1:9/v1", "apiKey": "battery-key", "api": "openai-completions",
            "models": [ { "id": "think-a", "reasoning": true }, { "id": "think-b", "reasoning": true } ]
        } } }"#,
    )
    .expect("write models.json");
    options.session.no_session = true;
    options.config.provider = Some("battery".to_owned());
    options.config.model = Some("think-a".to_owned());
    options.config.thinking = Some(eukhe_types::ai::ModelThinkingLevel::Low);
    let opened = open_headless_session(&options, HeadlessTarget::Selected, &BACKGROUND_CONTEXT)
        .await
        .expect("the session opens");

    options.config.model = Some("think-b".to_owned());
    options.config.thinking = None;
    apply_flag_model(&options, &opened.session, &BACKGROUND_CONTEXT)
        .await
        .expect("the flags apply");

    let agent = opened
        .session
        .main()
        .agent(&BACKGROUND_CONTEXT)
        .await
        .expect("the main agent");
    assert_eq!(
        (agent.model, agent.thinking_level),
        (
            Some(eukhe_durable::harness::types::ModelRef {
                provider: "battery".to_owned(),
                model_id: "think-b".to_owned(),
            }),
            eukhe_types::pi_ai::ModelThinkingLevel::Low
        )
    );
}
