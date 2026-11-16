//! Changing models mid-session in the TUI: the `/model` picker (daemon
//! `set_model`) moves the session from Anthropic Messages to `OpenAI`
//! Responses, the cycle key (daemon `cycle_model` within the scoped
//! models) moves it back, and each segment runs a `bash` tool call and
//! its result against a loopback provider serving both APIs. Every
//! request is held to its API's rules, at the session's thinking level.

use super::*;

#[path = "../support/provider_mock.rs"]
mod provider_mock;

use provider_mock::{replay, switched_session_replays, ProviderMock, Replay};

fn settle(text: &str) -> eukhe_tui::interactive::HeadlessStep {
    eukhe_tui::interactive::HeadlessStep::SubmitAndSettle {
        text: text.to_string(),
        timeout_ms: 60_000,
    }
}

fn wait_render(needle: &str) -> eukhe_tui::interactive::HeadlessStep {
    eukhe_tui::interactive::HeadlessStep::WaitRender {
        needle: needle.to_string(),
        timeout_ms: 30_000,
    }
}

#[tokio::test]
async fn tui_model_picker_and_cycle_key_switch_api_with_tool_calls() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let mock = ProviderMock::start();
    std::fs::write(
        agent_dir.join("models.json"),
        mock.models_json().to_string(),
    )
    .expect("write models.json");
    // The cycle key steps through this scope.
    std::fs::write(
        agent_dir.join("settings.json"),
        serde_json::json!({
            "enabledModels": ["mock-anthropic/claude-mock", "mock-openai/gpt-mock"],
        })
        .to_string(),
    )
    .expect("write settings.json");
    let supervisor = spawn_supervisor(dir.path());
    let auth = eukhe_core::auth::AuthStorage::in_memory_without_env(
        &eukhe_core::auth::AuthStorageData::default(),
        std::sync::Arc::new(eukhe_core::auth::NoOAuth),
    );
    let registry = eukhe_core::models::ModelRegistry::create(auth, agent_dir.join("models.json"));
    let catalog: Vec<eukhe_types::ai::CatalogModel> = registry
        .get_available()
        .into_iter()
        .map(|model| eukhe_types::ai::CatalogModel {
            thinking_levels: eukhe_ai::models::registry_thinking_levels(model),
            service_tiers: eukhe_ai::quirks::service_tiers(model.into()),
            account: eukhe_types::ai::AccountOffer::NotRefreshed,
            model: model.clone(),
        })
        .collect();

    let mut options = base_options(&supervisor, dir.path(), &session_dir);
    options.script_path = None;
    options.model_catalog = catalog;
    options.model_selection = eukhe_tui::interactive::ModelSelection {
        provider: Some("mock-anthropic".to_string()),
        model: Some("claude-mock".to_string()),
        api_key: None,
        thinking: Some(eukhe_types::ai::ModelThinkingLevel::Low),
    };
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            settle("List the files."),
            eukhe_tui::interactive::HeadlessStep::Submit("/model chat".to_string()),
            wait_render("Search models"),
            eukhe_tui::interactive::HeadlessStep::Type("gpt-mock".to_string()),
            eukhe_tui::interactive::HeadlessStep::Type("\n".to_string()),
            wait_render("Model: gpt-mock"),
            // The pick returns to the role hub; Esc closes it.
            wait_render("Search roles"),
            eukhe_tui::interactive::HeadlessStep::Key(crossterm::event::KeyEvent::new(
                crossterm::event::KeyCode::Esc,
                crossterm::event::KeyModifiers::NONE,
            )),
            settle("List them again."),
            eukhe_tui::interactive::HeadlessStep::Key(crossterm::event::KeyEvent::new(
                crossterm::event::KeyCode::Char('m'),
                crossterm::event::KeyModifiers::ALT,
            )),
            wait_render("Model: mock-anthropic/claude-mock"),
            settle("Once more."),
        ],
        width: 120,
        height: 36,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");

    assert_eq!(
        mock.log().iter().map(replay).collect::<Vec<Replay>>(),
        switched_session_replays(),
        "frames:\n{}",
        outcome.frames.join("\n")
    );
    drop(supervisor);
}
