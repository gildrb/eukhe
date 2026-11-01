//! The saved chat model through the role table: the choices the previous
//! version wrote survive an update, `modelRoles.all` keeps the chat model
//! when `settings.json` loses `defaultProvider`/`defaultModel`, and a saved
//! model the catalog lacks names its setting without a settings write.

use std::path::PathBuf;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_types::cvar::Command;

use super::tests::offline_models;
use super::*;
use crate::models::roles::{role_table, RoleModel};
use crate::settings::Persisted;

/// Two battery models with a configured key.
const BATTERY: &str = r#"{ "providers": { "battery": {
    "baseUrl": "http://127.0.0.1:9/v1", "apiKey": "battery-key", "api": "openai-completions",
    "models": [ { "id": "mock-reason", "reasoning": true }, { "id": "mock-plain" } ]
} } }"#;

/// A catalog unlike the one the choices were saved under: a new battery
/// model listed first, the startup model when nothing is saved.
const UPDATED: &str = r#"{ "providers": { "battery": {
    "baseUrl": "http://127.0.0.1:9/v1", "apiKey": "battery-key", "api": "openai-completions",
    "models": [ { "id": "mock-new" }, { "id": "mock-reason", "reasoning": true }, { "id": "mock-plain" } ]
} } }"#;

/// An agent dir under a temporary home, with a models.json, and a working
/// directory outside it.
struct Home {
    _dir: tempfile::TempDir,
    cwd: PathBuf,
    agent: PathBuf,
}

impl Home {
    fn new(models_json: &str) -> Self {
        let dir = tempfile::tempdir().unwrap();
        let cwd = dir.path().join("work");
        let agent = dir.path().join("home").join(".eukhe");
        std::fs::create_dir_all(&cwd).unwrap();
        std::fs::create_dir_all(&agent).unwrap();
        std::fs::write(agent.join("models.json"), models_json).unwrap();
        Self {
            _dir: dir,
            cwd,
            agent,
        }
    }

    fn settings(&self) -> SettingsManager {
        SettingsManager::create(&self.cwd, &self.agent)
    }

    /// `set <id> <value>` in the global config.cfg (the `/model` hub's and
    /// the daemon's write).
    fn set_global(&self, id: &str, value: &str) {
        self.settings()
            .run_global(&[Command::Set {
                id: id.to_owned(),
                value: value.to_owned(),
            }])
            .unwrap();
    }

    /// The bytes of the global settings files (`None`: absent).
    fn files(&self) -> [Option<Vec<u8>>; 2] {
        let read = |name: &str| std::fs::read(self.agent.join(name)).ok();
        [read("settings.json"), read("config.cfg")]
    }

    async fn open(&self) -> OpenModel {
        let models = offline_models(&self.agent).models;
        resolve_open_model(&models, &self.settings(), None, None, &BACKGROUND_CONTEXT)
            .await
            .unwrap()
    }

    /// The resolved model and every role's model of these settings.
    async fn resolved_roles(&self) -> (Option<ResolvedModel>, Vec<RoleModel>) {
        let models = offline_models(&self.agent).models;
        let settings = self.settings();
        let resolved = resolve_session_model(&models, &settings, None, None, &BACKGROUND_CONTEXT)
            .await
            .unwrap();
        (resolved, role_table(settings.cvars()))
    }
}

fn model_ref(provider: &str, model_id: &str) -> ModelRef {
    ModelRef {
        provider: provider.to_owned(),
        model_id: model_id.to_owned(),
    }
}

fn row(role: ModelRole, source: RoleSource, selector: Option<&str>) -> RoleModel {
    RoleModel {
        role,
        source,
        selector: selector.map(str::to_owned),
    }
}

/// Regression ("every update resets my model"): the choices the previous
/// version saved (the `/model` switch's `defaultProvider`/`defaultModel`,
/// the hub's role settings in config.cfg) resolve to the same models after
/// an update whose catalog would pick another model with nothing saved.
/// With `settings.json` rewritten without the default model (the old Home
/// Manager activation), `modelRoles.all` keeps the chat model.
#[tokio::test]
async fn saved_choices_survive_an_update_and_a_settings_json_rewrite() {
    let home = Home::new(BATTERY);
    assert_eq!(
        home.settings()
            .set_default_model_and_provider("battery", "mock-reason")
            .unwrap(),
        Persisted::Applies
    );
    home.set_global("memory.model", "battery/mock-plain");
    home.set_global("auxiliaryModel", "battery/mock-plain");
    home.set_global("modelRoles.judge", "local/lfm2.5-230m");

    std::fs::write(home.agent.join("models.json"), UPDATED).unwrap();
    let models = offline_models(&home.agent).models;
    let nothing_saved = resolve_session_model(
        &models,
        &SettingsManager::create(&home.cwd, home.agent.join("empty")),
        None,
        None,
        &BACKGROUND_CONTEXT,
    )
    .await
    .unwrap()
    .map(|resolved| resolved.model);
    assert_eq!(nothing_saved, Some(model_ref("battery", "mock-new")));

    let chat = ResolvedModel {
        model: model_ref("battery", "mock-reason"),
        thinking: ModelThinkingLevel::Medium,
        substituted: None,
    };
    let roles = |chat_source, chat_selector, rest: RoleSource, all: Option<&str>| {
        vec![
            row(ModelRole::Chat, chat_source, chat_selector),
            row(
                ModelRole::Memory,
                RoleSource::Own,
                Some("battery/mock-plain"),
            ),
            row(
                ModelRole::Auxiliary,
                RoleSource::Own,
                Some("battery/mock-plain"),
            ),
            row(ModelRole::Image, rest, all),
            row(ModelRole::Subagent, rest, all),
            row(ModelRole::Gateway, rest, all),
            row(ModelRole::Query, rest, all),
            row(ModelRole::Titles, rest, all),
            row(ModelRole::Judge, RoleSource::Own, Some("local/lfm2.5-230m")),
            row(ModelRole::Translate, rest, all),
            row(ModelRole::Speech, RoleSource::Default, None),
            row(ModelRole::Dictation, RoleSource::Default, None),
        ]
    };
    assert_eq!(
        home.resolved_roles().await,
        (
            Some(chat.clone()),
            roles(
                RoleSource::Own,
                Some("battery/mock-reason"),
                RoleSource::Default,
                None
            )
        )
    );

    // The chat default lives in config.cfg now: a settings.json rewrite
    // (the old Home Manager activation) leaves it, and the other roles
    // run on `modelRoles.all`.
    home.set_global("modelRoles.all", "battery/mock-reason");
    std::fs::write(home.agent.join("settings.json"), "{}").unwrap();
    let all = Some("battery/mock-reason");
    assert_eq!(
        home.resolved_roles().await,
        (
            Some(chat),
            roles(RoleSource::Own, all, RoleSource::All, all)
        )
    );
}

/// A saved chat model the catalog lacks (from `defaultModel`, or from
/// `modelRoles.all` with or without a provider) gives the next startup
/// model with a notice that names the model and its setting; a saved
/// model without credentials leaves the session without a model, and the
/// fix names its setting. The resolution writes no settings file.
#[tokio::test]
async fn a_missing_saved_model_names_its_setting_and_writes_nothing() {
    let saved_default = Home::new(BATTERY);
    assert_eq!(
        saved_default
            .settings()
            .set_default_model_and_provider("battery", "gone")
            .unwrap(),
        Persisted::Applies
    );
    let all_gone = Home::new(BATTERY);
    all_gone.set_global("modelRoles.all", "battery/gone");
    let all_bare = Home::new(BATTERY);
    all_bare.set_global("modelRoles.all", "gone");
    let anthropic = eukhe_ai::providers::all::get_builtin_models("anthropic").remove(0);
    let all_unkeyed = Home::new(BATTERY);
    all_unkeyed.set_global("modelRoles.all", &format!("anthropic/{}", anthropic.id));

    let mut notices = Vec::new();
    let mut unchanged = Vec::new();
    for home in [&saved_default, &all_gone, &all_bare, &all_unkeyed] {
        let before = home.files();
        notices.push(home.open().await.notice());
        unchanged.push(home.files() == before);
    }
    let runs_on = "the model catalog does not have it. The session runs on battery/mock-reason.";
    assert_eq!(
        (notices, unchanged),
        (
            vec![
                Some(format!(
                    "The saved default model battery/gone did not run: {runs_on}"
                )),
                Some(format!(
                    "The all-roles model battery/gone (modelRoles.all) did not run: {runs_on}"
                )),
                Some(format!(
                    "The all-roles model gone (modelRoles.all) did not run: {runs_on}"
                )),
                Some(format!(
                    "The all-roles model anthropic/{} (modelRoles.all) did not run: its provider has no credentials. eukhe does not move to another provider. Sign in with /login, set the provider's API key, or change modelRoles.all. The session has no model.",
                    anthropic.id
                )),
            ],
            vec![true; 4]
        )
    );
}
