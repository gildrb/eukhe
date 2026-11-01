//! One store per setting, over the user's own files (`tests/fixtures/
//! user_home`: the `settings.json` and `config.cfg` of the v0.10.61
//! reports). A setting the UI writes goes to the global `config.cfg`, so
//! it is the value a read gives back and no settings row says otherwise;
//! `eukhe` run from the home directory reads `~/.eukhe` once, as the
//! global scope.

use std::path::{Path, PathBuf};

use super::cvar::table;
use super::{Persisted, SettingsManager, SettingsScope, ThinkingLevelSetting};
use crate::models::roles::{
    all_roles_overrides, all_roles_reach, own_decl, role_table, RoleModel, RoleSource,
};
use eukhe_types::model_roles::ModelRole;

const USER_SETTINGS: &str = include_str!("../../tests/fixtures/user_home/settings.json");
const USER_CONFIG: &str = include_str!("../../tests/fixtures/user_home/config.cfg");

/// A home with the user's `~/.eukhe` files and a project directory.
struct Home {
    _dir: tempfile::TempDir,
    root: PathBuf,
    agent: PathBuf,
}

impl Home {
    fn new() -> Self {
        let dir = tempfile::tempdir().unwrap();
        let home = dir.path().join("home");
        let agent = home.join(".eukhe");
        std::fs::create_dir_all(&agent).unwrap();
        std::fs::create_dir_all(home.join("work")).unwrap();
        std::fs::write(agent.join("settings.json"), USER_SETTINGS).unwrap();
        std::fs::write(agent.join("config.cfg"), USER_CONFIG).unwrap();
        Self {
            _dir: dir,
            root: home,
            agent,
        }
    }

    /// The settings of a session in `cwd`.
    fn settings(&self, cwd: &Path) -> SettingsManager {
        SettingsManager::create(cwd, &self.agent)
    }

    fn work(&self) -> PathBuf {
        self.root.join("work")
    }

    fn file(&self, name: &str) -> String {
        std::fs::read_to_string(self.agent.join(name)).unwrap()
    }
}

/// Regression (v0.10.61: "Thinking level: max", then "the default thinking
/// level is not saved as the default: defaultThinkingLevel is saved, but
/// ~/.eukhe/config.cfg also sets it"): the UI's write of the thinking
/// level, with the user's files, applies, reads back, and replaces the
/// config.cfg line in place; settings.json is untouched.
#[test]
fn a_thinking_level_set_in_the_ui_reads_back() {
    let home = Home::new();
    let written = home
        .settings(&home.work())
        .set_default_thinking_level(ThinkingLevelSetting::Max)
        .unwrap();
    assert_eq!(
        (
            written,
            home.settings(&home.work()).get_default_thinking_level(),
            home.file("config.cfg"),
            home.file("settings.json"),
        ),
        (
            Persisted::Applies,
            Some(ThinkingLevelSetting::Max),
            "set memory.model elpis/qwen3.8-27b\n\
             set memory.thinking low\n\
             set auxiliaryModel elpis/qwen3.8-27b\n\
             set modelRoles.tiny zai/glm-5.3-flash\n\
             set defaultThinkingLevel max\n\
             set gateway.signal.model elpis/qwen3.8-27b\n\
             set modelRoles.all anthropic/claude-fable-5\n"
                .to_owned(),
            USER_SETTINGS.to_owned(),
        )
    );
}

/// The model switch's save, with the user's files: the default model
/// goes to config.cfg and applies; the recent list stays in settings.json.
#[test]
fn a_model_switch_saves_where_reads_look() {
    let home = Home::new();
    let written = home
        .settings(&home.work())
        .set_default_model_and_provider("anthropic", "claude-opus-5-5")
        .unwrap();
    let settings = home.settings(&home.work());
    assert_eq!(
        (
            written,
            settings.cvars().optional_text(&table::DEFAULT_PROVIDER),
            settings.cvars().optional_text(&table::DEFAULT_MODEL),
            settings.get_recent_models(),
        ),
        (
            Persisted::Applies,
            Some("anthropic".to_owned()),
            Some("claude-opus-5-5".to_owned()),
            vec![
                "anthropic/claude-opus-5-5".to_owned(),
                "anthropic/claude-fable-5".to_owned(),
                "elpis/qwen3.8-27b".to_owned(),
            ],
        )
    );
}

/// Regression (sessions run from `~`: "the default model is not saved as
/// the default", "memory.model is a Global cvar"): with the home directory
/// as the session's directory, `~/.eukhe` is the global scope once: no
/// settings error, every write applies, and the role sources are global.
#[test]
fn a_session_in_the_home_directory_reads_the_agent_dir_once() {
    let home = Home::new();
    let mut settings = home.settings(&home.root);
    assert_eq!(settings.errors(), []);
    assert_eq!(
        (
            settings
                .set_default_model_and_provider("anthropic", "claude-fable-5")
                .unwrap(),
            settings
                .set_default_thinking_level(ThinkingLevelSetting::High)
                .unwrap(),
            settings.config_scope(&table::MEMORY_MODEL),
            settings.config_scope(&table::DEFAULT_MODEL),
            settings.errors().to_vec(),
        ),
        (
            Persisted::Applies,
            Persisted::Applies,
            Some(SettingsScope::Global),
            Some(SettingsScope::Global),
            Vec::new(),
        )
    );
}

/// `/model --all anthropic/claude-fable-5` with the user's files (the
/// switch saves the chat default, then the all-roles model clears every
/// role's own global setting): the whole role table runs on the model, but
/// speech and dictation (local audio, never on the all-roles model); no
/// project setting keeps a role elsewhere. Only the role settings leave
/// the files.
#[test]
fn model_all_runs_every_llm_role_on_the_model() {
    let home = Home::new();
    let selector = "anthropic/claude-fable-5";
    let mut settings = home.settings(&home.work());
    assert_eq!(
        settings
            .set_default_model_and_provider("anthropic", "claude-fable-5")
            .unwrap(),
        Persisted::Applies
    );
    let cleared: Vec<_> = all_roles_reach().into_iter().filter_map(own_decl).collect();
    settings.save_all_roles_model(selector, &cleared).unwrap();

    let settings = home.settings(&home.work());
    let row = |role, source, selector: Option<&str>| RoleModel {
        role,
        source,
        selector: selector.map(str::to_owned),
    };
    let mut expected_settings: serde_json::Value = serde_json::from_str(USER_SETTINGS).unwrap();
    expected_settings["memory"]
        .as_object_mut()
        .unwrap()
        .remove("model");
    expected_settings["gateway"]["signal"]
        .as_object_mut()
        .unwrap()
        .remove("model");
    assert_eq!(
        (
            role_table(settings.cvars()),
            all_roles_overrides(&settings, selector),
            home.file("config.cfg"),
            serde_json::from_str::<serde_json::Value>(&home.file("settings.json")).unwrap(),
        ),
        (
            vec![
                row(ModelRole::Chat, RoleSource::Own, Some(selector)),
                row(ModelRole::Memory, RoleSource::All, Some(selector)),
                row(ModelRole::Auxiliary, RoleSource::All, Some(selector)),
                row(ModelRole::Image, RoleSource::All, Some(selector)),
                row(ModelRole::Subagent, RoleSource::All, Some(selector)),
                row(ModelRole::Gateway, RoleSource::All, Some(selector)),
                row(ModelRole::Query, RoleSource::All, Some(selector)),
                row(ModelRole::Titles, RoleSource::All, Some(selector)),
                row(ModelRole::Judge, RoleSource::All, Some(selector)),
                row(ModelRole::Translate, RoleSource::All, Some(selector)),
                row(ModelRole::Speech, RoleSource::Default, None),
                row(ModelRole::Dictation, RoleSource::Default, None),
            ],
            Vec::new(),
            "set memory.thinking low\n\
             set defaultThinkingLevel xhigh\n\
             set modelRoles.all anthropic/claude-fable-5\n\
             set defaultProvider anthropic\n\
             set defaultModel claude-fable-5\n"
                .to_owned(),
            expected_settings,
        )
    );
}

/// After `/model --all`, a project's own setting of a role still wins
/// there; the overrides name the role, its model, the setting and the
/// project file. A later choice of one role sets that role alone.
#[test]
fn model_all_names_what_a_project_keeps_and_a_role_can_differ_again() {
    let home = Home::new();
    let project = home.work().join(".eukhe");
    std::fs::create_dir_all(&project).unwrap();
    std::fs::write(
        project.join("config.cfg"),
        "set auxiliaryModel zai/glm-5.3\n",
    )
    .unwrap();
    let selector = "anthropic/claude-fable-5";
    let cleared: Vec<_> = all_roles_reach().into_iter().filter_map(own_decl).collect();
    home.settings(&home.work())
        .save_all_roles_model(selector, &cleared)
        .unwrap();
    let overrides = all_roles_overrides(&home.settings(&home.work()), selector);
    let mut settings = home.settings(&home.work());
    settings
        .run_global(&eukhe_types::cvar::parse_list("set memory.model zai/glm-5.3-flash").unwrap())
        .unwrap();
    assert_eq!(
        (
            overrides,
            all_roles_overrides(&home.settings(&home.work()), selector)
                .into_iter()
                .map(|kept| (kept.role, kept.selector))
                .collect::<Vec<_>>(),
        ),
        (
            vec![crate::models::roles::AllRolesOverride {
                role: ModelRole::Auxiliary,
                selector: "zai/glm-5.3".to_owned(),
                setting: "auxiliaryModel",
                file: project.join("config.cfg").display().to_string(),
            }],
            vec![
                (ModelRole::Memory, "zai/glm-5.3-flash".to_owned()),
                (ModelRole::Auxiliary, "zai/glm-5.3".to_owned()),
            ],
        )
    );
}

/// A setting eukhe keeps as a document (here `packages`) is never set by
/// a cfg file: its readers read settings.json alone.
#[test]
fn a_cfg_file_never_sets_a_document_setting() {
    let home = Home::new();
    std::fs::write(
        home.agent.join("config.cfg"),
        format!("{USER_CONFIG}\nset packages []\n"),
    )
    .unwrap();
    let settings = home.settings(&home.work());
    assert_eq!(
        settings
            .errors()
            .iter()
            .map(|error| error.message.clone())
            .collect::<Vec<_>>(),
        ["config.cfg: `packages` is kept in settings.json only: a cfg file or `/set` cannot set it"]
    );
}
