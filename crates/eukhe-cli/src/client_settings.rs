//! The interactive client-settings seam implementation: every call opens
//! the file-backed settings manager over the run's directories (the store
//! is a pair of small JSON files, so the re-read is the same freshness
//! the TS manager's `reload` produces) and applies the one setting.

use anyhow::Result;
use std::path::PathBuf;
use std::sync::Arc;

use eukhe_core::agent_log::{AgentLog, AgentLogLevel};
use eukhe_core::resources::ThemePathOptions;
use eukhe_core::settings::cvar::{table, Decl};
use eukhe_core::settings::SettingsScope;
use eukhe_core::tiny::{Candidate, Pick};
use eukhe_theme::ThemeSources;
use eukhe_tiny::LOCAL_PREFIX;
use eukhe_tui::client_settings::{
    ClientSettings, LocalRoleChoices, LocalRoleModel, ModelRoleSource, ModelRoleValue,
};
use eukhe_types::cvar::Command;
use eukhe_types::model_roles::ModelRole;

/// The agent-log component theme warnings go to.
const THEME_LOG_COMPONENT: &str = "coding-agent.theme";

/// The agent-log component rejected frames go to.
const RENDER_LOG_COMPONENT: &str = "tui-render";

/// The run's theme flags (TS `additionalThemePaths`/`noThemes`).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CliThemeFlags {
    /// `--theme <path>` entries, cwd-resolved.
    pub paths: Vec<PathBuf>,
    /// `--no-themes`: the resource system's themes stay unregistered.
    pub no_themes: bool,
}

/// The seam handle the interactive run carries (TS injects the same
/// settings manager into the interactive mode).
#[derive(Clone)]
pub struct CliClientSettings {
    cwd: PathBuf,
    agent_dir: PathBuf,
    themes: CliThemeFlags,
}

impl CliClientSettings {
    pub fn new(cwd: PathBuf, agent_dir: PathBuf, themes: CliThemeFlags) -> Arc<Self> {
        Arc::new(Self {
            cwd,
            agent_dir,
            themes,
        })
    }

    fn manager(&self) -> eukhe_core::settings::SettingsManager {
        eukhe_core::settings::SettingsManager::create(&self.cwd, &self.agent_dir)
    }
}

macro_rules! setting {
    ($get:ident, $set:ident, $getter:ident, $setter:ident, $ty:ty) => {
        fn $get(&self) -> $ty {
            self.manager().$getter()
        }

        fn $set(&self, value: $ty) -> Result<()> {
            self.manager().$setter(value)?.applied()
        }
    };
}

macro_rules! str_setting {
    ($get:ident, $set:ident, $getter:ident, $setter:ident) => {
        fn $get(&self) -> String {
            self.manager().$getter().to_string()
        }

        fn $set(&self, value: &str) -> Result<()> {
            self.manager().$setter(value)?.applied()
        }
    };
}

/// Where a model role lives in the settings.
enum RoleTarget {
    /// `defaultProvider`/`defaultModel`, switched through the session.
    Chat,
    /// One selector cvar of a provider model.
    Remote(&'static Decl),
    /// A local role (`modelRoles.<role>`) and its tiny role.
    Local(eukhe_core::tiny::Role, &'static Decl),
}

/// The setting of `role` (the `/model` hub).
fn role_target(role: ModelRole) -> RoleTarget {
    use eukhe_core::tiny::Role;
    match role {
        ModelRole::Chat => RoleTarget::Chat,
        ModelRole::Memory => RoleTarget::Remote(&table::MEMORY_MODEL),
        ModelRole::Auxiliary => RoleTarget::Remote(&table::AUXILIARY_MODEL),
        ModelRole::Image => RoleTarget::Remote(&table::IMAGE_MODEL),
        ModelRole::Subagent => RoleTarget::Remote(&table::SUBAGENT_DEFAULT_MODEL),
        ModelRole::Gateway => RoleTarget::Remote(&table::GATEWAY_SIGNAL_MODEL),
        ModelRole::Titles => RoleTarget::Local(Role::Tiny, &table::MODEL_ROLE_TINY),
        ModelRole::Judge => RoleTarget::Local(Role::Judge, &table::MODEL_ROLE_JUDGE),
        ModelRole::Translate => RoleTarget::Local(Role::Translate, &table::MODEL_ROLE_TRANSLATE),
        ModelRole::Speech => RoleTarget::Local(Role::Speech, &table::MODEL_ROLE_SPEECH),
        ModelRole::Dictation => RoleTarget::Local(Role::Dictation, &table::MODEL_ROLE_DICTATION),
    }
}

impl ClientSettings for CliClientSettings {
    fn theme(&self) -> Option<String> {
        self.manager().get_theme()
    }

    fn set_theme(&self, theme: &str) -> Result<()> {
        self.manager().set_theme(theme.to_string())?.applied()
    }

    fn theme_sources(&self) -> ThemeSources {
        eukhe_core::resources::theme_sources(&ThemePathOptions {
            cwd: self.cwd.clone(),
            agent_dir: self.agent_dir.clone(),
            additional_theme_paths: self.themes.paths.clone(),
            no_themes: self.themes.no_themes,
        })
    }

    fn log_theme_warning(&self, message: &str) {
        AgentLog::new(&self.agent_dir, THEME_LOG_COMPONENT).log(
            AgentLogLevel::Warn,
            message,
            serde_json::Map::new(),
        );
    }

    fn log_render_error(&self, message: &str) {
        AgentLog::new(&self.agent_dir, RENDER_LOG_COMPONENT).log(
            AgentLogLevel::Error,
            message,
            serde_json::Map::new(),
        );
    }

    fn default_service_tier(&self) -> String {
        // The wire name of the persisted default tier (TS
        // `getDefaultServiceTier()`), "default" when unset or unreadable.
        serde_json::to_value(self.manager().get_default_service_tier())
            .ok()
            .and_then(|value| value.as_str().map(str::to_string))
            .unwrap_or_else(|| "default".to_string())
    }

    fn set_default_service_tier(&self, tier: &str) -> Result<()> {
        let parsed: eukhe_types::ai::ServiceTier =
            serde_json::from_value(serde_json::Value::String(tier.to_string()))
                .map_err(|error| anyhow::anyhow!("Invalid service tier \"{tier}\": {error}"))?;
        self.manager().set_default_service_tier(parsed)?.applied()
    }

    fn stream_pace(&self) -> eukhe_tui::pace::PaceRate {
        let manager = self.manager();
        eukhe_tui::pace::PaceRate {
            min: manager.get_stream_pace_min_chars(),
            lag: manager.get_stream_pace_lag(),
        }
    }

    fn show_speed(&self) -> bool {
        self.manager().get_show_speed()
    }

    fn pinned_agents(&self) -> eukhe_tui::agents_panel::PinnedAgents {
        eukhe_tui::agents_panel::PinnedAgents::parse(&self.manager().get_pinned_agents())
    }

    fn stuck_after_secs(&self) -> u64 {
        self.manager().get_stuck_after_secs()
    }

    setting!(
        show_images,
        set_show_images,
        get_show_images,
        set_show_images,
        bool
    );
    setting!(
        clear_on_shrink,
        set_clear_on_shrink,
        get_clear_on_shrink,
        set_clear_on_shrink,
        bool
    );
    setting!(
        show_terminal_progress,
        set_show_terminal_progress,
        get_show_terminal_progress,
        set_show_terminal_progress,
        bool
    );
    setting!(
        fullscreen,
        set_fullscreen,
        get_fullscreen,
        set_fullscreen,
        bool
    );
    setting!(
        image_auto_resize,
        set_image_auto_resize,
        get_image_auto_resize,
        set_image_auto_resize,
        bool
    );
    setting!(
        block_images,
        set_block_images,
        get_block_images,
        set_block_images,
        bool
    );

    fn image_model(&self) -> Option<String> {
        self.manager().get_image_model()
    }

    fn model_role(&self, role: ModelRole, session_model: &str) -> Option<ModelRoleValue> {
        let manager = self.manager();
        let source = |decl: &Decl| match manager.config_scope(decl) {
            None => ModelRoleSource::Unset,
            Some(SettingsScope::Global) => ModelRoleSource::Global,
            Some(SettingsScope::Project) => ModelRoleSource::Project,
        };
        let session = || {
            if session_model.is_empty() {
                "the session model".to_owned()
            } else {
                session_model.to_owned()
            }
        };
        let (selector, source, fallback) = match role_target(role) {
            RoleTarget::Chat => (
                manager
                    .get_default_provider()
                    .zip(manager.get_default_model())
                    .map(|(provider, model)| format!("{provider}/{model}")),
                source(&table::DEFAULT_MODEL),
                "the built-in default model".to_owned(),
            ),
            RoleTarget::Remote(decl) => {
                let fallback = match role {
                    ModelRole::Memory => manager
                        .get_auxiliary_model()
                        .map(|model| model.trim().to_owned())
                        .filter(|model| !model.is_empty())
                        .unwrap_or_else(session),
                    ModelRole::Subagent => "the parent's model".to_owned(),
                    ModelRole::Gateway => "the gateway session's model".to_owned(),
                    ModelRole::Chat
                    | ModelRole::Auxiliary
                    | ModelRole::Image
                    | ModelRole::Titles
                    | ModelRole::Judge
                    | ModelRole::Translate
                    | ModelRole::Speech
                    | ModelRole::Dictation => session(),
                };
                (manager.cvars().optional_text(decl), source(decl), fallback)
            }
            RoleTarget::Local(tiny, decl) => {
                // What runs once the primary is unset: the role's chain
                // without it (`pick` in bend/tiny.bend, compiled).
                let settings = eukhe_core::tiny::RoleSettings {
                    primary: String::new(),
                    ..eukhe_core::tiny::role_settings(manager.cvars(), tiny)
                };
                let home = eukhe_core::tiny::TinyHome::under(&self.agent_dir);
                let fallback =
                    match eukhe_core::tiny::resolve(tiny, &settings, &home, session_model) {
                        Pick::Use(Candidate::Local(id)) => format!("{LOCAL_PREFIX}{id}"),
                        Pick::Use(Candidate::Remote(selector)) => selector,
                        Pick::Unavailable => "no model available".to_owned(),
                    };
                (manager.cvars().optional_text(decl), source(decl), fallback)
            }
        };
        let thinking = match role {
            ModelRole::Memory => Some(manager.get_memory_thinking().model_level()),
            ModelRole::Chat
            | ModelRole::Auxiliary
            | ModelRole::Image
            | ModelRole::Subagent
            | ModelRole::Gateway
            | ModelRole::Titles
            | ModelRole::Judge
            | ModelRole::Translate
            | ModelRole::Speech
            | ModelRole::Dictation => None,
        };
        Some(ModelRoleValue {
            selector,
            source,
            fallback,
            thinking,
        })
    }

    fn set_model_role(
        &self,
        role: ModelRole,
        selector: &str,
        thinking: Option<eukhe_types::ai::ModelThinkingLevel>,
    ) -> Result<()> {
        let decl = match role_target(role) {
            RoleTarget::Chat => {
                anyhow::bail!("The chat role switches through the session")
            }
            RoleTarget::Remote(decl) | RoleTarget::Local(_, decl) => decl,
        };
        let mut commands = vec![Command::Set {
            id: decl.id.to_owned(),
            value: selector.to_owned(),
        }];
        match (role, thinking) {
            (_, None) => {}
            (ModelRole::Memory, Some(level)) => commands.push(Command::Set {
                id: table::MEMORY_THINKING.id.to_owned(),
                value: level.wire_name().to_owned(),
            }),
            (
                ModelRole::Chat
                | ModelRole::Auxiliary
                | ModelRole::Image
                | ModelRole::Subagent
                | ModelRole::Gateway
                | ModelRole::Titles
                | ModelRole::Judge
                | ModelRole::Translate
                | ModelRole::Speech
                | ModelRole::Dictation,
                Some(_),
            ) => anyhow::bail!("The {} role takes no thinking level", role.id()),
        }
        self.manager()
            .run_global(&commands)
            .map_err(|error| anyhow::anyhow!("{error}"))
    }

    fn clear_model_role(&self, role: ModelRole) -> Result<()> {
        match role_target(role) {
            RoleTarget::Chat => anyhow::bail!("The chat role always holds a model"),
            RoleTarget::Remote(decl) | RoleTarget::Local(_, decl) => {
                self.manager().clear_global(&[decl])
            }
        }
    }

    fn local_role_choices(&self, role: ModelRole) -> LocalRoleChoices {
        let RoleTarget::Local(tiny, _) = role_target(role) else {
            return LocalRoleChoices::default();
        };
        let home = eukhe_core::tiny::TinyHome::under(&self.agent_dir);
        LocalRoleChoices {
            models: eukhe_tiny::CATALOG
                .iter()
                .filter(|model| model.roles.contains(&tiny))
                .map(|model| LocalRoleModel {
                    id: model.id.to_owned(),
                    title: model.title.to_owned(),
                    installed: eukhe_tiny::installed(&home, model),
                })
                .collect(),
            takes_remote: tiny.takes_remote(),
        }
    }

    setting!(
        enable_skill_commands,
        set_enable_skill_commands,
        get_enable_skill_commands,
        set_enable_skill_commands,
        bool
    );
    setting!(
        enable_builtin_skills,
        set_enable_builtin_skills,
        get_enable_builtin_skills,
        set_enable_builtin_skills,
        bool
    );
    setting!(
        show_hardware_cursor,
        set_show_hardware_cursor,
        get_show_hardware_cursor,
        set_show_hardware_cursor,
        bool
    );
    setting!(
        editor_padding_x,
        set_editor_padding_x,
        get_editor_padding_x,
        set_editor_padding_x,
        u64
    );
    setting!(
        autocomplete_max_visible,
        set_autocomplete_max_visible,
        get_autocomplete_max_visible,
        set_autocomplete_max_visible,
        u64
    );
    setting!(
        quiet_startup,
        set_quiet_startup,
        get_quiet_startup,
        set_quiet_startup,
        bool
    );
    str_setting!(
        idle_eviction_minutes,
        set_idle_eviction_minutes,
        get_idle_eviction_minutes,
        set_idle_eviction_minutes
    );
    str_setting!(
        mermaid_rendering_mode,
        set_mermaid_rendering_mode,
        get_mermaid_rendering_mode,
        set_mermaid_rendering_mode
    );
    fn workflow_size(&self) -> String {
        self.manager().get_workflow_size().as_str().to_owned()
    }

    fn set_workflow_size(&self, size: &str) -> Result<()> {
        self.manager().set_workflow_size(size)?.applied()
    }

    str_setting!(
        tree_filter_mode,
        set_tree_filter_mode,
        get_tree_filter_mode,
        set_tree_filter_mode
    );
    str_setting!(
        chat_detail,
        set_chat_detail,
        get_chat_detail,
        set_chat_detail
    );
    setting!(
        factory_enabled,
        set_factory_enabled,
        get_factory_enabled,
        set_factory_enabled,
        bool
    );
    setting!(
        warnings_anthropic_extra_usage,
        set_warnings_anthropic_extra_usage,
        get_warnings_anthropic_extra_usage,
        set_warnings_anthropic_extra_usage,
        bool
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `terminal.streamPace` in the settings file reaches the TUI rate; a
    /// `minChars` of 0 reads as 1.
    #[test]
    fn stream_pace_reads_the_terminal_settings() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let agent_dir = dir.path().join("agent");
        std::fs::create_dir_all(&agent_dir).expect("agent dir");
        std::fs::write(
            agent_dir.join("settings.json"),
            r#"{ "terminal": { "streamPace": { "minChars": 0, "lag": 7 } } }"#,
        )
        .expect("settings file");
        let settings = CliClientSettings::new(
            dir.path().to_path_buf(),
            agent_dir,
            CliThemeFlags::default(),
        );
        assert_eq!(
            settings.stream_pace(),
            eukhe_tui::pace::PaceRate { min: 1, lag: 7 }
        );
    }

    /// The seam over the real settings store: every write persists through
    /// the eukhe-core manager and the next read (a fresh manager over the same
    /// dirs, exactly what every call does) sees it.
    #[test]
    fn seam_round_trips_through_the_settings_store() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let agent_dir = dir.path().join("agent");
        std::fs::create_dir_all(&agent_dir).expect("agent dir");
        let settings = CliClientSettings::new(
            dir.path().to_path_buf(),
            agent_dir.clone(),
            CliThemeFlags::default(),
        );

        // The TS defaults read first.
        assert!(settings.show_images());
        assert!(!settings.quiet_startup());
        assert_eq!(settings.idle_eviction_minutes(), "90");
        assert_eq!(settings.mermaid_rendering_mode(), "streaming");
        assert_eq!(settings.tree_filter_mode(), "user-only");
        assert!(settings.warnings_anthropic_extra_usage());
        assert_eq!(settings.stream_pace(), eukhe_tui::pace::PaceRate::DEFAULT);

        // Writes persist (the settings file lands in the agent dir).
        settings.set_theme("dark").expect("theme");
        settings.set_idle_eviction_minutes("off").expect("idle");
        settings.set_tree_filter_mode("all").expect("tree filter");
        settings.set_show_images(false).expect("show images");
        assert!(settings.fullscreen());
        settings.set_fullscreen(false).expect("fullscreen");

        assert_eq!(settings.theme().as_deref(), Some("dark"));
        assert_eq!(settings.idle_eviction_minutes(), "off");
        assert_eq!(settings.tree_filter_mode(), "all");
        assert!(!settings.show_images());
        assert!(!settings.fullscreen());

        // The persisted file the real consumers read.
        let content =
            std::fs::read_to_string(agent_dir.join("settings.json")).expect("settings file");
        let value: serde_json::Value = serde_json::from_str(&content).expect("parse");
        assert_eq!(value["theme"], "dark");
        assert_eq!(value["idleEvictionMinutes"], "off");
        assert_eq!(value["treeFilterMode"], "all");
        assert_eq!(value["terminal"]["showImages"], false);
        assert_eq!(value["terminal"]["fullscreen"], false);

        // The factory's opt-in gate (`/factory on|off|status`): unset reads
        // as disabled (the default off), and the write persists the exact
        // nested-camelCase key the kernel's gate and the daemon's lane
        // advertisement read -- over the same document, leaving the other
        // keys alone.
        assert!(!settings.factory_enabled());
        settings.set_factory_enabled(true).expect("factory enabled");
        assert!(settings.factory_enabled());
        let content =
            std::fs::read_to_string(agent_dir.join("settings.json")).expect("settings file");
        let value: serde_json::Value = serde_json::from_str(&content).expect("parse");
        assert_eq!(value["factory"]["enabled"], true);
        assert_eq!(value["theme"], "dark", "the write leaves the other keys");
        settings
            .set_factory_enabled(false)
            .expect("factory disabled");
        assert!(!settings.factory_enabled());
        let content =
            std::fs::read_to_string(agent_dir.join("settings.json")).expect("settings file");
        let value: serde_json::Value = serde_json::from_str(&content).expect("parse");
        assert_eq!(value["factory"]["enabled"], false);
    }

    /// Every non-chat role's global key, in `ModelRole::ALL` order.
    const ROLE_KEYS: [(ModelRole, &str); 10] = [
        (ModelRole::Memory, "memory.model"),
        (ModelRole::Auxiliary, "auxiliaryModel"),
        (ModelRole::Image, "imageModel"),
        (ModelRole::Subagent, "subagentDefaultModel"),
        (ModelRole::Gateway, "gateway.signal.model"),
        (ModelRole::Titles, "modelRoles.tiny"),
        (ModelRole::Judge, "modelRoles.judge"),
        (ModelRole::Translate, "modelRoles.translate"),
        (ModelRole::Speech, "modelRoles.speech"),
        (ModelRole::Dictation, "modelRoles.dictation"),
    ];

    fn role_settings(dir: &std::path::Path) -> Arc<CliClientSettings> {
        let agent_dir = dir.join("agent");
        std::fs::create_dir_all(&agent_dir).expect("agent dir");
        CliClientSettings::new(dir.to_path_buf(), agent_dir, CliThemeFlags::default())
    }

    /// The hub's role list reads each role's own key from the global
    /// settings.json; `chat` reads the default provider and model.
    #[test]
    fn each_model_role_reads_its_key() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let settings = role_settings(dir.path());
        let mut document = serde_json::json!({
            "defaultProvider": "p",
            "defaultModel": "chat-model",
        });
        for (role, key) in ROLE_KEYS {
            let path: Vec<&str> = key.split('.').collect();
            let mut node = &mut document;
            for part in &path[..path.len() - 1] {
                node = node
                    .as_object_mut()
                    .expect("object")
                    .entry(*part)
                    .or_insert_with(|| serde_json::json!({}));
            }
            node[path[path.len() - 1]] = serde_json::json!(format!("p/{}", role.id()));
        }
        std::fs::write(
            dir.path().join("agent").join("settings.json"),
            document.to_string(),
        )
        .expect("settings.json");
        let read = |role| settings.model_role(role, "").expect("store");
        assert_eq!(
            (read(ModelRole::Chat).selector, read(ModelRole::Chat).source),
            (Some("p/chat-model".to_owned()), ModelRoleSource::Global)
        );
        for (role, _) in ROLE_KEYS {
            let value = read(role);
            assert_eq!(
                (value.selector, value.source),
                (Some(format!("p/{}", role.id())), ModelRoleSource::Global),
                "{}",
                role.id()
            );
        }
    }

    /// Assigning a role writes its key to the global config.cfg (the
    /// `/set --global` path) and the next read sees it; `memory` keeps
    /// its thinking in the same write; `chat` and a stray thinking level
    /// are refused.
    #[test]
    fn assigning_a_model_role_writes_its_global_key() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let settings = role_settings(dir.path());
        for (role, key) in ROLE_KEYS {
            let selector = format!("prov/{}-model", role.id());
            settings
                .set_model_role(role, &selector, None)
                .expect("assign");
            let cfg = std::fs::read_to_string(dir.path().join("agent").join("config.cfg"))
                .expect("config.cfg");
            assert!(
                cfg.lines().any(
                    |line| line.starts_with(&format!("set {key} ")) && line.contains(&selector)
                ),
                "{key} in {cfg}"
            );
            let value = settings.model_role(role, "").expect("store");
            assert_eq!(
                (value.selector, value.source),
                (Some(selector), ModelRoleSource::Global)
            );
        }
        settings
            .set_model_role(
                ModelRole::Memory,
                "prov/m",
                Some(eukhe_types::ai::ModelThinkingLevel::High),
            )
            .expect("memory with thinking");
        assert_eq!(
            settings
                .model_role(ModelRole::Memory, "")
                .expect("store")
                .thinking,
            Some(eukhe_types::ai::ModelThinkingLevel::High)
        );
        assert!(settings
            .set_model_role(ModelRole::Chat, "p/m", None)
            .is_err());
        assert!(settings
            .set_model_role(
                ModelRole::Image,
                "p/m",
                Some(eukhe_types::ai::ModelThinkingLevel::Low)
            )
            .is_err());
    }

    /// Clearing a role unsets it in both global files: it reads unset and
    /// falls back (a text tiny role to the session model its chain picks;
    /// with no installed local model and no session model, none).
    #[test]
    fn clearing_a_model_role_falls_back() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let settings = role_settings(dir.path());
        std::fs::write(
            dir.path().join("agent").join("settings.json"),
            r#"{ "modelRoles": { "tiny": "local/lfm2.5-350m" } }"#,
        )
        .expect("settings.json");
        settings
            .set_model_role(ModelRole::Titles, "local/lfm2.5-230m", None)
            .expect("assign");
        settings.clear_model_role(ModelRole::Titles).expect("clear");
        let value = settings
            .model_role(ModelRole::Titles, "prov/session")
            .expect("store");
        assert_eq!(
            (value.selector, value.source, value.fallback),
            (None, ModelRoleSource::Unset, "prov/session".to_owned())
        );
        assert_eq!(
            settings
                .model_role(ModelRole::Titles, "")
                .expect("store")
                .fallback,
            "no model available"
        );
        assert_eq!(
            settings
                .model_role(ModelRole::Speech, "prov/session")
                .expect("store")
                .fallback,
            "no model available",
            "speech takes no remote model"
        );
        assert!(settings.clear_model_role(ModelRole::Chat).is_err());
    }

    /// Regression (audit M2): a theme pick that the global config.cfg
    /// shadows was saved and then reverted at the next start with no
    /// word. The setter now says which file sets it.
    #[test]
    fn a_setting_a_cfg_file_shadows_says_so() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let agent_dir = dir.path().join("agent");
        std::fs::create_dir_all(&agent_dir).expect("agent dir");
        std::fs::write(agent_dir.join("config.cfg"), "set theme light\n").expect("config.cfg");
        let settings = CliClientSettings::new(
            dir.path().to_path_buf(),
            agent_dir.clone(),
            CliThemeFlags::default(),
        );
        let error = settings.set_theme("dark").expect_err("shadowed");
        assert_eq!(
            error.to_string(),
            format!(
                "`theme` is saved, but {} also sets it, so that value applies",
                agent_dir.join("config.cfg").display()
            )
        );
        assert_eq!(settings.theme().as_deref(), Some("light"));
    }

    /// The registered themes are the resource system's (here an
    /// auto-discovered agent-dir theme) plus the `--theme` paths;
    /// `--no-themes` keeps only the `--theme` paths.
    #[test]
    fn theme_sources_register_the_resource_themes_and_the_cli_paths() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let agent_dir = dir.path().join("agent");
        let auto = agent_dir.join("themes").join("auto.json");
        let cli_theme = dir.path().join("cli.json");
        std::fs::create_dir_all(auto.parent().expect("themes dir")).expect("themes dir");
        std::fs::write(&auto, "{}").expect("auto theme");
        std::fs::write(&cli_theme, "{}").expect("cli theme");
        let flags = CliThemeFlags {
            paths: vec![cli_theme.clone()],
            no_themes: false,
        };
        let settings =
            CliClientSettings::new(dir.path().to_path_buf(), agent_dir.clone(), flags.clone());
        assert_eq!(
            settings.theme_sources(),
            ThemeSources {
                registered: vec![auto, cli_theme.clone()],
                custom_dir: Some(agent_dir.join("themes")),
                diagnostics: Vec::new(),
            }
        );
        let settings = CliClientSettings::new(
            dir.path().to_path_buf(),
            agent_dir.clone(),
            CliThemeFlags {
                no_themes: true,
                ..flags
            },
        );
        assert_eq!(
            settings.theme_sources(),
            ThemeSources {
                registered: vec![cli_theme],
                custom_dir: Some(agent_dir.join("themes")),
                diagnostics: Vec::new(),
            }
        );
    }

    /// A theme warning lands in the agent log under the theme component.
    #[test]
    fn theme_warnings_go_to_the_agent_log() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let agent_dir = dir.path().join("agent");
        let settings = CliClientSettings::new(
            dir.path().to_path_buf(),
            agent_dir.clone(),
            CliThemeFlags::default(),
        );
        settings.log_theme_warning("Theme \"x\" unavailable");
        let raw =
            std::fs::read_to_string(agent_dir.join("logs").join("agent.jsonl")).expect("agent log");
        let entry: serde_json::Value = serde_json::from_str(raw.trim()).expect("one entry");
        assert_eq!(
            (&entry["level"], &entry["component"], &entry["msg"]),
            (
                &serde_json::json!("warn"),
                &serde_json::json!("coding-agent.theme"),
                &serde_json::json!("Theme \"x\" unavailable"),
            )
        );
    }
}
