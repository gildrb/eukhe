//! The interactive client-settings seam implementation: every call opens
//! the file-backed settings manager over the run's directories (the store
//! is a pair of small JSON files, so the re-read is the same freshness
//! the TS manager's `reload` produces) and applies the one setting.

use anyhow::Result;
use std::path::PathBuf;
use std::sync::Arc;

use eukhe_core::agent_log::{AgentLog, AgentLogLevel};
use eukhe_core::resources::ThemePathOptions;
use eukhe_theme::ThemeSources;
use eukhe_tui::client_settings::ClientSettings;

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

    fn memory_model(&self) -> Option<String> {
        self.manager().get_memory_model()
    }

    fn set_memory_model(&self, provider: &str, model_id: &str) -> Result<()> {
        self.manager()
            .set_memory_model(provider, model_id)?
            .applied()
    }

    fn memory_thinking(&self) -> Option<eukhe_types::ai::ModelThinkingLevel> {
        Some(self.manager().get_memory_thinking().model_level())
    }

    fn set_memory_model_with_thinking(
        &self,
        provider: &str,
        model_id: &str,
        thinking: eukhe_types::ai::ModelThinkingLevel,
    ) -> Result<()> {
        self.manager()
            .set_memory_model_with_thinking(
                provider,
                model_id,
                eukhe_core::settings::ThinkingLevelSetting::from_model_level(thinking),
            )?
            .applied()
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
