//! The interactive client-settings seam implementation: every call opens
//! the file-backed settings manager over the run's directories (the store
//! is a pair of small JSON files, so the re-read is the same freshness
//! the TS manager's `reload` produces) and applies the one setting.

use anyhow::Result;
use std::path::PathBuf;
use std::sync::Arc;

use eukhe_core::agent_log::{AgentLog, AgentLogLevel};
use eukhe_core::resources::ThemePathOptions;
use eukhe_tui::client_settings::ClientSettings;
use eukhe_tui::theme_catalog::ThemeSources;

/// The agent-log component theme warnings go to.
const THEME_LOG_COMPONENT: &str = "coding-agent.theme";

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
            self.manager().$setter(value)
        }
    };
}

macro_rules! str_setting {
    ($get:ident, $set:ident, $getter:ident, $setter:ident) => {
        fn $get(&self) -> String {
            self.manager().$getter().to_string()
        }

        fn $set(&self, value: &str) -> Result<()> {
            self.manager().$setter(value)
        }
    };
}

impl ClientSettings for CliClientSettings {
    fn theme(&self) -> Option<String> {
        self.manager().get_theme().map(str::to_string)
    }

    fn set_theme(&self, theme: &str) -> Result<()> {
        self.manager().set_theme(theme.to_string())
    }

    fn theme_sources(&self) -> ThemeSources {
        let custom_dir = Some(self.agent_dir.join("themes"));
        let options = ThemePathOptions {
            cwd: self.cwd.clone(),
            agent_dir: self.agent_dir.clone(),
            additional_theme_paths: self.themes.paths.clone(),
            no_themes: self.themes.no_themes,
        };
        match eukhe_core::resources::resolve_theme_paths(&options) {
            Ok(registered) => ThemeSources {
                registered,
                custom_dir,
                diagnostics: Vec::new(),
            },
            // The resource themes are unavailable; the `--theme` paths and
            // the custom directory still resolve.
            Err(error) => ThemeSources {
                registered: self.themes.paths.clone(),
                custom_dir,
                diagnostics: vec![format!("Theme resources failed to resolve: {error:#}")],
            },
        }
    }

    fn log_theme_warning(&self, message: &str) {
        AgentLog::new(&self.agent_dir, THEME_LOG_COMPONENT).log(
            AgentLogLevel::Warn,
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
        self.manager().set_default_service_tier(parsed)
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
        self.manager()
            .global_settings()
            .memory
            .as_ref()
            .and_then(|memory| memory.model.as_deref())
            .map(str::trim)
            .filter(|model| !model.is_empty())
            .map(str::to_string)
    }

    fn set_memory_model(&self, provider: &str, model_id: &str) -> Result<()> {
        self.manager().set_memory_model(provider, model_id)
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

    fn telemetry_status(&self) -> String {
        eukhe_core::session_engine::telemetry::telemetry_status_text(
            &self.manager(),
            &self.agent_dir,
        )
    }

    fn set_telemetry_enabled(&self, enabled: bool) -> Result<String> {
        eukhe_core::session_engine::telemetry::set_telemetry_enabled_text(
            &mut self.manager(),
            &self.agent_dir,
            enabled,
        )
    }

    fn telemetry_notice_due(&self) -> bool {
        // TS agent-session-services: telemetry enabled, onboarding
        // already shown (a first interactive launch belongs to the
        // onboarding screen; the notice surfaces on the next launch),
        // and the notice not yet shown.
        let manager = self.manager();
        eukhe_core::session_engine::telemetry::telemetry_switch(&manager).enabled()
            && manager.get_onboarding_shown()
            && !manager.get_telemetry_notice_shown()
    }

    fn set_telemetry_notice_shown(&self) -> Result<()> {
        self.manager().set_telemetry_notice_shown(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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

        // Writes persist (the settings file lands in the agent dir).
        settings.set_theme("dark").expect("theme");
        settings.set_idle_eviction_minutes("off").expect("idle");
        settings.set_tree_filter_mode("all").expect("tree filter");
        settings.set_show_images(false).expect("show images");
        assert!(!settings.fullscreen());
        settings.set_fullscreen(true).expect("fullscreen");

        assert_eq!(settings.theme().as_deref(), Some("dark"));
        assert_eq!(settings.idle_eviction_minutes(), "off");
        assert_eq!(settings.tree_filter_mode(), "all");
        assert!(!settings.show_images());
        assert!(settings.fullscreen());

        // The persisted file the real consumers read.
        let content =
            std::fs::read_to_string(agent_dir.join("settings.json")).expect("settings file");
        let value: serde_json::Value = serde_json::from_str(&content).expect("parse");
        assert_eq!(value["theme"], "dark");
        assert_eq!(value["idleEvictionMinutes"], "off");
        assert_eq!(value["treeFilterMode"], "all");
        assert_eq!(value["terminal"]["showImages"], false);
        assert_eq!(value["terminal"]["fullscreen"], true);

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
