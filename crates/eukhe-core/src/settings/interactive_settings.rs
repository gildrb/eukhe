//! The interactive settings-menu accessors (TS settings-manager getters and
//! setters behind the `/settings` rows). Every
//! setter writes the global scope like the TS `markModified` + `save` pair;
//! every getter reads its cvar (`settings::cvar::table`) with its declared
//! default.

use anyhow::{anyhow, Result};

use super::cvar::{table, CvarType};
use super::getters::{default_nat, default_text};
use super::manager::SettingsManager;

impl SettingsManager {
    /// `terminal.showImages` setter (the getter lives with the manager's
    /// startup accessors).
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings scope cannot be saved.
    pub fn set_show_images(&mut self, show: bool) -> Result<()> {
        self.global_mut()
            .terminal
            .get_or_insert_with(Default::default)
            .show_images = Some(show);
        self.save_global_scope()
    }

    /// `terminal.clearOnShrink` (TS default: the `EUKHE_CLEAR_ON_SHRINK`
    /// environment value; this port has no such override).
    #[must_use]
    pub fn get_clear_on_shrink(&self) -> bool {
        self.cvars().bool(&table::TERMINAL_CLEAR_ON_SHRINK)
    }

    /// `terminal.clearOnShrink` setter.
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings scope cannot be saved.
    pub fn set_clear_on_shrink(&mut self, enabled: bool) -> Result<()> {
        self.global_mut()
            .terminal
            .get_or_insert_with(Default::default)
            .clear_on_shrink = Some(enabled);
        self.save_global_scope()
    }

    /// `terminal.showTerminalProgress`.
    #[must_use]
    pub fn get_show_terminal_progress(&self) -> bool {
        self.cvars().bool(&table::TERMINAL_SHOW_TERMINAL_PROGRESS)
    }

    /// `terminal.showTerminalProgress` setter.
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings scope cannot be saved.
    pub fn set_show_terminal_progress(&mut self, enabled: bool) -> Result<()> {
        self.global_mut()
            .terminal
            .get_or_insert_with(Default::default)
            .show_terminal_progress = Some(enabled);
        self.save_global_scope()
    }

    /// `terminal.fullscreen` setter (the getter lives with the manager's
    /// startup accessors).
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings scope cannot be saved.
    pub fn set_fullscreen(&mut self, enabled: bool) -> Result<()> {
        self.global_mut()
            .terminal
            .get_or_insert_with(Default::default)
            .fullscreen = Some(enabled);
        self.save_global_scope()
    }

    /// `images.autoResize`.
    #[must_use]
    pub fn get_image_auto_resize(&self) -> bool {
        self.cvars().bool(&table::IMAGES_AUTO_RESIZE)
    }

    /// `images.autoResize` setter.
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings scope cannot be saved.
    pub fn set_image_auto_resize(&mut self, enabled: bool) -> Result<()> {
        self.global_mut()
            .images
            .get_or_insert_with(Default::default)
            .auto_resize = Some(enabled);
        self.save_global_scope()
    }

    /// `images.blockImages`.
    #[must_use]
    pub fn get_block_images(&self) -> bool {
        self.cvars().bool(&table::IMAGES_BLOCK_IMAGES)
    }

    /// `images.blockImages` setter.
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings scope cannot be saved.
    pub fn set_block_images(&mut self, blocked: bool) -> Result<()> {
        self.global_mut()
            .images
            .get_or_insert_with(Default::default)
            .block_images = Some(blocked);
        self.save_global_scope()
    }

    /// `enableSkillCommands`.
    #[must_use]
    pub fn get_enable_skill_commands(&self) -> bool {
        self.cvars().bool(&table::ENABLE_SKILL_COMMANDS)
    }

    /// `enableSkillCommands` setter.
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings scope cannot be saved.
    pub fn set_enable_skill_commands(&mut self, enabled: bool) -> Result<()> {
        self.global_mut().enable_skill_commands = Some(enabled);
        self.save_global_scope()
    }

    /// `enableBuiltinSkills`.
    #[must_use]
    pub fn get_enable_builtin_skills(&self) -> bool {
        self.cvars().bool(&table::ENABLE_BUILTIN_SKILLS)
    }

    /// `enableBuiltinSkills` setter.
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings scope cannot be saved.
    pub fn set_enable_builtin_skills(&mut self, enabled: bool) -> Result<()> {
        self.global_mut().enable_builtin_skills = Some(enabled);
        self.save_global_scope()
    }

    /// `showHardwareCursor` (the `EUKHE_HARDWARE_CURSOR` override is not
    /// part of this port).
    #[must_use]
    pub fn get_show_hardware_cursor(&self) -> bool {
        self.cvars().bool(&table::SHOW_HARDWARE_CURSOR)
    }

    /// `showHardwareCursor` setter.
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings scope cannot be saved.
    pub fn set_show_hardware_cursor(&mut self, enabled: bool) -> Result<()> {
        self.global_mut().show_hardware_cursor = Some(enabled);
        self.save_global_scope()
    }

    /// `editorPaddingX` (the setter clamps 0-3).
    #[must_use]
    pub fn get_editor_padding_x(&self) -> u64 {
        self.cvars().nat(&table::EDITOR_PADDING_X)
    }

    /// `editorPaddingX` setter (clamped 0-3).
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings scope cannot be saved.
    pub fn set_editor_padding_x(&mut self, padding: u64) -> Result<()> {
        self.global_mut().editor_padding_x = Some(padding.min(3));
        self.save_global_scope()
    }

    /// `autocompleteMaxVisible` (the setter clamps 3-20).
    #[must_use]
    pub fn get_autocomplete_max_visible(&self) -> u64 {
        self.cvars().nat(&table::AUTOCOMPLETE_MAX_VISIBLE)
    }

    /// `autocompleteMaxVisible` setter (clamped 3-20).
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings scope cannot be saved.
    pub fn set_autocomplete_max_visible(&mut self, max_visible: u64) -> Result<()> {
        self.global_mut().autocomplete_max_visible = Some(max_visible.clamp(3, 20));
        self.save_global_scope()
    }

    /// `quietStartup`.
    #[must_use]
    pub fn get_quiet_startup(&self) -> bool {
        self.cvars().bool(&table::QUIET_STARTUP)
    }

    /// `quietStartup` setter.
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings scope cannot be saved.
    pub fn set_quiet_startup(&mut self, quiet: bool) -> Result<()> {
        self.global_mut().quiet_startup = Some(quiet);
        self.save_global_scope()
    }

    /// `idleEvictionMinutes` (TS `number | "off"`; a `none` value reads as
    /// `off`, an invalid number as the default, like the TS getter).
    #[must_use]
    pub fn get_idle_eviction_minutes(&self) -> String {
        let decl = &table::IDLE_EVICTION_MINUTES;
        let value = self.cvars().value(decl);
        if value.as_str() == Some("off") || value.as_str() == Some("none") {
            return "off".to_string();
        }
        match value.as_f64() {
            Some(number) if number.is_finite() && number > 0.0 => {
                let rounded = number.round();
                if (number - rounded).abs() < f64::EPSILON {
                    format!("{rounded:.0}")
                } else {
                    format!("{number}")
                }
            }
            _ => default_nat(decl).to_string(),
        }
    }

    /// TS `setIdleEvictionMinutes`: a positive number or `"off"`.
    ///
    /// # Errors
    ///
    /// Returns an error when the value is neither `"off"` nor a positive
    /// finite number, or when the global settings scope cannot be saved.
    pub fn set_idle_eviction_minutes(&mut self, value: &str) -> Result<()> {
        if value == "off" {
            self.global_mut().idle_eviction_minutes = Some(serde_json::json!("off"));
            return self.save_global_scope();
        }
        let number: f64 = value
            .parse()
            .map_err(|_| anyhow!("Idle eviction minutes must be a positive number or off"))?;
        if !number.is_finite() || number <= 0.0 {
            return Err(anyhow!(
                "Idle eviction minutes must be a positive number or off"
            ));
        }
        self.global_mut().idle_eviction_minutes = Some(serde_json::json!(number));
        self.save_global_scope()
    }

    /// `markdown.mermaid` (`off`, `final`, or `streaming`).
    #[must_use]
    pub fn get_mermaid_rendering_mode(&self) -> &'static str {
        let decl = &table::MARKDOWN_MERMAID;
        let mode = self.cvars().text(decl);
        match decl.ty {
            CvarType::Choice(modes) => modes.iter().find(|known| **known == mode).copied(),
            CvarType::Bool
            | CvarType::Nat
            | CvarType::Text
            | CvarType::List
            | CvarType::ChoiceList(_)
            | CvarType::Json => None,
        }
        .unwrap_or_else(|| default_text(decl))
    }

    /// `markdown.mermaid` setter (`off`, `final`, or `streaming`).
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown rendering mode, or when the global
    /// settings scope cannot be saved.
    pub fn set_mermaid_rendering_mode(&mut self, mode: &str) -> Result<()> {
        let parsed = match mode {
            "off" => super::types::MermaidRenderingMode::Off,
            "final" => super::types::MermaidRenderingMode::Final,
            "streaming" => super::types::MermaidRenderingMode::Streaming,
            other => return Err(anyhow!("Unknown mermaid rendering mode: {other}")),
        };
        self.global_mut()
            .markdown
            .get_or_insert_with(Default::default)
            .mermaid = Some(parsed);
        self.save_global_scope()
    }

    /// `warnings.anthropicExtraUsage`.
    #[must_use]
    pub fn get_warnings_anthropic_extra_usage(&self) -> bool {
        self.cvars().bool(&table::WARNINGS_ANTHROPIC_EXTRA_USAGE)
    }

    /// `warnings.anthropicExtraUsage` setter.
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings scope cannot be saved.
    pub fn set_warnings_anthropic_extra_usage(&mut self, enabled: bool) -> Result<()> {
        self.global_mut()
            .warnings
            .get_or_insert_with(Default::default)
            .anthropic_extra_usage = Some(enabled);
        self.save_global_scope()
    }

    /// `treeFilterMode` setter (the getter lives with the manager's
    /// startup accessors); TS `setTreeFilterMode` writes the global scope.
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings scope cannot be saved.
    pub fn set_tree_filter_mode(&mut self, mode: &str) -> Result<()> {
        self.global_mut().tree_filter_mode = Some(mode.to_string());
        self.save_global_scope()
    }

    /// `chatDetail` setter (TS #2709 `setChatDetail`: the Ctrl+O cycle
    /// saves the level); TS writes the global scope.
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings scope cannot be saved.
    pub fn set_chat_detail(&mut self, detail: &str) -> Result<()> {
        self.global_mut().chat_detail = Some(detail.to_string());
        self.save_global_scope()
    }

    /// `factory.enabled` (the agent factory's opt-in gate): unset reads
    /// as disabled — the factory stays off until the user runs
    /// `/factory on`. A Global cvar: only the global settings set it, the
    /// document `set_factory_enabled` writes and the kernel's factory gate
    /// reads, so no project can flip the gate out from under the kernel.
    #[must_use]
    pub fn get_factory_enabled(&self) -> bool {
        self.cvars().bool(&table::FACTORY_ENABLED)
    }

    /// `factory.enabled` setter: persists the opt-in gate to the global
    /// scope (the same shared settings key the daemon's lane advertisement
    /// and the kernel's factory gate read).
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings scope cannot be saved.
    pub fn set_factory_enabled(&mut self, enabled: bool) -> Result<()> {
        self.global_mut()
            .factory
            .get_or_insert_with(Default::default)
            .enabled = Some(enabled);
        self.save_global_scope()
    }

    /// `enabledModels` (TS `getEnabledModels`/`setEnabledModels`): the
    /// persisted model-scope patterns (`None` is no filter).
    #[must_use]
    pub fn get_enabled_models(&self) -> Option<Vec<String>> {
        let patterns = self.cvars().list(&table::ENABLED_MODELS);
        (!patterns.is_empty()).then_some(patterns)
    }
}
