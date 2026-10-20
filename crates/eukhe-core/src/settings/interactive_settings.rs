//! The interactive settings-menu accessors (TS settings-manager getters and
//! setters behind the `/settings` rows). Every
//! setter writes the global scope like the TS `markModified` + `save` pair;
//! every getter reads its cvar (`settings::cvar::table`) with its declared
//! default.

use anyhow::{anyhow, Result};
use serde_json::Value;

use super::cvar::{table, CvarType};
use super::getters::{default_nat, default_text};
use super::manager::SettingsManager;
use super::persist::Persisted;

impl SettingsManager {
    /// `terminal.showImages` setter (the getter lives with the manager's
    /// startup accessors).
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings scope cannot be saved.
    pub fn set_show_images(&mut self, show: bool) -> Result<Persisted> {
        self.set_global_cvar(&table::TERMINAL_SHOW_IMAGES, &Value::Bool(show))
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
    pub fn set_clear_on_shrink(&mut self, enabled: bool) -> Result<Persisted> {
        self.set_global_cvar(&table::TERMINAL_CLEAR_ON_SHRINK, &Value::Bool(enabled))
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
    pub fn set_show_terminal_progress(&mut self, enabled: bool) -> Result<Persisted> {
        self.set_global_cvar(
            &table::TERMINAL_SHOW_TERMINAL_PROGRESS,
            &Value::Bool(enabled),
        )
    }

    /// `terminal.showSpeed`: the status line's generation speed.
    #[must_use]
    pub fn get_show_speed(&self) -> bool {
        self.cvars().bool(&table::TERMINAL_SHOW_SPEED)
    }

    /// `terminal.fullscreen` setter (the getter lives with the manager's
    /// startup accessors).
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings scope cannot be saved.
    pub fn set_fullscreen(&mut self, enabled: bool) -> Result<Persisted> {
        self.set_global_cvar(&table::TERMINAL_FULLSCREEN, &Value::Bool(enabled))
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
    pub fn set_image_auto_resize(&mut self, enabled: bool) -> Result<Persisted> {
        self.set_global_cvar(&table::IMAGES_AUTO_RESIZE, &Value::Bool(enabled))
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
    pub fn set_block_images(&mut self, blocked: bool) -> Result<Persisted> {
        self.set_global_cvar(&table::IMAGES_BLOCK_IMAGES, &Value::Bool(blocked))
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
    pub fn set_enable_skill_commands(&mut self, enabled: bool) -> Result<Persisted> {
        self.set_global_cvar(&table::ENABLE_SKILL_COMMANDS, &Value::Bool(enabled))
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
    pub fn set_enable_builtin_skills(&mut self, enabled: bool) -> Result<Persisted> {
        self.set_global_cvar(&table::ENABLE_BUILTIN_SKILLS, &Value::Bool(enabled))
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
    pub fn set_show_hardware_cursor(&mut self, enabled: bool) -> Result<Persisted> {
        self.set_global_cvar(&table::SHOW_HARDWARE_CURSOR, &Value::Bool(enabled))
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
    pub fn set_editor_padding_x(&mut self, padding: u64) -> Result<Persisted> {
        self.set_global_cvar(&table::EDITOR_PADDING_X, &Value::from(padding.min(3)))
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
    pub fn set_autocomplete_max_visible(&mut self, max_visible: u64) -> Result<Persisted> {
        self.set_global_cvar(
            &table::AUTOCOMPLETE_MAX_VISIBLE,
            &Value::from(max_visible.clamp(3, 20)),
        )
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
    pub fn set_quiet_startup(&mut self, quiet: bool) -> Result<Persisted> {
        self.set_global_cvar(&table::QUIET_STARTUP, &Value::Bool(quiet))
    }

    /// `idleEvictionMinutes` (`number | "off"`; a `none` value reads as
    /// `off`; the load names a malformed value, which then reads as unset).
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

    /// TS `setIdleEvictionMinutes`: a positive whole number of minutes,
    /// or `"off"`.
    ///
    /// # Errors
    ///
    /// The value is neither `"off"` nor a positive whole number, or the
    /// global settings file cannot be read, parsed or written.
    pub fn set_idle_eviction_minutes(&mut self, value: &str) -> Result<Persisted> {
        if value == "off" {
            return self.set_global_cvar(&table::IDLE_EVICTION_MINUTES, &Value::from("off"));
        }
        match value.parse::<u64>() {
            Ok(minutes) if minutes > 0 => {
                self.set_global_cvar(&table::IDLE_EVICTION_MINUTES, &Value::from(minutes))
            }
            Ok(_) | Err(_) => Err(anyhow!(
                "Idle eviction minutes must be a positive whole number or off"
            )),
        }
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
            | CvarType::NatOrOff
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
    pub fn set_mermaid_rendering_mode(&mut self, mode: &str) -> Result<Persisted> {
        let parsed = match mode {
            "off" => super::types::MermaidRenderingMode::Off,
            "final" => super::types::MermaidRenderingMode::Final,
            "streaming" => super::types::MermaidRenderingMode::Streaming,
            other => return Err(anyhow!("Unknown mermaid rendering mode: {other}")),
        };
        self.set_global_cvar(&table::MARKDOWN_MERMAID, &serde_json::to_value(parsed)?)
    }

    /// `workflow.size`: the default size of a `/dynamic-workflow` run.
    #[must_use]
    pub fn get_workflow_size(&self) -> eukhe_types::workflow::WorkflowSize {
        let decl = &table::WORKFLOW_SIZE;
        eukhe_types::workflow::WorkflowSize::parse(&self.cvars().text(decl))
            .or_else(|| eukhe_types::workflow::WorkflowSize::parse(default_text(decl)))
            .unwrap_or(eukhe_types::workflow::WorkflowSize::Medium)
    }

    /// `workflow.size` setter (`small`, `medium`, or `large`).
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown size, or when the global settings
    /// scope cannot be saved.
    pub fn set_workflow_size(&mut self, size: &str) -> Result<Persisted> {
        let parsed = eukhe_types::workflow::WorkflowSize::parse(size)
            .ok_or_else(|| anyhow!("Unknown workflow size: {size}"))?;
        self.set_global_cvar(&table::WORKFLOW_SIZE, &serde_json::to_value(parsed)?)
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
    pub fn set_warnings_anthropic_extra_usage(&mut self, enabled: bool) -> Result<Persisted> {
        self.set_global_cvar(
            &table::WARNINGS_ANTHROPIC_EXTRA_USAGE,
            &Value::Bool(enabled),
        )
    }

    /// `treeFilterMode` setter (the getter lives with the manager's
    /// startup accessors); TS `setTreeFilterMode` writes the global scope.
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings scope cannot be saved.
    pub fn set_tree_filter_mode(&mut self, mode: &str) -> Result<Persisted> {
        self.set_global_cvar(&table::TREE_FILTER_MODE, &Value::from(mode))
    }

    /// `chatDetail` setter (TS #2709 `setChatDetail`: the Ctrl+O cycle
    /// saves the level); TS writes the global scope.
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings scope cannot be saved.
    pub fn set_chat_detail(&mut self, detail: &str) -> Result<Persisted> {
        self.set_global_cvar(&table::CHAT_DETAIL, &Value::from(detail))
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
    pub fn set_factory_enabled(&mut self, enabled: bool) -> Result<Persisted> {
        self.set_global_cvar(&table::FACTORY_ENABLED, &Value::Bool(enabled))
    }

    /// `enabledModels` (TS `getEnabledModels`/`setEnabledModels`): the
    /// persisted model-scope patterns (`None` is no filter).
    #[must_use]
    pub fn get_enabled_models(&self) -> Option<Vec<String>> {
        let patterns = self.cvars().list(&table::ENABLED_MODELS);
        (!patterns.is_empty()).then_some(patterns)
    }
}
