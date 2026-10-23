//! The client-settings seam. eukhe-tui depends on eukhe-types only, so the
//! interactive commands that read or persist user settings (`/settings`)
//! call this trait; the composition
//! root (eukhe-cli) implements it over the real settings manager. Every
//! getter reads the effective settings with the TS default; every setter
//! persists the global scope (TS `markModified` + `save`).

use anyhow::Result;
use eukhe_types::model_roles::ModelRole;

/// Where a model role's value comes from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModelRoleSource {
    /// No file sets it: the role's fallback applies.
    Unset,
    /// The global settings (`settings.json` or `config.cfg`).
    Global,
    /// The project's settings (they win over the global ones).
    Project,
}

/// A model role's value as the settings resolve it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModelRoleValue {
    /// The selector that is set (`provider/id`, `local/<id>`); `None`
    /// when unset.
    pub selector: Option<String>,
    pub source: ModelRoleSource,
    /// What runs while the role is unset (`session model`, the model a
    /// local role's chain picks, ...).
    pub fallback: String,
    /// The reasoning effort of a role that keeps one (`memory`).
    pub thinking: Option<eukhe_types::ai::ModelThinkingLevel>,
}

/// A local catalog model that serves a role.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalRoleModel {
    /// The id after `local/` in the selector.
    pub id: String,
    pub title: String,
    /// Its files are downloaded (`eukhe tiny-models download`).
    pub installed: bool,
}

/// What a local role accepts: its catalog models, and whether a provider
/// (text) model serves it too.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct LocalRoleChoices {
    pub models: Vec<LocalRoleModel>,
    pub takes_remote: bool,
}

pub trait ClientSettings: Send + Sync {
    /// `theme` (TS `getTheme`/`setTheme`).
    fn theme(&self) -> Option<String>;
    /// Persists `theme` to the global scope.
    ///
    /// # Errors
    ///
    /// Returns `Err` when opening or persisting the settings
    /// store fails.
    fn set_theme(&self, theme: &str) -> Result<()>;
    /// Where theme names resolve (TS `setRegisteredThemes` from the
    /// resource loader + `getCustomThemesDir`), re-resolved per call so
    /// `/reload` and `/settings` see edited settings and files.
    fn theme_sources(&self) -> eukhe_theme::ThemeSources;
    /// Record a theme warning in the agent log (the chat shows it too).
    fn log_theme_warning(&self, message: &str);
    /// Record a frame the off-screen check rejected in the agent log (the
    /// screen shows a toast too).
    fn log_render_error(&self, message: &str);
    /// `terminal.showImages` (TS default true).
    fn show_images(&self) -> bool;
    /// Persists `terminal.showImages` to the global scope.
    ///
    /// # Errors
    ///
    /// Returns `Err` when opening or persisting the settings
    /// store fails.
    fn set_show_images(&self, enabled: bool) -> Result<()>;
    /// `terminal.clearOnShrink` (TS default false).
    fn clear_on_shrink(&self) -> bool;
    /// Persists `terminal.clearOnShrink` to the global scope.
    ///
    /// # Errors
    ///
    /// Returns `Err` when opening or persisting the settings
    /// store fails.
    fn set_clear_on_shrink(&self, enabled: bool) -> Result<()>;
    /// `terminal.showTerminalProgress` (TS default false).
    fn show_terminal_progress(&self) -> bool;
    /// Persists `terminal.showTerminalProgress` to the global scope.
    ///
    /// # Errors
    ///
    /// Returns `Err` when opening or persisting the settings
    /// store fails.
    fn set_show_terminal_progress(&self, enabled: bool) -> Result<()>;
    /// `terminal.showSpeed` (default true): the status line's generation
    /// speed (prefill, decode, and the summary of the last response).
    fn show_speed(&self) -> bool {
        true
    }
    /// `terminal.pinnedAgents` (default `collapsed`): the pinned agents
    /// block above the composer.
    fn pinned_agents(&self) -> crate::agents_panel::PinnedAgents {
        crate::agents_panel::PinnedAgents::Collapsed
    }
    /// `terminal.stuckAfterSecs` (default 60; 0 is off): seconds a running
    /// agent may go without a word before the block shows it as quiet.
    fn stuck_after_secs(&self) -> u64 {
        crate::agents_panel::DEFAULT_STUCK_AFTER_SECS
    }
    /// `terminal.fullscreen` (default true: the alternate screen; an
    /// explicit false runs inline).
    fn fullscreen(&self) -> bool;
    /// Persists `terminal.fullscreen` to the global scope.
    ///
    /// # Errors
    ///
    /// Returns `Err` when opening or persisting the settings
    /// store fails.
    fn set_fullscreen(&self, enabled: bool) -> Result<()>;
    /// `images.autoResize` (TS default true).
    fn image_auto_resize(&self) -> bool;
    /// Persists `images.autoResize` to the global scope.
    ///
    /// # Errors
    ///
    /// Returns `Err` when opening or persisting the settings
    /// store fails.
    fn set_image_auto_resize(&self, enabled: bool) -> Result<()>;
    /// `images.blockImages` (TS default false).
    fn block_images(&self) -> bool;
    /// Persists `images.blockImages` to the global scope.
    ///
    /// # Errors
    ///
    /// Returns `Err` when opening or persisting the settings
    /// store fails.
    fn set_block_images(&self, blocked: bool) -> Result<()>;
    /// `imageModel` (TS `getImageModel`: "provider/model-id" or a bare id;
    /// unset by default). Read-only for the paste-time hint that names the
    /// setting when the session model lacks image input.
    fn image_model(&self) -> Option<String>;
    /// The value of model role `role` as the settings resolve it;
    /// `session_model` (`provider/id`, empty: none) is the session's model
    /// the role's fallback may name. `None` without a settings store.
    fn model_role(&self, _role: ModelRole, _session_model: &str) -> Option<ModelRoleValue> {
        None
    }
    /// Persists `selector` (`provider/id`, or `local/<id>` for a local
    /// role) as model role `role` globally (the `/set --global` path),
    /// with `thinking` for a role that takes a reasoning effort. The
    /// `chat` role switches through the session, never here.
    ///
    /// # Errors
    ///
    /// Returns `Err` for the `chat` role, a role that takes no thinking
    /// given one, or when opening or persisting the settings store fails.
    fn set_model_role(
        &self,
        _role: ModelRole,
        _selector: &str,
        _thinking: Option<eukhe_types::ai::ModelThinkingLevel>,
    ) -> Result<()> {
        anyhow::bail!("Model role settings are unavailable")
    }
    /// Unsets model role `role` in the global settings: the role falls
    /// back to its default chain.
    ///
    /// # Errors
    ///
    /// Returns `Err` for the `chat` role (the session always holds a
    /// model), or when opening or persisting the settings store fails.
    fn clear_model_role(&self, _role: ModelRole) -> Result<()> {
        anyhow::bail!("Model role settings are unavailable")
    }
    /// What local role `role` accepts (nothing for a role outside the
    /// local group).
    fn local_role_choices(&self, _role: ModelRole) -> LocalRoleChoices {
        LocalRoleChoices::default()
    }
    /// `enableSkillCommands` (TS default true).
    fn enable_skill_commands(&self) -> bool;
    /// Persists `enableSkillCommands` to the global scope.
    ///
    /// # Errors
    ///
    /// Returns `Err` when opening or persisting the settings
    /// store fails.
    fn set_enable_skill_commands(&self, enabled: bool) -> Result<()>;
    /// `enableBuiltinSkills` (TS default true).
    fn enable_builtin_skills(&self) -> bool;
    /// Persists `enableBuiltinSkills` to the global scope.
    ///
    /// # Errors
    ///
    /// Returns `Err` when opening or persisting the settings
    /// store fails.
    fn set_enable_builtin_skills(&self, enabled: bool) -> Result<()>;
    /// `showHardwareCursor` (TS default false).
    fn show_hardware_cursor(&self) -> bool;
    /// Persists `showHardwareCursor` to the global scope.
    ///
    /// # Errors
    ///
    /// Returns `Err` when opening or persisting the settings
    /// store fails.
    fn set_show_hardware_cursor(&self, enabled: bool) -> Result<()>;
    /// `terminal.streamPace.minChars` (default 2; 0 reads as 1) and
    /// `terminal.streamPace.lag` (default 3): how fast streamed text
    /// reaches the screen.
    fn stream_pace(&self) -> crate::pace::PaceRate;
    /// `editorPaddingX` (TS default 0).
    fn editor_padding_x(&self) -> u64;
    /// Persists `editorPaddingX` to the global scope.
    ///
    /// # Errors
    ///
    /// Returns `Err` when opening or persisting the settings
    /// store fails.
    fn set_editor_padding_x(&self, padding: u64) -> Result<()>;
    /// `autocompleteMaxVisible` (TS default 5).
    fn autocomplete_max_visible(&self) -> u64;
    /// Persists `autocompleteMaxVisible` to the global scope.
    ///
    /// # Errors
    ///
    /// Returns `Err` when opening or persisting the settings
    /// store fails.
    fn set_autocomplete_max_visible(&self, max_visible: u64) -> Result<()>;
    /// `quietStartup` (TS default false).
    fn quiet_startup(&self) -> bool;
    /// Persists `quietStartup` to the global scope.
    ///
    /// # Errors
    ///
    /// Returns `Err` when opening or persisting the settings
    /// store fails.
    fn set_quiet_startup(&self, quiet: bool) -> Result<()>;
    /// `idleEvictionMinutes` wire form (a number or `off`).
    fn idle_eviction_minutes(&self) -> String;
    /// Persists the `idleEvictionMinutes` wire form to the global scope.
    ///
    /// # Errors
    ///
    /// Returns `Err` when opening or persisting the settings
    /// store fails.
    fn set_idle_eviction_minutes(&self, value: &str) -> Result<()>;
    /// `markdown.mermaid` (`off`/`final`/`streaming`).
    fn mermaid_rendering_mode(&self) -> String;
    /// Persists `markdown.mermaid` to the global scope.
    ///
    /// # Errors
    ///
    /// Returns `Err` when opening or persisting the settings
    /// store fails.
    fn set_mermaid_rendering_mode(&self, mode: &str) -> Result<()>;
    /// `workflow.size` (`small`/`medium`/`large`): the default size of a
    /// `/dynamic-workflow` run.
    fn workflow_size(&self) -> String;
    /// Persists `workflow.size` to the global scope.
    ///
    /// # Errors
    ///
    /// Returns `Err` for an unknown size, or when opening or persisting
    /// the settings store fails.
    fn set_workflow_size(&self, size: &str) -> Result<()>;
    /// `treeFilterMode` (`default`/`no-tools`/`user-only`/`labeled-only`/`all`).
    fn tree_filter_mode(&self) -> String;
    /// Persists `treeFilterMode` to the global scope.
    ///
    /// # Errors
    ///
    /// Returns `Err` when opening or persisting the settings
    /// store fails.
    fn set_tree_filter_mode(&self, mode: &str) -> Result<()>;
    /// `defaultServiceTier` (TS `getDefaultServiceTier`, default
    /// "default"): the wire name of the persisted default tier -- the
    /// settings row's bound value.
    fn default_service_tier(&self) -> String;
    /// TS `settingsManager.setDefaultServiceTier` -- persists the wire name.
    ///
    /// # Errors
    ///
    /// Returns `Err` when the tier name is not a known service tier or
    /// opening or persisting the settings store fails.
    fn set_default_service_tier(&self, tier: &str) -> Result<()>;
    /// `factory.enabled` (the agent factory's opt-in gate; unset reads
    /// as disabled).
    fn factory_enabled(&self) -> bool;
    /// Persists `factory.enabled` to the global scope -- the same shared
    /// settings key the daemon's `factory_activity` lane advertisement
    /// and the kernel's factory gate read.
    ///
    /// # Errors
    ///
    /// Returns an error when opening or persisting the settings store
    /// fails.
    fn set_factory_enabled(&self, enabled: bool) -> Result<()>;
    /// `chatDetail` (`overview`/`details`/`all`; TS #2709 default
    /// `details`): the conversation-detail level the chat starts at.
    /// `chatDetail` (`overview`/`details`/`all`; the default reads as
    /// `overview`, the collapse mode): the conversation-detail level the
    /// chat starts at.
    fn chat_detail(&self) -> String;
    /// Persists `chatDetail` to the global scope (TS #2709: the Ctrl+O
    /// cycle saves the level; every later chat re-reads it).
    ///
    /// # Errors
    ///
    /// Returns `Err` when opening or persisting the settings
    /// store fails.
    fn set_chat_detail(&self, detail: &str) -> Result<()>;
    /// `warnings.anthropicExtraUsage` (TS default true).
    fn warnings_anthropic_extra_usage(&self) -> bool;
    /// Persists `warnings.anthropicExtraUsage` to the global scope.
    ///
    /// # Errors
    ///
    /// Returns `Err` when opening or persisting the settings
    /// store fails.
    fn set_warnings_anthropic_extra_usage(&self, enabled: bool) -> Result<()>;
}
