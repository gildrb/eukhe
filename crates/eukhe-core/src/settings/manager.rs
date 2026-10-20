//! `SettingsManager`: loads global + project settings, merges them, builds
//! the cvar layers over them (`settings::cvar`, `settings::cfg`), and
//! writes back only what this session changed.

use std::sync::Arc;

use anyhow::Result;
use eukhe_types::cvar::{Aliases, Binds, Command};

use super::cfg::{config_layer, replace_sets, run_script, CONFIG_CFG};
use super::cvar::{
    document_sets, registry, value_text, AgentLayer, CvarError, CvarWriteError, Cvars, LayerKind,
    Sets, Target,
};
use super::load::from_value_lenient;
use super::merge::{deep_merge, migrate};
use super::storage::{SettingsScope, SettingsStorage};
use super::trust::{apply_project_trust, effective_project, ProjectTrust};
use super::types::{
    MemorySettings, QueueModeSetting, Settings, ThinkingLevelSetting, TransportSetting,
};

pub const RECENT_MODELS_LIMIT: usize = 20;

#[derive(Debug, Clone)]
pub struct SettingsError {
    pub scope: SettingsScope,
    pub message: String,
}

pub struct SettingsManager {
    storage: Arc<dyn SettingsStorage>,
    global: Settings,
    /// The project scope as its document holds it (every key): the base
    /// project-scope edits rewrite arrays from, never an input to the
    /// effective settings.
    project_document: Settings,
    /// The project scope that applies: the document minus what the
    /// project's trust withholds (see `settings::trust`).
    project: Settings,
    project_trust: ProjectTrust,
    merged: Settings,
    /// The values every getter reads: the config layer (`settings.json`,
    /// then `config.cfg`) and the agent family [`Self::set_family`] gave.
    cvars: Cvars,
    /// The aliases of the config cfg files.
    aliases: Aliases,
    errors: Vec<SettingsError>,
    /// The raw global document (the parsed JSON before the lenient field
    /// load). The daemon model allowlist distinguishes an ABSENT
    /// `allowedModels` key (unrestricted) from a PRESENT-but-malformed one
    /// (the security gate fails closed) — the typed `Settings` drops both
    /// to `None`, so the raw value is the only witness.
    global_raw: Option<serde_json::Value>,
    /// Load failures per scope; a scope whose file failed to parse is never
    /// written back (the TS `save` guard against clobbering bad settings).
    global_load_error: Option<String>,
    project_load_error: Option<String>,
}

impl SettingsManager {
    /// Load global + project settings from a storage backend.
    pub fn from_storage(storage: Arc<dyn SettingsStorage>) -> Self {
        Self::load(storage, Vec::new(), Vec::new())
    }

    /// The one load path ([`Self::from_storage`] and [`Self::reload`]):
    /// both scopes, the project trust decision, the merge of the global
    /// scope with the project scope that trust lets apply, and the config
    /// layer of cvars over it with `family` on top.
    fn load(
        storage: Arc<dyn SettingsStorage>,
        mut errors: Vec<SettingsError>,
        family: Vec<AgentLayer>,
    ) -> Self {
        let (global, global_raw, global_load_error) =
            load_scope(storage.as_ref(), SettingsScope::Global, &mut errors);
        let (project_document, _, project_load_error) =
            load_scope(storage.as_ref(), SettingsScope::Project, &mut errors);
        let (project, mut project_trust) =
            apply_project_trust(storage.as_ref(), &global, &project_document, &mut errors);
        let merged = deep_merge(&global, &project);
        let layer = config_layer(storage.as_ref(), &global, &merged, project_trust.level);
        errors.extend(layer.errors);
        for key in layer.withheld {
            if !project_trust.ignored_keys.contains(&key) {
                project_trust.ignored_keys.push(key);
            }
        }
        if let Some(message) = project_trust.warning(&[]) {
            errors.push(SettingsError {
                scope: SettingsScope::Project,
                message,
            });
        }
        let mut cvars = layer.cvars;
        cvars.set_family(family);
        Self {
            storage,
            global,
            project_document,
            project,
            project_trust,
            merged,
            cvars,
            aliases: layer.aliases,
            errors,
            global_raw,
            global_load_error,
            project_load_error,
        }
    }

    /// File-backed manager (agentDir + cwd/.eukhe).
    pub fn create(
        cwd: impl AsRef<std::path::Path>,
        agent_dir: impl AsRef<std::path::Path>,
    ) -> Self {
        let cwd = std::path::PathBuf::from(cwd.as_ref());
        let agent_dir = std::path::PathBuf::from(agent_dir.as_ref());
        let storage: Arc<dyn SettingsStorage> =
            Arc::new(super::storage::FileSettingsStorage::new(cwd, agent_dir));
        Self::from_storage(storage)
    }

    /// In-memory manager (tests, embedded hosts).
    #[must_use]
    pub fn in_memory(initial: &Settings) -> Self {
        let storage: Arc<dyn SettingsStorage> =
            Arc::new(super::storage::InMemorySettingsStorage::default());
        let content = serde_json::to_string_pretty(&initial).unwrap_or_default();
        storage
            .with_lock(SettingsScope::Global, &mut |current| {
                let _ = current;
                Some(content.clone())
            })
            .ok();
        Self::from_storage(storage)
    }

    /// Effective (global + project) settings.
    #[must_use]
    pub fn settings(&self) -> &Settings {
        &self.merged
    }

    #[must_use]
    pub fn global_settings(&self) -> &Settings {
        &self.global
    }

    /// The raw global document (post-migration, pre-lenient-load value);
    /// `None` when the scope has no document or it failed to parse (the
    /// load error covers the latter).
    #[must_use]
    pub fn global_raw(&self) -> Option<&serde_json::Value> {
        self.global_raw.as_ref()
    }

    /// The project scope that applies (trust-filtered; see
    /// `settings::trust`).
    #[must_use]
    pub fn project_settings(&self) -> &Settings {
        &self.project
    }

    /// The project scope exactly as its document holds it, for edits that
    /// rewrite a project array; an untrusted project's withheld keys are
    /// still here, so the edit never drops them.
    #[must_use]
    pub fn project_document(&self) -> &Settings {
        &self.project_document
    }

    /// This load's project trust decision and what it withheld.
    #[must_use]
    pub fn project_trust(&self) -> &ProjectTrust {
        &self.project_trust
    }

    /// The global document's read/parse failure, if any (setting-level
    /// errors such as a relative `trustedProjects` entry are not load
    /// failures).
    #[must_use]
    pub fn global_load_error(&self) -> Option<&str> {
        self.global_load_error.as_deref()
    }

    #[must_use]
    pub fn errors(&self) -> &[SettingsError] {
        &self.errors
    }

    /// Take and clear the recorded settings errors (warnings are printed once
    /// by the CLI commands that surface them).
    pub fn drain_errors(&mut self) -> Vec<SettingsError> {
        std::mem::take(&mut self.errors)
    }

    /// Reload both scopes and the cfg files from storage; the family set by
    /// [`Self::set_family`] stays.
    ///
    /// # Errors
    ///
    /// The current implementation never returns `Err`; scope load problems
    /// are recorded as load errors on the manager instead.
    pub fn reload(&mut self) -> Result<()> {
        let errors = std::mem::take(&mut self.errors);
        let family = self.cvars.family().to_vec();
        *self = Self::load(Arc::clone(&self.storage), errors, family);
        Ok(())
    }

    /// The values the getters read.
    #[must_use]
    pub fn cvars(&self) -> &Cvars {
        &self.cvars
    }

    /// The aliases of the config cfg files.
    #[must_use]
    pub fn aliases(&self) -> &Aliases {
        &self.aliases
    }

    /// The agent family over the config layer (root first, the agent
    /// itself last); it survives [`Self::reload`] and every setter.
    pub fn set_family(&mut self, family: Vec<AgentLayer>) {
        self.cvars.set_family(family);
    }

    /// A new agent's profile: the global-scope cfg `files` in order
    /// (`subagent.cfg`, `agents/<name>.cfg`) run as profile commands over
    /// this agent's values. Returns the profile sets, the aliases (this
    /// manager's plus the files'), and what failed (an absent file is
    /// skipped; a file that cannot be read is a failure).
    #[must_use]
    pub fn read_profile(&self, files: &[String]) -> (Sets, Aliases, Vec<SettingsError>) {
        let mut agent = self.cvars.child();
        let mut aliases = self.aliases.clone();
        let mut errors = Vec::new();
        for file in files {
            match self.storage.read_cfg(SettingsScope::Global, file) {
                Ok(Some(text)) => errors.extend(run_script(
                    &mut agent,
                    Target::Profile,
                    &text,
                    &mut aliases,
                    SettingsScope::Global,
                    file,
                )),
                Ok(None) => {}
                Err(error) => errors.push(SettingsError {
                    scope: SettingsScope::Global,
                    message: format!("{file}: {error:#}"),
                }),
            }
        }
        (agent.agent().profile.clone(), aliases, errors)
    }

    /// Record `errors` with the load's errors (an agent profile's, which
    /// the session reads over this manager).
    pub fn push_errors(&mut self, errors: impl IntoIterator<Item = SettingsError>) {
        self.errors.extend(errors);
    }

    /// The explicit global command (`/set --global`): run the `set` and
    /// `toggle` commands over the global layer alone (the global
    /// `settings.json`, then the global `config.cfg`; a project never
    /// decides what a global toggle flips) and write each resulting set
    /// into the global `config.cfg`, replacing the line that set the cvar
    /// before. The read, the run, and the write hold the file's lock; then
    /// the config layer is rebuilt.
    ///
    /// # Errors
    ///
    /// The first command that does not apply (then nothing is written); the
    /// cfg file cannot be locked, read, or written.
    pub fn run_global(&mut self, commands: &[Command]) -> Result<(), CvarWriteError> {
        let registry = registry();
        let global = serde_json::to_value(&self.global).unwrap_or(serde_json::Value::Null);
        let mut outcome: Result<(), CvarError> = Ok(());
        self.storage
            .with_cfg_lock(SettingsScope::Global, CONFIG_CFG, &mut |current| {
                let text = current.unwrap_or_default();
                let mut layer = Cvars::new(registry, document_sets(registry, &global, &global));
                let mut aliases = Aliases::default();
                // The file's own failures were recorded at load.
                let _recorded_at_load = run_script(
                    &mut layer,
                    Target::Config,
                    &text,
                    &mut aliases,
                    SettingsScope::Global,
                    CONFIG_CFG,
                );
                let before = layer.config().0.len();
                outcome = match layer
                    .execute(
                        Target::Config,
                        commands,
                        &mut aliases,
                        &mut Binds::default(),
                    )
                    .into_iter()
                    .next()
                {
                    Some(error) => Err(error),
                    None => Ok(()),
                };
                outcome
                    .is_ok()
                    .then(|| replace_sets(&text, &Sets(layer.config().0[before..].to_vec())))
            })
            .map_err(|error| CvarWriteError::Io(format!("{error:#}")))?;
        outcome.map_err(CvarWriteError::Cvar)?;
        self.rebuild_cvars();
        Ok(())
    }

    /// Write `sets` into agent `name`'s profile (`agents/<name>.cfg` in
    /// the global scope): each replaces the line of its cvar, every other
    /// line stays. The read and the write hold the file's lock.
    ///
    /// # Errors
    ///
    /// A set that is not a valid agent set (an undeclared or Global cvar,
    /// a bad value); a name that is not a plain file name; the cfg file
    /// cannot be locked, read, or written.
    pub fn write_agent_cfg(&mut self, name: &str, sets: &Sets) -> Result<(), CvarWriteError> {
        if name.is_empty() || name.contains(['/', '\\']) || name == "." || name == ".." {
            return Err(CvarWriteError::Io(format!("`{name}` is not an agent name")));
        }
        for set in &sets.0 {
            self.cvars
                .check(LayerKind::Agent, &set.id, &value_text(&set.value))
                .map_err(CvarWriteError::Cvar)?;
        }
        self.storage
            .with_cfg_lock(
                SettingsScope::Global,
                &format!("{}/{name}.cfg", super::PROFILE_DIR),
                &mut |current| Some(replace_sets(&current.unwrap_or_default(), sets)),
            )
            .map_err(|error| CvarWriteError::Io(format!("{error:#}")))
    }

    /// Rebuild the merge and the config layer after a settings edit; the
    /// family stays, and the config files' errors (recorded at load) are
    /// not recorded again.
    fn rebuild_cvars(&mut self) {
        self.merged = deep_merge(&self.global, &self.project);
        let layer = config_layer(
            self.storage.as_ref(),
            &self.global,
            &self.merged,
            self.project_trust.level,
        );
        let family = self.cvars.family().to_vec();
        self.cvars = layer.cvars;
        self.cvars.set_family(family);
        self.aliases = layer.aliases;
    }

    /// Mutable global settings for the setters in sibling modules (the
    /// TS setters mutate `globalSettings` then save).
    pub(crate) fn global_mut(&mut self) -> &mut Settings {
        &mut self.global
    }

    /// Persist the global scope (sibling-module setters share this).
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings file cannot be written.
    pub(crate) fn save_global_scope(&mut self) -> Result<()> {
        self.save_global()
    }

    // -- persisted setters --------------------------------------------------

    /// `defaultModel` + `defaultProvider` setter (the model switch's
    /// combined write).
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings file cannot be written.
    pub fn set_default_model_and_provider(&mut self, provider: &str, model: &str) -> Result<()> {
        self.global.default_provider = Some(provider.to_string());
        self.global.default_model = Some(model.to_string());
        self.record_model_use(provider, model);
        self.save_global()
    }

    /// Persist `memory.model` globally as an exact `provider/model-id`
    /// selector without replacing the compactor's other memory settings.
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings file cannot be written.
    pub fn set_memory_model(&mut self, provider: &str, model_id: &str) -> Result<()> {
        self.global
            .memory
            .get_or_insert_with(MemorySettings::default)
            .model = Some(format!("{provider}/{model_id}"));
        self.save_global()
    }
    /// Record a model use at the front of `recentModels` (capped at 20).
    pub fn record_model_use(&mut self, provider: &str, model: &str) {
        let key = format!("{provider}/{model}");
        let mut recent: Vec<String> = vec![key];
        for existing in self.global.recent_models.iter().flatten() {
            if existing != &recent[0] {
                recent.push(existing.clone());
            }
        }
        recent.truncate(RECENT_MODELS_LIMIT);
        self.global.recent_models = Some(recent);
    }

    /// `steeringMode` setter.
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings file cannot be written.
    pub fn set_steering_mode(&mut self, mode: QueueModeSetting) -> Result<()> {
        self.global.steering_mode = Some(mode);
        self.save_global()
    }

    /// `followUpMode` setter.
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings file cannot be written.
    pub fn set_follow_up_mode(&mut self, mode: QueueModeSetting) -> Result<()> {
        self.global.follow_up_mode = Some(mode);
        self.save_global()
    }

    /// `theme` setter.
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings file cannot be written.
    pub fn set_theme(&mut self, theme: String) -> Result<()> {
        self.global.theme = Some(theme);
        self.save_global()
    }

    /// `defaultThinkingLevel` setter.
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings file cannot be written.
    pub fn set_default_thinking_level(&mut self, level: ThinkingLevelSetting) -> Result<()> {
        self.global.default_thinking_level = Some(level);
        self.save_global()
    }

    /// TS `setRetryEnabled`: the auto-retry toggle the provider retry
    /// policy reads (`retry.enabled`).
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings file cannot be written.
    pub fn set_retry_enabled(&mut self, enabled: bool) -> Result<()> {
        self.global
            .retry
            .get_or_insert_with(Default::default)
            .enabled = Some(enabled);
        self.save_global()
    }

    /// TS `setCompactionEnabled`: the auto-compaction toggle
    /// (`compaction.enabled` in the global settings file). The connection
    /// state's `autoCompactionEnabled` is this value in TS, so a daemon
    /// restart re-seeds the flag from the persisted setting.
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings file cannot be written.
    pub fn set_compaction_enabled(&mut self, enabled: bool) -> Result<()> {
        self.global
            .compaction
            .get_or_insert_with(Default::default)
            .enabled = Some(enabled);
        self.save_global()
    }

    /// `transport` setter.
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings file cannot be written.
    pub fn set_transport(&mut self, transport: TransportSetting) -> Result<()> {
        self.global.transport = Some(transport);
        self.save_global()
    }

    /// `rlmMaxDepth` setter.
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings file cannot be written.
    pub fn set_rlm_max_depth(&mut self, depth: u64) -> Result<()> {
        self.global.rlm_max_depth = Some(depth);
        self.save_global()
    }

    /// `onboardingShown` setter.
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings file cannot be written.
    pub fn set_onboarding_shown(&mut self, shown: bool) -> Result<()> {
        self.global.onboarding_shown = Some(shown);
        self.save_global()
    }

    /// Replace the `packages` array in the global settings file.
    pub fn set_packages(&mut self, packages: Vec<serde_json::Value>) {
        self.global.packages = Some(packages.clone());
        self.persist_scope_field(
            SettingsScope::Global,
            "packages",
            &serde_json::Value::Array(packages),
        );
        self.rebuild_cvars();
    }

    /// Replace the `packages` array in the project settings file.
    pub fn set_project_packages(&mut self, packages: Vec<serde_json::Value>) {
        self.project_document.packages = Some(packages.clone());
        self.persist_scope_field(
            SettingsScope::Project,
            "packages",
            &serde_json::Value::Array(packages),
        );
        self.refresh_project_scope();
    }

    /// Replace one resource-path array (`skills`/`prompts`/`themes`) in the
    /// global settings file (TS `setSkillPaths` & friends).
    pub fn set_global_resource_array(&mut self, field: &str, values: Vec<String>) {
        let array: Vec<serde_json::Value> =
            values.into_iter().map(serde_json::Value::String).collect();
        match field {
            "skills" => self.global.skills = Some(strings(&array)),
            "prompts" => self.global.prompts = Some(strings(&array)),
            "themes" => self.global.themes = Some(strings(&array)),
            _ => return,
        }
        self.persist_scope_field(
            SettingsScope::Global,
            field,
            &serde_json::Value::Array(array),
        );
        self.rebuild_cvars();
    }

    /// Replace one resource-path array in the project settings file (TS
    /// `setProjectSkillPaths` & friends).
    pub fn set_project_resource_array(&mut self, field: &str, values: Vec<String>) {
        let array: Vec<serde_json::Value> =
            values.into_iter().map(serde_json::Value::String).collect();
        match field {
            "skills" => self.project_document.skills = Some(strings(&array)),
            "prompts" => self.project_document.prompts = Some(strings(&array)),
            "themes" => self.project_document.themes = Some(strings(&array)),
            _ => return,
        }
        self.persist_scope_field(
            SettingsScope::Project,
            field,
            &serde_json::Value::Array(array),
        );
        self.refresh_project_scope();
    }

    /// Re-derive the applying project scope and the merge after a project
    /// document edit (the trust decision stands).
    fn refresh_project_scope(&mut self) {
        (self.project, _) = effective_project(&self.project_document, self.project_trust.level);
        self.rebuild_cvars();
    }

    /// Write one field into a scope's file, merging with the current on-disk
    /// document so concurrently-added fields survive. Settings failures are
    /// recorded as warnings, never thrown (the TS save contract).
    fn persist_scope_field(
        &mut self,
        scope: SettingsScope,
        field: &str,
        value: &serde_json::Value,
    ) {
        let load_error = match scope {
            SettingsScope::Global => self.global_load_error.clone(),
            SettingsScope::Project => self.project_load_error.clone(),
        };
        if let Some(message) = load_error {
            let label = match scope {
                SettingsScope::Global => "Global",
                SettingsScope::Project => "Project",
            };
            self.errors.push(SettingsError {
                scope,
                message: format!(
                    "{label} settings not saved: settings file failed to parse: {message}"
                ),
            });
            return;
        }
        let result = self.storage.with_lock(scope, &mut |current| {
            let mut map: serde_json::Map<String, serde_json::Value> = current
                .and_then(|content| serde_json::from_str::<serde_json::Value>(&content).ok())
                .and_then(|value| match value {
                    serde_json::Value::Object(mut map) => {
                        super::merge::migrate(&mut map);
                        Some(map)
                    }
                    _ => None,
                })
                .unwrap_or_default();
            map.insert(field.to_string(), value.clone());
            serde_json::to_string_pretty(&serde_json::Value::Object(map)).ok()
        });
        if let Err(error) = result {
            self.errors.push(SettingsError {
                scope,
                message: error.to_string(),
            });
        }
    }

    /// TS `setDefaultServiceTier`: the persisted default a fresh session
    /// starts from; the stored string is the same vocabulary
    /// `get_default_service_tier` parses.
    ///
    /// # Errors
    ///
    /// Returns an error when the global settings file cannot be written.
    pub fn set_default_service_tier(&mut self, tier: eukhe_types::ai::ServiceTier) -> Result<()> {
        use eukhe_types::ai::ServiceTier;
        let name = match tier {
            ServiceTier::Auto => "auto",
            ServiceTier::Default => "default",
            ServiceTier::Flex => "flex",
            ServiceTier::Scale => "scale",
            ServiceTier::Priority => "priority",
        };
        self.global.default_service_tier = Some(name.to_string());
        self.save_global()
    }

    // -- persistence ---------------------------------------------------------

    /// Write the global scope back (project scope is host-written, not
    /// user-set in this port), then re-derive the effective settings. A
    /// global document that failed to parse is never written: the setter
    /// fails and the file stays as the user left it.
    fn save_global(&mut self) -> Result<()> {
        if let Some(message) = self.global_load_error.clone() {
            let message =
                format!("Global settings not saved: settings file failed to parse: {message}");
            self.errors.push(SettingsError {
                scope: SettingsScope::Global,
                message: message.clone(),
            });
            return Err(anyhow::anyhow!(message));
        }
        let content = serde_json::to_string_pretty(&self.global)?;
        self.storage
            .with_lock(SettingsScope::Global, &mut |current| {
                let _ = current;
                Some(content.clone())
            })?;
        self.rebuild_cvars();
        Ok(())
    }
}

/// Resolved `idleEvictionMinutes`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IdleEviction {
    Minutes(u64),
    Off,
}

/// Resolved session-archiving settings: the age rule (archive sessions
/// untouched for `max_age_days` days) and the count rule (keep the newest
/// `max_sessions` sessions). Each field is `None` when its rule is off.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SessionArchivePolicy {
    pub max_age_days: Option<u64>,
    pub max_sessions: Option<usize>,
}

fn strings(array: &[serde_json::Value]) -> Vec<String> {
    array
        .iter()
        .filter_map(|value| value.as_str().map(str::to_string))
        .collect()
}

/// One loaded scope: the leniently-parsed settings, the migrated raw
/// document (the value before the lenient field load — the only witness
/// for a PRESENT-but-malformed known field, which the lenient load drops),
/// and the load error (`Some` when the scope's document exists but could
/// not be read or parsed).
#[allow(clippy::type_complexity)]
fn load_scope(
    storage: &dyn SettingsStorage,
    scope: SettingsScope,
    errors: &mut Vec<SettingsError>,
) -> (Settings, Option<serde_json::Value>, Option<String>) {
    let mut load_error: Option<String> = None;
    // The pure-read arm: a locked protocol read on any cache miss, the
    // process-cached copy on a hit (see `SettingsStorage::read`).
    let content = match storage.read(scope) {
        Ok(content) => content,
        Err(error) => {
            let message = error.to_string();
            errors.push(SettingsError {
                scope,
                message: message.clone(),
            });
            return (Settings::default(), None, Some(message));
        }
    };
    let Some(content) = content else {
        return (Settings::default(), None, None);
    };
    let value: serde_json::Value = match serde_json::from_str(&content) {
        Ok(value) => value,
        Err(error) => {
            load_error = Some(error.to_string());
            serde_json::Value::Null
        }
    };
    if let Some(message) = load_error {
        errors.push(SettingsError {
            scope,
            message: message.clone(),
        });
        return (Settings::default(), None, Some(message));
    }
    // Migrate the raw document, then load leniently.
    let migrated = match value {
        serde_json::Value::Object(mut map) => {
            migrate(&mut map);
            serde_json::Value::Object(map)
        }
        other => other,
    };
    (from_value_lenient(&migrated), Some(migrated), None)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::settings::types::{MarkdownSettings, StreamPaceSettings, TerminalSettings};

    #[test]
    fn in_memory_loads_merges_and_saves() {
        let mut manager = SettingsManager::in_memory(&Settings::default());
        manager
            .set_default_model_and_provider("prime-inference", "z-ai/glm-5.3")
            .unwrap();
        assert_eq!(
            manager.get_default_provider().as_deref(),
            Some("prime-inference")
        );
        assert_eq!(manager.get_default_model().as_deref(), Some("z-ai/glm-5.3"));
        assert_eq!(
            manager.get_recent_models(),
            vec!["prime-inference/z-ai/glm-5.3".to_string()]
        );
        manager.reload().unwrap();
        assert_eq!(manager.get_default_model().as_deref(), Some("z-ai/glm-5.3"));
    }

    /// `factory.enabled` reads the GLOBAL scope only (the agent-dir
    /// document the kernel's factory gate and `set_factory_enabled` use):
    /// a project-scope override can never flip the gate out from under the
    /// kernel — a project `.eukhe/settings.json` with `enabled: true`
    /// leaves the factory disabled while the global setting says nothing
    /// (Macroscope review finding: the merged read could diverge the
    /// daemon's lane advertisement and the client's `/factory status`
    /// from what the kernel would do).
    #[test]
    fn factory_enabled_reads_the_global_scope_only() {
        let dir = tempfile::tempdir().unwrap();
        let cwd = dir.path().join("cwd");
        let agent_dir = dir.path().join("agent");
        std::fs::create_dir_all(cwd.join(".eukhe")).unwrap();
        std::fs::create_dir_all(&agent_dir).unwrap();
        std::fs::write(
            cwd.join(".eukhe/settings.json"),
            r#"{ "factory": { "enabled": true } }"#,
        )
        .unwrap();

        let mut manager = SettingsManager::create(&cwd, &agent_dir);
        assert!(
            !manager.get_factory_enabled(),
            "a project-scope override never enables the gate"
        );

        manager
            .set_factory_enabled(true)
            .expect("set factory enabled");
        assert!(manager.get_factory_enabled());
        let content =
            std::fs::read_to_string(agent_dir.join("settings.json")).expect("global file");
        assert!(
            content.contains(r#""enabled": true"#),
            "the write lands in the global document the kernel gate reads: {content}"
        );

        manager
            .set_factory_enabled(false)
            .expect("set factory disabled");
        assert!(!manager.get_factory_enabled());
    }

    /// `terminal.fullscreen` survives eukhe rewriting the global document
    /// for another setting, and its own setter persists it.
    #[test]
    fn fullscreen_survives_an_unrelated_save_and_persists() {
        let dir = tempfile::tempdir().unwrap();
        let cwd = dir.path().join("cwd");
        let agent_dir = dir.path().join("agent");
        std::fs::create_dir_all(&cwd).unwrap();
        std::fs::create_dir_all(&agent_dir).unwrap();
        let path = agent_dir.join("settings.json");
        std::fs::write(&path, r#"{ "terminal": { "fullscreen": true } }"#).unwrap();
        let read = || -> serde_json::Value {
            serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap()
        };

        let mut manager = SettingsManager::create(&cwd, &agent_dir);
        assert!(manager.get_fullscreen());
        manager.set_theme("dark".to_string()).expect("set theme");
        assert_eq!(read()["terminal"]["fullscreen"], serde_json::json!(true));

        manager.set_fullscreen(false).expect("set fullscreen");
        assert!(!SettingsManager::create(&cwd, &agent_dir).get_fullscreen());
        assert_eq!(read()["terminal"]["fullscreen"], serde_json::json!(false));
    }

    #[test]
    fn code_block_indent_reads_markdown_settings_with_ts_default() {
        // `markdown.codeBlockIndent` (TS getCodeBlockIndent): absent -> the
        // TS default two spaces; set -> the configured string.
        let manager = SettingsManager::in_memory(&Settings::default());
        assert_eq!(manager.get_code_block_indent(), "  ");

        let settings = Settings {
            markdown: Some(MarkdownSettings {
                code_block_indent: Some("    ".to_string()),
                mermaid: None,
            }),
            ..Settings::default()
        };
        let manager = SettingsManager::in_memory(&settings);
        assert_eq!(manager.get_code_block_indent(), "    ");
    }

    /// `terminal.streamPace`: absent -> defaults (2, 3); set -> the values;
    /// a `minChars` of 0 reads as 1.
    #[test]
    fn stream_pace_reads_terminal_settings_with_defaults() {
        let read = |pace: Option<StreamPaceSettings>| {
            let manager = SettingsManager::in_memory(&Settings {
                terminal: Some(TerminalSettings {
                    stream_pace: pace,
                    ..TerminalSettings::default()
                }),
                ..Settings::default()
            });
            (
                manager.get_stream_pace_min_chars(),
                manager.get_stream_pace_lag(),
            )
        };
        let absent = SettingsManager::in_memory(&Settings::default());
        assert_eq!(
            (
                absent.get_stream_pace_min_chars(),
                absent.get_stream_pace_lag()
            ),
            (2, 3)
        );
        assert_eq!(read(None), (2, 3));
        assert_eq!(
            read(Some(StreamPaceSettings {
                min_chars: Some(5),
                lag: Some(0),
            })),
            (5, 0)
        );
        assert_eq!(
            read(Some(StreamPaceSettings {
                min_chars: Some(0),
                lag: None,
            })),
            (1, 3)
        );
        assert_eq!(
            read(Some(StreamPaceSettings {
                min_chars: Some(u64::MAX),
                lag: Some(u64::MAX),
            })),
            (usize::MAX, usize::MAX)
        );
    }

    /// TS #2709: the Ctrl+O level persists as the global `chatDetail`
    /// setting — a later run reads it back — and anything but the three
    /// TS levels reads as the `overview` startup default (the collapse
    /// mode; operator directive 2026-09-28).
    #[test]
    fn chat_detail_persists_the_chosen_level_with_the_startup_fallback() {
        let mut manager = SettingsManager::in_memory(&Settings::default());
        assert_eq!(manager.get_chat_detail(), "overview");
        manager.set_chat_detail("all").unwrap();
        assert_eq!(manager.get_chat_detail(), "all");
        manager.reload().unwrap();
        assert_eq!(
            manager.get_chat_detail(),
            "all",
            "the saved level survives a reload (a later chat re-reads it)"
        );
        manager.set_chat_detail("details").unwrap();
        assert_eq!(
            manager.get_chat_detail(),
            "details",
            "a saved details level reads back exactly (the Ctrl+O thinking reveal persists)"
        );
        manager.set_chat_detail("verbose").unwrap();
        assert_eq!(
            manager.get_chat_detail(),
            "overview",
            "an invalid value falls back to the startup default"
        );
    }

    /// The steering default is "all" (every queued steer co-delivers as
    /// ONE turn at the next tool-call boundary) with "one-at-a-time"
    /// selectable; the follow-up default stays "one-at-a-time".
    #[test]
    fn steering_mode_defaults_to_all_follow_ups_stay_one_at_a_time() {
        let mut manager = SettingsManager::in_memory(&Settings::default());
        assert_eq!(manager.get_steering_mode(), QueueModeSetting::All);
        assert_eq!(manager.get_follow_up_mode(), QueueModeSetting::OneAtATime);
        manager
            .set_steering_mode(QueueModeSetting::OneAtATime)
            .unwrap();
        assert_eq!(
            manager.get_steering_mode(),
            QueueModeSetting::OneAtATime,
            "the explicit one-at-a-time setting still selects one-per-turn"
        );
    }

    #[test]
    fn migrations_apply_on_load() {
        let storage: Arc<dyn SettingsStorage> =
            Arc::new(super::super::storage::InMemorySettingsStorage::default());
        storage
            .with_lock(SettingsScope::Global, &mut |_| {
                Some(r#"{ "queueMode": "all" }"#.into())
            })
            .unwrap();
        let manager = SettingsManager::from_storage(storage);
        assert_eq!(manager.get_steering_mode(), QueueModeSetting::All);
    }

    #[test]
    fn wrong_typed_fields_never_fail_load() {
        let storage: Arc<dyn SettingsStorage> =
            Arc::new(super::super::storage::InMemorySettingsStorage::default());
        storage
            .with_lock(SettingsScope::Global, &mut |_| {
                Some(r#"{ "defaultProvider": 42, "theme": "eukhe" }"#.into())
            })
            .unwrap();
        let manager = SettingsManager::from_storage(storage);
        assert_eq!(manager.get_default_provider(), None);
        assert_eq!(manager.get_theme().as_deref(), Some("eukhe"));
    }

    #[test]
    fn idle_eviction_semantics() {
        let eviction = |minutes: Option<serde_json::Value>| {
            SettingsManager::in_memory(&Settings {
                idle_eviction_minutes: minutes,
                ..Settings::default()
            })
            .get_idle_eviction()
        };
        assert_eq!(eviction(None), IdleEviction::Minutes(90));
        assert_eq!(eviction(Some(serde_json::json!("off"))), IdleEviction::Off);
        assert_eq!(
            eviction(Some(serde_json::json!(0))),
            IdleEviction::Minutes(90)
        );
        assert_eq!(
            eviction(Some(serde_json::json!(45))),
            IdleEviction::Minutes(45)
        );
    }

    #[test]
    fn compaction_toggle_defaults_on_and_persists() {
        // TS getCompactionEnabled: absent -> true (auto-compaction is on
        // until the user opts out); setCompactionEnabled writes the global
        // scope, so the value survives a reload (a restarted session
        // re-seeds its flag from it).
        let mut manager = SettingsManager::in_memory(&Settings::default());
        assert!(manager.get_compaction_enabled());
        manager.set_compaction_enabled(false).unwrap();
        assert!(!manager.get_compaction_enabled());
        manager.reload().unwrap();
        assert!(!manager.get_compaction_enabled());
    }

    #[test]
    fn session_archive_policy_semantics() {
        let policy = |age: Option<serde_json::Value>, count: Option<serde_json::Value>| {
            SettingsManager::in_memory(&Settings {
                session_archive_max_age_days: age,
                session_archive_max_sessions: count,
                ..Settings::default()
            })
            .get_session_archive_policy()
        };
        // Absent keys: both rules on with their defaults.
        assert_eq!(
            policy(None, None),
            SessionArchivePolicy {
                max_age_days: Some(30),
                max_sessions: Some(200),
            }
        );
        // "off"/"none" disable a rule; malformed values fall back to the
        // default (the `idleEvictionMinutes` grammar); a count of 0 is off.
        assert_eq!(
            policy(
                Some(serde_json::json!("off")),
                Some(serde_json::json!("none"))
            ),
            SessionArchivePolicy {
                max_age_days: None,
                max_sessions: None,
            }
        );
        assert_eq!(
            policy(Some(serde_json::json!(0)), Some(serde_json::json!(0))),
            SessionArchivePolicy {
                max_age_days: Some(30),
                max_sessions: None,
            }
        );
        assert_eq!(
            policy(Some(serde_json::json!(14)), Some(serde_json::json!(50))),
            SessionArchivePolicy {
                max_age_days: Some(14),
                max_sessions: Some(50),
            }
        );
    }

    /// TS `getImageModel`: the `imageModel` reference reads trimmed, and
    /// malformed values (empty/whitespace) behave as unset.
    #[test]
    fn image_model_reads_trimmed_or_unset() {
        let manager = SettingsManager::in_memory(&Settings {
            image_model: Some("  battery/mock-vision  ".to_string()),
            ..Settings::default()
        });
        assert_eq!(
            manager.get_image_model().as_deref(),
            Some("battery/mock-vision")
        );
        let manager = SettingsManager::in_memory(&Settings {
            image_model: Some("   ".to_string()),
            ..Settings::default()
        });
        assert_eq!(manager.get_image_model(), None);
        let manager = SettingsManager::in_memory(&Settings::default());
        assert_eq!(manager.get_image_model(), None);
    }

    /// `memory.settleTimeoutMs`: unset and `0` take the default (as
    /// `subagentStallMs` and `maxToolRounds` read `0`); `0` once meant
    /// no wait at all, so every turn showed unbuilt lines cut short.
    #[test]
    fn memory_settle_timeout_zero_takes_the_default() {
        let settle = |ms| {
            SettingsManager::in_memory(&Settings {
                memory: Some(crate::settings::types::MemorySettings {
                    settle_timeout_ms: ms,
                    ..Default::default()
                }),
                ..Settings::default()
            })
            .get_memory_settle_timeout()
        };
        assert_eq!(settle(None), crate::memory::SETTLE_TIMEOUT);
        assert_eq!(settle(Some(0)), crate::memory::SETTLE_TIMEOUT);
        assert_eq!(settle(Some(1_500)), std::time::Duration::from_millis(1_500));
    }
}
