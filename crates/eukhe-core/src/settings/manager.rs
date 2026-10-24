//! `SettingsManager`: loads global + project settings, merges them, builds
//! the cvar layers over them (`settings::cvar`, `settings::cfg`), and
//! writes back only what a setter changes (`settings::persist`).

use std::sync::Arc;

use anyhow::{anyhow, Result};
use eukhe_types::cvar::{Aliases, Binds, Command};
use serde_json::{Map, Value};

use super::cfg::{
    cfg_error, config_layer, global_list, remove_sets, replace_sets, run_script, ConfigBounds,
    CONFIG_CFG, SETTINGS_JSON,
};
use super::cvar::{
    document_sets, registry, table, value_text, AgentLayer, CvarError, CvarScope, CvarWriteError,
    Cvars, Decl, LayerKind, Sets, Target,
};
use super::load::load_document;
use super::merge::{deep_merge, migrate};
use super::persist::{
    edit_document, edit_read, read_document, DocRead, KeyEdit, Persisted, Shadow,
};
use super::storage::{SettingsScope, SettingsStorage, CONFIG_DIR_NAME};
use super::trust::{apply_project_trust, effective_project, ProjectTrust};
use super::types::{QueueModeSetting, Settings, ThinkingLevelSetting, TransportSetting};

pub const RECENT_MODELS_LIMIT: usize = 20;

#[derive(Debug, Clone, PartialEq, Eq)]
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
    /// Where each part of the config layer comes from.
    bounds: ConfigBounds,
    /// The aliases of the config cfg files.
    aliases: Aliases,
    errors: Vec<SettingsError>,
    /// The raw global document (the parsed JSON before the field load).
    /// A reader that must tell an ABSENT key from a PRESENT-but-malformed
    /// one (the model allowlist, the admission limits) reads it: the typed
    /// `Settings` drops both to `None`.
    global_raw: Option<Value>,
    /// The global document's read or parse failure, if any.
    global_load_error: Option<String>,
}

/// A change of a settings document read under its lock: the document to
/// write (`None`: it changed nothing), or why it cannot apply.
type DocumentEdit<'a> = dyn FnMut(DocRead) -> Result<Option<Map<String, Value>>, String> + 'a;

/// One loaded scope.
struct ScopeLoad {
    /// The typed settings: every leaf that applies.
    settings: Settings,
    /// The migrated document; `None` when absent or broken.
    raw: Option<Value>,
    /// Why the document could not be read or parsed.
    error: Option<String>,
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
        let global = load_scope(storage.as_ref(), SettingsScope::Global, &mut errors);
        let project_document =
            load_scope(storage.as_ref(), SettingsScope::Project, &mut errors).settings;
        // An unreadable global config.cfg trusts nothing; config_layer
        // records its error.
        let trusted = global_list(storage.as_ref(), &global.settings, &table::TRUSTED_PROJECTS)
            .unwrap_or_default();
        let (project, mut project_trust) =
            apply_project_trust(storage.as_ref(), &trusted, &project_document, &mut errors);
        let merged = deep_merge(&global.settings, &project);
        let layer = config_layer(
            storage.as_ref(),
            &global.settings,
            &merged,
            project_trust.level,
        );
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
            global: global.settings,
            project_document,
            project,
            project_trust,
            merged,
            cvars,
            bounds: layer.bounds,
            aliases: layer.aliases,
            errors,
            global_raw: global.raw,
            global_load_error: global.error,
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
    ///
    /// # Panics
    ///
    /// When `initial` does not serialize (a `Settings` always does).
    #[must_use]
    pub fn in_memory(initial: &Settings) -> Self {
        let storage: Arc<dyn SettingsStorage> =
            Arc::new(super::storage::InMemorySettingsStorage::default());
        let content = serde_json::to_string_pretty(&initial).expect("settings serialize");
        storage
            .with_lock(SettingsScope::Global, &mut |_| Some(content.clone()))
            .expect("the in-memory storage never fails");
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

    /// The raw global document (post-migration, pre-field-load value);
    /// `None` when the scope has no document or it failed to parse (the
    /// load error covers the latter).
    #[must_use]
    pub fn global_raw(&self) -> Option<&Value> {
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

    /// The scope whose file sets cvar `decl` last in the config layer:
    /// the project `config.cfg`, the global `config.cfg`, or a
    /// `settings.json` (the project's when it holds the key of a Local
    /// cvar, else the global one); `None` when no file sets it (the
    /// default applies).
    #[must_use]
    pub fn config_scope(&self, decl: &Decl) -> Option<SettingsScope> {
        let at = self
            .cvars
            .config()
            .0
            .iter()
            .rposition(|set| set.id == decl.id)?;
        if at >= self.bounds.global_cfg {
            return Some(SettingsScope::Project);
        }
        if at >= self.bounds.document {
            return Some(SettingsScope::Global);
        }
        let in_project = match decl.scope {
            CvarScope::Global => false,
            CvarScope::Local => serde_json::to_value(&self.project)
                .ok()
                .as_ref()
                .and_then(|project| {
                    decl.id
                        .split('.')
                        .try_fold(project, |node, key| node.get(key))
                })
                .is_some_and(|value| !value.is_null()),
        };
        Some(if in_project {
            SettingsScope::Project
        } else {
            SettingsScope::Global
        })
    }

    /// Unset cvars `decls` in the global layer: their keys leave the
    /// global `settings.json` and their sets and toggles leave the global
    /// `config.cfg` (each file under its lock); then the config layer is
    /// rebuilt, so a project's value or the default applies.
    ///
    /// # Errors
    ///
    /// A file cannot be locked, read, parsed or written.
    pub fn clear_global(&mut self, decls: &[&Decl]) -> Result<()> {
        self.write_scope(SettingsScope::Global, &mut |read| {
            let edits = decls
                .iter()
                .map(|decl| (decl.id.split('.').collect(), KeyEdit::Remove))
                .collect();
            edit_document(read, edits)
        })?;
        let ids: Vec<&str> = decls.iter().map(|decl| decl.id).collect();
        self.storage
            .with_cfg_lock(SettingsScope::Global, CONFIG_CFG, &mut |current| {
                let text = current?;
                let kept = remove_sets(&text, &ids);
                (kept != text).then_some(kept)
            })
            .map_err(|error| anyhow!("Global config.cfg not saved: {error:#}"))?;
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
        self.bounds = layer.bounds;
        self.aliases = layer.aliases;
    }

    /// Re-derive the applying project scope and the merge after a project
    /// document edit (the trust decision stands).
    fn refresh_project_scope(&mut self) {
        (self.project, _) = effective_project(&self.project_document, self.project_trust.level);
        self.rebuild_cvars();
    }

    // -- persistence ---------------------------------------------------------

    /// The read/modify/write of one scope's `settings.json` under its lock:
    /// read the document on disk now, let `edit` change it (through the
    /// compiled core, [`edit_document`]), write the result, and load it. A
    /// document that cannot be read or parsed is never written. Every key
    /// that `edit` does not touch keeps its value, a key that failed to
    /// load included.
    ///
    /// # Errors
    ///
    /// The file cannot be locked, read, parsed or written, or `edit`
    /// refuses (a parent on its path is not an object).
    fn write_scope(&mut self, scope: SettingsScope, edit: &mut DocumentEdit<'_>) -> Result<()> {
        let label = match scope {
            SettingsScope::Global => "Global",
            SettingsScope::Project => "Project",
        };
        let mut failure: Option<String> = None;
        let mut written: Option<Map<String, Value>> = None;
        self.storage
            .with_lock(scope, &mut |current| {
                failure = None;
                written = None;
                let read = match read_document(current.as_deref()) {
                    DocRead::Broken(reason) => {
                        DocRead::Broken(format!("the settings file does not parse: {reason}"))
                    }
                    read @ (DocRead::Missing | DocRead::Parsed(_)) => read,
                };
                let document = match edit(read) {
                    Ok(Some(document)) => document,
                    Ok(None) => return None,
                    Err(reason) => {
                        failure = Some(reason);
                        return None;
                    }
                };
                match serde_json::to_string_pretty(&document) {
                    Ok(text) => {
                        written = Some(document);
                        Some(text)
                    }
                    Err(error) => {
                        failure = Some(error.to_string());
                        None
                    }
                }
            })
            .map_err(|error| anyhow!("{label} settings not saved: {error:#}"))?;
        if let Some(reason) = failure {
            return Err(anyhow!("{label} settings not saved: {reason}"));
        }
        if let Some(document) = written {
            self.install_scope(scope, document);
        }
        Ok(())
    }

    /// Load `document`, just written to `scope`, as that scope; its leaf
    /// diagnostics not recorded before are recorded.
    fn install_scope(&mut self, scope: SettingsScope, mut document: Map<String, Value>) {
        migrate(&mut document);
        let loaded = load_document(&document);
        for error in &loaded.rejected {
            let error = cfg_error(scope, SETTINGS_JSON, error);
            if !self.errors.contains(&error) {
                self.errors.push(error);
            }
        }
        match scope {
            SettingsScope::Global => {
                self.global = loaded.settings;
                self.global_raw = Some(Value::Object(document));
                self.global_load_error = None;
                self.rebuild_cvars();
            }
            SettingsScope::Project => {
                self.project_document = loaded.settings;
                self.refresh_project_scope();
            }
        }
    }

    /// Write `value` at the key path of cvar `decl` in `scope`'s
    /// `settings.json` and say whether it applies.
    ///
    /// # Errors
    ///
    /// `value` is not a value the setting holds (nothing is written), or
    /// the write fails ([`Self::write_scope`]).
    pub(crate) fn set_scope_cvar(
        &mut self,
        scope: SettingsScope,
        decl: &Decl,
        value: &Value,
    ) -> Result<Persisted> {
        let path: Vec<&str> = decl.id.split('.').collect();
        let (probe, _) = edit_read(DocRead::Missing, &path, &KeyEdit::Set(value.clone()))
            .map_err(|error| anyhow!(error))?;
        if let Some(error) = load_document(&probe).rejected.into_iter().next() {
            return Err(anyhow!(error));
        }
        self.write_scope(scope, &mut |read| {
            edit_document(read, vec![(path.clone(), KeyEdit::Set(value.clone()))])
        })?;
        Ok(self.persisted(&[(decl, value)]))
    }

    /// [`Self::set_scope_cvar`] in the global scope (every interactive
    /// setter).
    pub(crate) fn set_global_cvar(&mut self, decl: &Decl, value: &Value) -> Result<Persisted> {
        self.set_scope_cvar(SettingsScope::Global, decl, value)
    }

    /// Whether each written `(decl, value)` is the value that applies: the
    /// last set of the config layer for the cvar (the agent family is the
    /// session's own and does not count). Another value means a higher
    /// layer sets it.
    fn persisted(&self, written: &[(&Decl, &Value)]) -> Persisted {
        let sets = &self.cvars.config().0;
        let shadows: Vec<Shadow> = written
            .iter()
            .filter_map(|(decl, value)| {
                let at = sets.iter().rposition(|set| set.id == decl.id)?;
                (sets[at].value != **value).then(|| Shadow {
                    id: decl.id.to_string(),
                    file: self.layer_file(at),
                })
            })
            .collect();
        if shadows.is_empty() {
            Persisted::Applies
        } else {
            Persisted::Shadowed(shadows)
        }
    }

    /// The file that set config set `at`.
    fn layer_file(&self, at: usize) -> String {
        let project = self
            .storage
            .project_dir()
            .map(|dir| dir.join(CONFIG_DIR_NAME));
        let global = self
            .storage
            .global_location()
            .and_then(std::path::Path::parent);
        let (dir, name, fallback) = if at < self.bounds.document {
            (project, SETTINGS_JSON, "the project settings.json")
        } else if at < self.bounds.global_cfg {
            (
                global.map(std::path::Path::to_path_buf),
                CONFIG_CFG,
                "the global config.cfg",
            )
        } else {
            (project, CONFIG_CFG, "the project config.cfg")
        };
        dir.map_or_else(
            || fallback.to_string(),
            |dir| dir.join(name).display().to_string(),
        )
    }

    // -- persisted setters --------------------------------------------------

    /// `defaultModel` + `defaultProvider` setter (the model switch's
    /// combined write); the model goes to the front of `recentModels`
    /// (as the file holds it now, capped at 20).
    ///
    /// # Errors
    ///
    /// The global settings file cannot be read, parsed or written.
    pub fn set_default_model_and_provider(
        &mut self,
        provider: &str,
        model: &str,
    ) -> Result<Persisted> {
        let key = format!("{provider}/{model}");
        self.write_scope(SettingsScope::Global, &mut |read| {
            let mut recent = vec![key.clone()];
            if let DocRead::Parsed(document) = &read {
                if let Some(Value::Array(items)) = document.get("recentModels") {
                    recent.extend(
                        items
                            .iter()
                            .filter_map(Value::as_str)
                            .filter(|item| *item != key)
                            .map(str::to_string),
                    );
                }
            }
            recent.truncate(RECENT_MODELS_LIMIT);
            edit_document(
                read,
                vec![
                    (vec!["defaultProvider"], KeyEdit::Set(provider.into())),
                    (vec!["defaultModel"], KeyEdit::Set(model.into())),
                    (vec!["recentModels"], KeyEdit::Set(recent.into())),
                ],
            )
        })?;
        Ok(self.persisted(&[
            (&table::DEFAULT_PROVIDER, &Value::from(provider)),
            (&table::DEFAULT_MODEL, &Value::from(model)),
        ]))
    }

    /// `steeringMode` setter.
    ///
    /// # Errors
    ///
    /// The global settings file cannot be read, parsed or written.
    pub fn set_steering_mode(&mut self, mode: QueueModeSetting) -> Result<Persisted> {
        self.set_global_cvar(&table::STEERING_MODE, &serde_json::to_value(mode)?)
    }

    /// `followUpMode` setter.
    ///
    /// # Errors
    ///
    /// The global settings file cannot be read, parsed or written.
    pub fn set_follow_up_mode(&mut self, mode: QueueModeSetting) -> Result<Persisted> {
        self.set_global_cvar(&table::FOLLOW_UP_MODE, &serde_json::to_value(mode)?)
    }

    /// `theme` setter.
    ///
    /// # Errors
    ///
    /// The global settings file cannot be read, parsed or written.
    pub fn set_theme(&mut self, theme: String) -> Result<Persisted> {
        self.set_global_cvar(&table::THEME, &Value::String(theme))
    }

    /// `defaultThinkingLevel` setter.
    ///
    /// # Errors
    ///
    /// The global settings file cannot be read, parsed or written.
    pub fn set_default_thinking_level(&mut self, level: ThinkingLevelSetting) -> Result<Persisted> {
        self.set_global_cvar(
            &table::DEFAULT_THINKING_LEVEL,
            &serde_json::to_value(level)?,
        )
    }

    /// TS `setRetryEnabled`: the auto-retry toggle the provider retry
    /// policy reads (`retry.enabled`).
    ///
    /// # Errors
    ///
    /// The global settings file cannot be read, parsed or written.
    pub fn set_retry_enabled(&mut self, enabled: bool) -> Result<Persisted> {
        self.set_global_cvar(&table::RETRY_ENABLED, &Value::Bool(enabled))
    }

    /// TS `setCompactionEnabled`: the auto-compaction toggle
    /// (`compaction.enabled` in the global settings file). The connection
    /// state's `autoCompactionEnabled` is this value in TS, so a daemon
    /// restart re-seeds the flag from the persisted setting.
    ///
    /// # Errors
    ///
    /// The global settings file cannot be read, parsed or written.
    pub fn set_compaction_enabled(&mut self, enabled: bool) -> Result<Persisted> {
        self.set_global_cvar(&table::COMPACTION_ENABLED, &Value::Bool(enabled))
    }

    /// `transport` setter.
    ///
    /// # Errors
    ///
    /// The global settings file cannot be read, parsed or written.
    pub fn set_transport(&mut self, transport: TransportSetting) -> Result<Persisted> {
        self.set_global_cvar(&table::TRANSPORT, &serde_json::to_value(transport)?)
    }

    /// `rlmMaxDepth` setter.
    ///
    /// # Errors
    ///
    /// The global settings file cannot be read, parsed or written.
    pub fn set_rlm_max_depth(&mut self, depth: u64) -> Result<Persisted> {
        self.set_global_cvar(&table::RLM_MAX_DEPTH, &Value::from(depth))
    }

    /// `onboardingShown` setter.
    ///
    /// # Errors
    ///
    /// The global settings file cannot be read, parsed or written.
    pub fn set_onboarding_shown(&mut self, shown: bool) -> Result<Persisted> {
        self.set_global_cvar(&table::ONBOARDING_SHOWN, &Value::Bool(shown))
    }

    /// Replace the `packages` array of `scope`'s settings file.
    ///
    /// # Errors
    ///
    /// The settings file cannot be read, parsed or written.
    pub fn set_scope_packages(
        &mut self,
        scope: SettingsScope,
        packages: Vec<Value>,
    ) -> Result<Persisted> {
        self.set_scope_cvar(scope, &table::PACKAGES, &Value::Array(packages))
    }

    /// Replace one resource-path array (`skills`/`prompts`/`themes`) of
    /// `scope`'s settings file (TS `setSkillPaths` & friends).
    ///
    /// # Errors
    ///
    /// `field` is not one of the three arrays, or the settings file cannot
    /// be read, parsed or written.
    pub fn set_scope_resource_array(
        &mut self,
        scope: SettingsScope,
        field: &str,
        values: Vec<String>,
    ) -> Result<Persisted> {
        let decl = match field {
            "skills" => &table::SKILLS,
            "prompts" => &table::PROMPTS,
            "themes" => &table::THEMES,
            other => return Err(anyhow!("`{other}` is not a resource array")),
        };
        self.set_scope_cvar(scope, decl, &Value::from(values))
    }

    /// Set global `mcpServers.<name>` to `entry`: only that key changes.
    ///
    /// # Errors
    ///
    /// The global settings file cannot be read, parsed or written, or its
    /// `mcpServers` is not an object.
    pub fn set_global_mcp_server(&mut self, name: &str, entry: &Value) -> Result<()> {
        self.write_scope(SettingsScope::Global, &mut |read| {
            edit_document(
                read,
                vec![(vec!["mcpServers", name], KeyEdit::Set(entry.clone()))],
            )
        })
    }

    /// Remove global `mcpServers.<name>`; `true` when it was there.
    ///
    /// # Errors
    ///
    /// The global settings file cannot be read, parsed or written.
    pub fn remove_global_mcp_server(&mut self, name: &str) -> Result<bool> {
        let mut removed = false;
        self.write_scope(SettingsScope::Global, &mut |read| {
            let document = edit_document(read, vec![(vec!["mcpServers", name], KeyEdit::Remove)])?;
            removed = document.is_some();
            Ok(document)
        })?;
        Ok(removed)
    }

    /// TS `setDefaultServiceTier`: the persisted default a fresh session
    /// starts from; the stored string is the same vocabulary
    /// `get_default_service_tier` parses.
    ///
    /// # Errors
    ///
    /// The global settings file cannot be read, parsed or written.
    pub fn set_default_service_tier(
        &mut self,
        tier: eukhe_types::ai::ServiceTier,
    ) -> Result<Persisted> {
        use eukhe_types::ai::ServiceTier;
        let name = match tier {
            ServiceTier::Auto => "auto",
            ServiceTier::Default => "default",
            ServiceTier::Flex => "flex",
            ServiceTier::Scale => "scale",
            ServiceTier::Priority => "priority",
        };
        self.set_global_cvar(&table::DEFAULT_SERVICE_TIER, &Value::from(name))
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

/// Load one scope: its document, migrated, through the leaf load. A
/// document that cannot be read or parsed is a load error (the scope
/// applies nothing); each leaf that does not apply is a settings error.
fn load_scope(
    storage: &dyn SettingsStorage,
    scope: SettingsScope,
    errors: &mut Vec<SettingsError>,
) -> ScopeLoad {
    // The pure-read arm: a locked protocol read on any cache miss, the
    // process-cached copy on a hit (see `SettingsStorage::read`).
    let read = match storage.read(scope) {
        Ok(content) => read_document(content.as_deref()),
        Err(error) => DocRead::Broken(format!("{error:#}")),
    };
    let mut document = match read {
        DocRead::Missing => {
            return ScopeLoad {
                settings: Settings::default(),
                raw: None,
                error: None,
            }
        }
        DocRead::Parsed(document) => document,
        DocRead::Broken(message) => {
            errors.push(SettingsError {
                scope,
                message: message.clone(),
            });
            return ScopeLoad {
                settings: Settings::default(),
                raw: None,
                error: Some(message),
            };
        }
    };
    migrate(&mut document);
    let loaded = load_document(&document);
    errors.extend(
        loaded
            .rejected
            .iter()
            .map(|error| cfg_error(scope, SETTINGS_JSON, error)),
    );
    ScopeLoad {
        settings: loaded.settings,
        raw: Some(Value::Object(document)),
        error: None,
    }
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
            .unwrap()
            .applied()
            .expect("the value applies");
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
            .expect("set factory enabled")
            .applied()
            .expect("the value applies");
        assert!(manager.get_factory_enabled());
        let content =
            std::fs::read_to_string(agent_dir.join("settings.json")).expect("global file");
        assert!(
            content.contains(r#""enabled": true"#),
            "the write lands in the global document the kernel gate reads: {content}"
        );

        manager
            .set_factory_enabled(false)
            .expect("set factory disabled")
            .applied()
            .expect("the value applies");
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
        manager
            .set_theme("dark".to_string())
            .expect("set theme")
            .applied()
            .expect("the value applies");
        assert_eq!(read()["terminal"]["fullscreen"], serde_json::json!(true));

        manager
            .set_fullscreen(false)
            .expect("set fullscreen")
            .applied()
            .expect("the value applies");
        assert!(!SettingsManager::create(&cwd, &agent_dir).get_fullscreen());
        assert_eq!(read()["terminal"]["fullscreen"], serde_json::json!(false));
    }

    /// Regression (audit H2): a setter wrote the typed copy loaded at
    /// startup, so a field that failed to load (`compaction`, one bad
    /// leaf) and a key another writer added since were deleted from
    /// disk. A setter now changes only its key of the document on disk.
    #[test]
    fn a_setter_keeps_a_field_that_failed_to_load_and_a_concurrent_edit() {
        let dir = tempfile::tempdir().unwrap();
        let cwd = dir.path().join("cwd");
        let agent_dir = dir.path().join("agent");
        std::fs::create_dir_all(&cwd).unwrap();
        std::fs::create_dir_all(&agent_dir).unwrap();
        let path = agent_dir.join("settings.json");
        std::fs::write(
            &path,
            r#"{"compaction":{"enabled":false,"reserveTokens":"16k"},"theme":"x"}"#,
        )
        .unwrap();
        let mut manager = SettingsManager::create(&cwd, &agent_dir);
        // Another writer adds a key after the load.
        std::fs::write(
            &path,
            r#"{"compaction":{"enabled":false,"reserveTokens":"16k"},"theme":"x","defaultModel":"m"}"#,
        )
        .unwrap();
        assert_eq!(
            manager.set_theme("y".to_string()).unwrap(),
            Persisted::Applies
        );
        let written: serde_json::Value =
            serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap();
        assert_eq!(
            written,
            serde_json::json!({
                "compaction": { "enabled": false, "reserveTokens": "16k" },
                "theme": "y",
                "defaultModel": "m"
            })
        );
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
        manager
            .set_chat_detail("all")
            .unwrap()
            .applied()
            .expect("the value applies");
        assert_eq!(manager.get_chat_detail(), "all");
        manager.reload().unwrap();
        assert_eq!(
            manager.get_chat_detail(),
            "all",
            "the saved level survives a reload (a later chat re-reads it)"
        );
        manager
            .set_chat_detail("details")
            .unwrap()
            .applied()
            .expect("the value applies");
        assert_eq!(
            manager.get_chat_detail(),
            "details",
            "a saved details level reads back exactly (the Ctrl+O thinking reveal persists)"
        );
        assert_eq!(
            manager
                .set_chat_detail("verbose")
                .map_err(|error| error.to_string()),
            Err(
                "`verbose` is not a value of `chatDetail` (one of overview, details, all)"
                    .to_string()
            ),
            "an invalid value is refused and never written"
        );
        assert_eq!(manager.get_chat_detail(), "details");
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
            .unwrap()
            .applied()
            .expect("the value applies");
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
        manager
            .set_compaction_enabled(false)
            .unwrap()
            .applied()
            .expect("the value applies");
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
