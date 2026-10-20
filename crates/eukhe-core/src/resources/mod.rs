//! Project context files (AGENTS.md/CLAUDE.md discovery) and the resource
//! loader. Port of core/resource-loader.ts, scoped to the session engine's
//! needs: skills, prompt templates, agents files, and system-prompt sources,
//! resolved from configured packages, settings, auto-discovery, and bundled
//! skills through the package manager. Themes resolve to the paths the
//! client registers; eukhe-tui loads the theme files.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use crate::skills::diagnostics::ResourceDiagnostic;
use crate::skills::{
    load_prompt_templates, load_skills, LoadPromptTemplatesOptions, LoadSkillsOptions,
    PromptTemplate, Skill,
};

/// AGENTS.md-family candidates, in priority order.
const CONTEXT_FILE_CANDIDATES: [&str; 4] = ["AGENTS.md", "AGENTS.MD", "CLAUDE.md", "CLAUDE.MD"];

/// A loaded context file (path + content).
#[derive(Debug, Clone, PartialEq)]
pub struct ContextFile {
    pub path: PathBuf,
    pub content: String,
}

fn load_context_file_from_dir(dir: &Path) -> Option<ContextFile> {
    for filename in CONTEXT_FILE_CANDIDATES {
        let file_path = dir.join(filename);
        if let Ok(content) = std::fs::read_to_string(&file_path) {
            return Some(ContextFile {
                path: file_path,
                content,
            });
        }
    }
    None
}

/// Load the global (agentDir) context file first, then the nearest-to-root
/// ancestor chain of cwd. Port of loadProjectContextFiles.
#[must_use]
pub fn load_project_context_files(cwd: &Path, agent_dir: &Path) -> Vec<ContextFile> {
    let mut context_files = Vec::new();
    let mut seen: HashSet<PathBuf> = HashSet::new();
    if let Some(global) = load_context_file_from_dir(agent_dir) {
        seen.insert(global.path.clone());
        context_files.push(global);
    }

    // Walk cwd upward, collecting context files; root-most first in output.
    let mut ancestors = Vec::new();
    let mut current = cwd.to_path_buf();
    loop {
        if let Some(found) = load_context_file_from_dir(&current) {
            if seen.insert(found.path.clone()) {
                ancestors.push(found);
            }
        }
        let Some(parent) = current.parent() else {
            break;
        };
        if parent == current {
            break;
        }
        current = parent.to_path_buf();
    }
    ancestors.reverse();
    context_files.extend(ancestors);
    context_files
}

// Session resource resolution (package-manager `resolve()`) feeds the
// loader below.
pub(crate) mod resolution;

use anyhow::{Context, Result};

use crate::packages::BundledSkillsDir;
use crate::prompts::{PromptOrigin, SourcedPrompt};
use crate::settings::{SettingsManager, TrustLevel};

/// Loaded resources for a session.
#[derive(Debug, Default)]
pub struct LoadedResources {
    pub skills: Vec<Skill>,
    pub skill_diagnostics: Vec<ResourceDiagnostic>,
    /// Prompt templates that failed to load or lost a name collision, each
    /// with its path, then the system prompt files that did not load.
    pub prompt_diagnostics: Vec<ResourceDiagnostic>,
    pub prompts: Vec<PromptTemplate>,
    pub agents_files: Vec<ContextFile>,
    /// The replacement system prompt: the explicit input, else the
    /// discovered `SYSTEM.md`.
    pub system_prompt: Option<SourcedPrompt>,
    /// The appended system prompts: the explicit inputs, else the
    /// discovered `APPEND_SYSTEM.md`.
    pub append_system_prompt: Vec<SourcedPrompt>,
}

/// One system prompt input from a caller. Its type is explicit: text is
/// always prompt text, and a file is always a file to read. On the wire, a
/// JSON string is text and `{"file": "<path>"}` is a file.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(untagged)]
pub enum SystemPromptInput {
    /// The prompt text.
    Text(String),
    /// A file that holds the prompt text. A relative path starts at the
    /// session cwd.
    File { file: PathBuf },
}

/// Resource loading options (the TS `DefaultResourceLoaderOptions` surface,
/// minus the theme machinery).
#[derive(Default)]
pub struct ResourceLoaderOptions {
    pub cwd: PathBuf,
    pub agent_dir: PathBuf,
    /// Settings manager for package resolution; loaded from disk when `None`.
    pub settings: Option<SettingsManager>,
    /// Built-in skills directory (default: the packaged layout).
    pub bundled_skills_dir: BundledSkillsDir,
    /// Extra force-exclude patterns for built-in skills.
    pub extra_builtin_skill_overrides: Vec<String>,
    pub additional_skill_paths: Vec<String>,
    pub additional_prompt_paths: Vec<String>,
    pub no_skills: bool,
    pub no_prompt_templates: bool,
    pub no_context_files: bool,
    /// `--system-prompt` or `--system-prompt-file`. It overrides the
    /// discovered `SYSTEM.md`.
    pub system_prompt: Option<SystemPromptInput>,
    /// `--append-system-prompt` and `--append-system-prompt-file`, in
    /// order. They override the discovered `APPEND_SYSTEM.md`.
    pub append_system_prompt: Vec<SystemPromptInput>,
}

impl ResourceLoaderOptions {
    /// Options with just the working directories set.
    pub fn new(cwd: impl Into<PathBuf>, agent_dir: impl Into<PathBuf>) -> Self {
        Self {
            cwd: cwd.into(),
            agent_dir: agent_dir.into(),
            ..Default::default()
        }
    }
}

/// Theme path resolution inputs (the TS resource-loader theme options).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ThemePathOptions {
    pub cwd: PathBuf,
    pub agent_dir: PathBuf,
    /// `--theme <path>` entries (TS `additionalThemePaths`).
    pub additional_theme_paths: Vec<PathBuf>,
    /// `--no-themes`: skip the resolved resource themes; the `--theme`
    /// paths still register.
    pub no_themes: bool,
}

pub use resolution::{resolve_theme_paths, theme_sources};

/// Load all session resources: package-manager resolution (configured
/// packages, settings arrays, auto-discovery, bundled skills) feeds the
/// enabled skill and prompt paths. Configured packages that are not
/// installed are not installed here: each one becomes a warning diagnostic
/// that gives the `eukhe package install` command.
///
/// # Errors
///
/// Returns an error when the session resource resolution fails (a
/// configured package source cannot be parsed), or when an explicit system
/// prompt file cannot be read.
pub fn load_resources(mut options: ResourceLoaderOptions) -> Result<LoadedResources> {
    let settings = options
        .settings
        .take()
        .unwrap_or_else(|| SettingsManager::create(&options.cwd, &options.agent_dir));
    let trust = settings.project_trust().level;
    let resolution = resolution::resolve_session_resources(&options, settings)?;

    let mut resources = LoadedResources::default();

    // Skills: CLI paths + additional paths first, then resolved paths in
    // precedence order; name collisions resolve first-wins in load order.
    let skills_result = if options.no_skills && resolution.skill_paths.is_empty() {
        crate::skills::LoadSkillsResult {
            skills: Vec::new(),
            diagnostics: Vec::new(),
        }
    } else {
        load_skills(&LoadSkillsOptions {
            cwd: options.cwd.clone(),
            agent_dir: options.agent_dir.clone(),
            skill_paths: resolution.skill_paths.clone(),
            include_defaults: false,
        })
    };
    resources.skills = skills_result
        .skills
        .into_iter()
        .map(|mut skill| {
            if let Some(source_info) =
                resolution::find_source_info(&resolution.source_infos, &skill.file_path)
            {
                skill.source_info = source_info;
            }
            skill
        })
        .collect();
    resources.skill_diagnostics = skills_result.diagnostics;
    // Resolution-time warnings (e.g. missing bundled skills directory), then
    // one warning per configured package that is not installed.
    resources
        .skill_diagnostics
        .extend(resolution.resolved.diagnostics.clone());
    resources
        .skill_diagnostics
        .extend(resolution.resolved.missing_packages.iter().map(|missing| {
            ResourceDiagnostic::Warning {
                message: missing.to_string(),
                path: None,
            }
        }));
    for path in &options.additional_skill_paths {
        if is_local_path(path)
            && !Path::new(path).exists()
            && !resources
                .skill_diagnostics
                .iter()
                .any(|d| diagnostics_path(d) == Some(path.clone()))
        {
            resources.skill_diagnostics.push(ResourceDiagnostic::Error {
                message: "Skill path does not exist".to_string(),
                path: Some(path.clone()),
            });
        }
    }

    // Prompt templates: CLI paths + resolved paths, then additional paths
    // (the resolution merged them in). The loader reports each path or file
    // that fails, a missing path included.
    let loaded_prompts = if options.no_prompt_templates && resolution.prompt_paths.is_empty() {
        crate::skills::LoadPromptTemplatesResult::default()
    } else {
        load_prompt_templates(&LoadPromptTemplatesOptions {
            cwd: options.cwd.clone(),
            agent_dir: options.agent_dir.clone(),
            prompt_paths: resolution.prompt_paths.clone(),
            include_defaults: false,
        })
    };
    resources.prompt_diagnostics = loaded_prompts.diagnostics;
    resources.prompts = dedupe_prompts(loaded_prompts.templates, &mut resources.prompt_diagnostics)
        .into_iter()
        .map(|mut prompt| {
            if let Some(source_info) =
                resolution::find_source_info(&resolution.source_infos, Path::new(&prompt.file_path))
            {
                prompt.source_info = source_info;
            }
            prompt
        })
        .collect();

    // Agents files (project context).
    if !options.no_context_files {
        resources.agents_files = load_project_context_files(&options.cwd, &options.agent_dir);
    }

    // System prompts: the explicit inputs, else the discovered files.
    let system_prompts = load_system_prompts(&SystemPromptRequest {
        cwd: &options.cwd,
        agent_dir: &options.agent_dir,
        trust,
        system: options.system_prompt.as_ref(),
        append: &options.append_system_prompt,
    })?;
    resources.system_prompt = system_prompts.system;
    resources.append_system_prompt = system_prompts.append;
    resources
        .prompt_diagnostics
        .extend(system_prompts.diagnostics);

    Ok(resources)
}

fn diagnostics_path(diagnostic: &ResourceDiagnostic) -> Option<String> {
    match diagnostic {
        ResourceDiagnostic::Warning { path, .. } | ResourceDiagnostic::Error { path, .. } => {
            path.clone()
        }
        ResourceDiagnostic::Collision { path, .. } => Some(path.clone()),
    }
}

/// The inputs of [`load_system_prompts`].
pub(crate) struct SystemPromptRequest<'a> {
    /// The session cwd. The project files are in `<cwd>/.eukhe/`.
    pub(crate) cwd: &'a Path,
    /// The agent dir. The global files are in it.
    pub(crate) agent_dir: &'a Path,
    /// The trust of the project at `cwd`. The project `SYSTEM.md` and
    /// `APPEND_SYSTEM.md` load only for a trusted project.
    pub(crate) trust: TrustLevel,
    /// The explicit replacement prompt. It overrides the discovered
    /// `SYSTEM.md`.
    pub(crate) system: Option<&'a SystemPromptInput>,
    /// The explicit appended prompts, in order. They override the
    /// discovered `APPEND_SYSTEM.md`.
    pub(crate) append: &'a [SystemPromptInput],
}

/// The system prompt texts that apply, and the problems with the
/// discovered files.
#[derive(Debug, Clone, Default, PartialEq)]
pub(crate) struct SystemPrompts {
    pub(crate) system: Option<SourcedPrompt>,
    pub(crate) append: Vec<SourcedPrompt>,
    pub(crate) diagnostics: Vec<ResourceDiagnostic>,
}

/// Resolve the system prompt inputs of a session. An explicit input wins
/// over the discovered file of its slot. A discovered file is the project
/// file when the project is trusted, else the global file. An untrusted
/// project file does not load: one warning names all of them. A discovered
/// file that cannot be read is an error diagnostic.
///
/// # Errors
///
/// Returns an error when an explicit file input cannot be read.
pub(crate) fn load_system_prompts(request: &SystemPromptRequest<'_>) -> Result<SystemPrompts> {
    let mut diagnostics = Vec::new();
    let mut withheld = Vec::new();
    let system = match request.system {
        Some(input) => Some(read_explicit_prompt(
            request.cwd,
            input,
            PromptSlot::System,
        )?),
        None => discover_prompt_file(request, PromptSlot::System, &mut withheld, &mut diagnostics)
            .and_then(|path| read_discovered_prompt(path, &mut diagnostics)),
    };
    let append = if request.append.is_empty() {
        discover_prompt_file(request, PromptSlot::Append, &mut withheld, &mut diagnostics)
            .and_then(|path| read_discovered_prompt(path, &mut diagnostics))
            .into_iter()
            .collect()
    } else {
        request
            .append
            .iter()
            .map(|input| read_explicit_prompt(request.cwd, input, PromptSlot::Append))
            .collect::<Result<Vec<_>>>()?
    };
    if !withheld.is_empty() {
        let files = withheld
            .iter()
            .map(|path| path.display().to_string())
            .collect::<Vec<_>>()
            .join(", ");
        diagnostics.push(ResourceDiagnostic::Warning {
            message: format!(
                "Project is not trusted: did not load project system prompt files {files}. To allow them, add {} to trustedProjects in {}.",
                request.cwd.display(),
                request.agent_dir.join("settings.json").display()
            ),
            path: None,
        });
    }
    Ok(SystemPrompts {
        system,
        append,
        diagnostics,
    })
}

/// The two system prompt slots.
#[derive(Debug, Clone, Copy)]
enum PromptSlot {
    /// The replacement prompt.
    System,
    /// The appended prompts.
    Append,
}

impl PromptSlot {
    fn text_flag(self) -> &'static str {
        match self {
            PromptSlot::System => "--system-prompt",
            PromptSlot::Append => "--append-system-prompt",
        }
    }

    fn file_flag(self) -> &'static str {
        match self {
            PromptSlot::System => "--system-prompt-file",
            PromptSlot::Append => "--append-system-prompt-file",
        }
    }

    fn file_name(self) -> &'static str {
        match self {
            PromptSlot::System => "SYSTEM.md",
            PromptSlot::Append => "APPEND_SYSTEM.md",
        }
    }
}

/// The text of an explicit input. Text stays text. A file that cannot be
/// read is an error.
fn read_explicit_prompt(
    cwd: &Path,
    input: &SystemPromptInput,
    slot: PromptSlot,
) -> Result<SourcedPrompt> {
    match input {
        SystemPromptInput::Text(text) => Ok(SourcedPrompt {
            origin: PromptOrigin::Flag(slot.text_flag()),
            text: text.clone(),
        }),
        SystemPromptInput::File { file } => {
            let path = cwd.join(file);
            let text = std::fs::read_to_string(&path).with_context(|| {
                format!(
                    "{} {}: cannot read the file",
                    slot.file_flag(),
                    path.display()
                )
            })?;
            Ok(SourcedPrompt {
                origin: PromptOrigin::File(path),
                text,
            })
        }
    }
}

/// The discovered file of `slot`: `<cwd>/.eukhe/<name>` when the project is
/// trusted, else `<agentDir>/<name>`. An untrusted project file goes into
/// `withheld`. A file whose presence cannot be checked is an error
/// diagnostic.
fn discover_prompt_file(
    request: &SystemPromptRequest<'_>,
    slot: PromptSlot,
    withheld: &mut Vec<PathBuf>,
    diagnostics: &mut Vec<ResourceDiagnostic>,
) -> Option<PathBuf> {
    let mut exists = |path: &Path| match path.try_exists() {
        Ok(found) => found,
        Err(error) => {
            diagnostics.push(ResourceDiagnostic::Error {
                message: format!(
                    "Cannot check the system prompt file: {error}. It is not in the system prompt."
                ),
                path: Some(path.display().to_string()),
            });
            false
        }
    };
    let project = request
        .cwd
        .join(crate::settings::CONFIG_DIR_NAME)
        .join(slot.file_name());
    if exists(&project) {
        match request.trust {
            TrustLevel::Trusted => return Some(project),
            TrustLevel::Untrusted => withheld.push(project),
        }
    }
    let global = request.agent_dir.join(slot.file_name());
    exists(&global).then_some(global)
}

/// The text of a discovered file. A file that cannot be read is an error
/// diagnostic.
fn read_discovered_prompt(
    path: PathBuf,
    diagnostics: &mut Vec<ResourceDiagnostic>,
) -> Option<SourcedPrompt> {
    match std::fs::read_to_string(&path) {
        Ok(text) => Some(SourcedPrompt {
            origin: PromptOrigin::File(path),
            text,
        }),
        Err(error) => {
            diagnostics.push(ResourceDiagnostic::Error {
                message: format!(
                    "Cannot read the system prompt file: {error}. It is not in the system prompt."
                ),
                path: Some(path.display().to_string()),
            });
            None
        }
    }
}

fn is_local_path(path: &str) -> bool {
    let trimmed = path.trim();
    !(trimmed.starts_with("npm:")
        || trimmed.starts_with("git:")
        || trimmed.starts_with("http://")
        || trimmed.starts_with("https://"))
}

/// TS dedupe keeps the FIRST template of each name; each later one from
/// another file is a collision diagnostic with its path (the same file
/// reached twice is one template).
fn dedupe_prompts(
    prompts: Vec<PromptTemplate>,
    diagnostics: &mut Vec<ResourceDiagnostic>,
) -> Vec<PromptTemplate> {
    let mut winners: std::collections::HashMap<String, String> = std::collections::HashMap::new();
    let mut out = Vec::new();
    for prompt in prompts {
        match winners.get(&prompt.name) {
            Some(winner_path) if *winner_path == prompt.file_path => {}
            Some(winner_path) => diagnostics.push(ResourceDiagnostic::Collision {
                message: format!("name \"/{}\" collision", prompt.name),
                path: prompt.file_path.clone(),
                collision: crate::skills::ResourceCollision {
                    resource_type: "prompt",
                    name: prompt.name.clone(),
                    winner_path: winner_path.clone(),
                    loser_path: prompt.file_path.clone(),
                },
            }),
            None => {
                winners.insert(prompt.name.clone(), prompt.file_path.clone());
                out.push(prompt);
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn context_files_global_then_ancestors_root_first() {
        let tmp = tempfile::tempdir().unwrap();
        let agent_dir = tmp.path().join("agent");
        let deep = tmp.path().join("a").join("b");
        fs::create_dir_all(&agent_dir).unwrap();
        fs::create_dir_all(&deep).unwrap();
        fs::write(agent_dir.join("AGENTS.md"), "global").unwrap();
        fs::write(tmp.path().join("a").join("AGENTS.md"), "level-a").unwrap();
        fs::write(deep.join("AGENTS.md"), "deep").unwrap();
        let files = load_project_context_files(&deep, &agent_dir);
        let contents: Vec<&str> = files.iter().map(|f| f.content.as_str()).collect();
        assert_eq!(contents, vec!["global", "level-a", "deep"]);
    }

    /// Write `<cwd>/.eukhe/SYSTEM.md` and `<cwd>/.eukhe/APPEND_SYSTEM.md`.
    fn project_prompt_files(cwd: &Path) -> (PathBuf, PathBuf) {
        let config_dir = cwd.join(".eukhe");
        fs::create_dir_all(&config_dir).unwrap();
        let system = config_dir.join("SYSTEM.md");
        let append = config_dir.join("APPEND_SYSTEM.md");
        fs::write(&system, "project system").unwrap();
        fs::write(&append, "project append").unwrap();
        (system, append)
    }

    fn untrusted_warning(cwd: &Path, agent_dir: &Path, files: [&Path; 2]) -> ResourceDiagnostic {
        ResourceDiagnostic::Warning {
            message: format!(
                "Project is not trusted: did not load project system prompt files {}, {}. To allow them, add {} to trustedProjects in {}.",
                files[0].display(),
                files[1].display(),
                cwd.display(),
                agent_dir.join("settings.json").display()
            ),
            path: None,
        }
    }

    /// An untrusted project neither replaces nor extends the system
    /// prompt. One warning names both files.
    #[test]
    fn untrusted_project_prompt_files_do_not_load() {
        let tmp = tempfile::tempdir().unwrap();
        let agent_dir = tmp.path().join("agent");
        let cwd = tmp.path().join("proj");
        fs::create_dir_all(&agent_dir).unwrap();
        let (system, append) = project_prompt_files(&cwd);
        let resources = load_resources(ResourceLoaderOptions {
            bundled_skills_dir: BundledSkillsDir::Disabled,
            no_context_files: true,
            ..ResourceLoaderOptions::new(&cwd, &agent_dir)
        })
        .unwrap();
        let prompt =
            crate::prompts::build_system_prompt(&crate::prompts::BuildSystemPromptOptions {
                custom_prompt: resources.system_prompt.clone(),
                append_system_prompt: resources.append_system_prompt.clone(),
                ..Default::default()
            });
        assert!(!prompt.contains("project system"), "{prompt}");
        assert!(!prompt.contains("project append"), "{prompt}");
        let warning = untrusted_warning(&cwd, &agent_dir, [system.as_path(), append.as_path()]);
        assert!(
            resources.prompt_diagnostics.contains(&warning),
            "{:?}",
            resources.prompt_diagnostics
        );
        assert_eq!(
            (resources.system_prompt, resources.append_system_prompt),
            (None, Vec::new())
        );
    }

    /// The global files load for an untrusted project; the project files
    /// do not.
    #[test]
    fn an_untrusted_project_keeps_the_global_prompt_files() {
        let tmp = tempfile::tempdir().unwrap();
        let agent_dir = tmp.path().join("agent");
        let cwd = tmp.path().join("proj");
        fs::create_dir_all(&agent_dir).unwrap();
        let global = agent_dir.join("SYSTEM.md");
        fs::write(&global, "global system").unwrap();
        let (system, append) = project_prompt_files(&cwd);
        let prompts = load_system_prompts(&SystemPromptRequest {
            cwd: &cwd,
            agent_dir: &agent_dir,
            trust: TrustLevel::Untrusted,
            system: None,
            append: &[],
        })
        .unwrap();
        assert_eq!(
            prompts,
            SystemPrompts {
                system: Some(SourcedPrompt {
                    origin: PromptOrigin::File(global),
                    text: "global system".to_string(),
                }),
                append: Vec::new(),
                diagnostics: vec![untrusted_warning(
                    &cwd,
                    &agent_dir,
                    [system.as_path(), append.as_path()],
                )],
            }
        );
    }

    /// A trusted project's files replace and extend the system prompt.
    #[test]
    fn trusted_project_prompt_files_apply() {
        let tmp = tempfile::tempdir().unwrap();
        let agent_dir = tmp.path().join("agent");
        let cwd = tmp.path().join("proj");
        fs::create_dir_all(&agent_dir).unwrap();
        let (system, append) = project_prompt_files(&cwd);
        fs::write(
            agent_dir.join("settings.json"),
            serde_json::json!({ "trustedProjects": [cwd.display().to_string()] }).to_string(),
        )
        .unwrap();
        let resources = load_resources(ResourceLoaderOptions {
            bundled_skills_dir: BundledSkillsDir::Disabled,
            no_context_files: true,
            ..ResourceLoaderOptions::new(&cwd, &agent_dir)
        })
        .unwrap();
        assert_eq!(
            (resources.system_prompt, resources.append_system_prompt),
            (
                Some(SourcedPrompt {
                    origin: PromptOrigin::File(system),
                    text: "project system".to_string(),
                }),
                vec![SourcedPrompt {
                    origin: PromptOrigin::File(append),
                    text: "project append".to_string(),
                }],
            )
        );
    }

    /// `--system-prompt-file ./missing.md` is an error, never the path as
    /// prompt text.
    #[test]
    fn a_missing_explicit_prompt_file_is_an_error() {
        let tmp = tempfile::tempdir().unwrap();
        let input = SystemPromptInput::File {
            file: PathBuf::from("./missing.md"),
        };
        let error = load_system_prompts(&SystemPromptRequest {
            cwd: tmp.path(),
            agent_dir: &tmp.path().join("agent"),
            trust: TrustLevel::Trusted,
            system: Some(&input),
            append: &[],
        })
        .unwrap_err();
        let path = tmp.path().join("./missing.md");
        let io_error = fs::read_to_string(&path).unwrap_err();
        assert_eq!(
            format!("{error:#}"),
            format!(
                "--system-prompt-file {}: cannot read the file: {io_error}",
                path.display()
            )
        );
    }

    /// A text input is the prompt text, also when it names a file.
    #[test]
    fn a_text_input_stays_text_when_it_names_a_file() {
        let tmp = tempfile::tempdir().unwrap();
        let file = tmp.path().join("real.md");
        fs::write(&file, "file text").unwrap();
        let input = SystemPromptInput::Text(file.display().to_string());
        let prompts = load_system_prompts(&SystemPromptRequest {
            cwd: tmp.path(),
            agent_dir: &tmp.path().join("agent"),
            trust: TrustLevel::Trusted,
            system: Some(&input),
            append: &[],
        })
        .unwrap();
        assert_eq!(
            prompts,
            SystemPrompts {
                system: Some(SourcedPrompt {
                    origin: PromptOrigin::Flag("--system-prompt"),
                    text: file.display().to_string(),
                }),
                append: Vec::new(),
                diagnostics: Vec::new(),
            }
        );
    }

    /// A discovered `SYSTEM.md` that cannot be read is a diagnostic.
    #[cfg(unix)]
    #[test]
    fn an_unreadable_discovered_system_prompt_is_a_diagnostic() {
        use std::os::unix::fs::PermissionsExt;
        let tmp = tempfile::tempdir().unwrap();
        let agent_dir = tmp.path().join("agent");
        fs::create_dir_all(&agent_dir).unwrap();
        let system = agent_dir.join("SYSTEM.md");
        fs::write(&system, "global system").unwrap();
        fs::set_permissions(&system, fs::Permissions::from_mode(0o000)).unwrap();
        let Err(io_error) = fs::read_to_string(&system) else {
            // Root reads the file anyway: nothing to check.
            return;
        };
        let prompts = load_system_prompts(&SystemPromptRequest {
            cwd: &tmp.path().join("proj"),
            agent_dir: &agent_dir,
            trust: TrustLevel::Untrusted,
            system: None,
            append: &[],
        })
        .unwrap();
        assert_eq!(
            prompts,
            SystemPrompts {
                system: None,
                append: Vec::new(),
                diagnostics: vec![ResourceDiagnostic::Error {
                    message: format!(
                        "Cannot read the system prompt file: {io_error}. It is not in the system prompt."
                    ),
                    path: Some(system.display().to_string()),
                }],
            }
        );
    }

    #[test]
    fn resources_load_end_to_end() {
        let tmp = tempfile::tempdir().unwrap();
        let agent_dir = tmp.path().join("agent");
        let cwd = tmp.path().join("proj");
        fs::create_dir_all(agent_dir.join("skills").join("alpha")).unwrap();
        fs::create_dir_all(cwd.join(".eukhe").join("prompts")).unwrap();
        fs::create_dir_all(&cwd).unwrap();
        fs::write(
            agent_dir.join("skills").join("alpha").join("SKILL.md"),
            "---\nname: alpha\ndescription: Alpha skill\n---\nbody",
        )
        .unwrap();
        fs::write(cwd.join(".eukhe").join("prompts").join("fix.md"), "Fix $1").unwrap();
        fs::write(cwd.join("AGENTS.md"), "Project rules").unwrap();
        let resources = load_resources(ResourceLoaderOptions {
            cwd,
            agent_dir,
            ..Default::default()
        })
        .unwrap();
        assert!(resources.skills.iter().any(|s| s.name == "alpha"));
        assert!(resources.prompts.iter().any(|p| p.name == "fix"));
        assert_eq!(resources.agents_files.len(), 1);
        assert_eq!(resources.agents_files[0].content, "Project rules");
    }

    #[test]
    fn package_provided_skills_and_prompts_load_into_a_session() {
        let tmp = tempfile::tempdir().unwrap();
        let agent_dir = tmp.path().join("agent");
        let cwd = tmp.path().join("proj");
        fs::create_dir_all(&agent_dir).unwrap();
        fs::create_dir_all(&cwd).unwrap();
        // A local package with a skill and a prompt.
        let pkg = tmp.path().join("fixture-pkg");
        fs::create_dir_all(pkg.join("skills").join("pack-skill")).unwrap();
        fs::create_dir_all(pkg.join("prompts")).unwrap();
        fs::write(
            pkg.join("package.json"),
            r#"{"name":"fixture-pkg","version":"1.0.0"}"#,
        )
        .unwrap();
        fs::write(
            pkg.join("skills").join("pack-skill").join("SKILL.md"),
            "---\nname: pack-skill\ndescription: From the package\n---\nBody",
        )
        .unwrap();
        fs::write(pkg.join("prompts").join("fix.md"), "Fix $1").unwrap();
        fs::write(
            agent_dir.join("settings.json"),
            serde_json::json!({"packages": ["../fixture-pkg"]}).to_string(),
        )
        .unwrap();

        let resources = load_resources(ResourceLoaderOptions::new(&cwd, &agent_dir)).unwrap();
        let skill = resources
            .skills
            .iter()
            .find(|skill| skill.name == "pack-skill")
            .expect("package skill loaded");
        assert_eq!(skill.source_info.source, "../fixture-pkg");
        assert_eq!(
            skill.source_info.origin,
            crate::skills::SourceOrigin::Package
        );
        let prompt = resources
            .prompts
            .iter()
            .find(|prompt| prompt.name == "fix")
            .expect("package prompt loaded");
        assert_eq!(prompt.source_info.source, "../fixture-pkg");
    }

    #[test]
    fn project_auto_skills_win_name_collisions_over_user_auto() {
        let tmp = tempfile::tempdir().unwrap();
        let agent_dir = tmp.path().join("agent");
        let cwd = tmp.path().join("proj");
        fs::create_dir_all(agent_dir.join("skills").join("alpha")).unwrap();
        fs::create_dir_all(cwd.join(".eukhe").join("skills").join("alpha")).unwrap();
        fs::create_dir_all(&cwd).unwrap();
        fs::write(
            agent_dir.join("skills").join("alpha").join("SKILL.md"),
            "---\nname: alpha\ndescription: User alpha\n---\nBody",
        )
        .unwrap();
        fs::write(
            cwd.join(".eukhe")
                .join("skills")
                .join("alpha")
                .join("SKILL.md"),
            "---\nname: alpha\ndescription: Project alpha\n---\nBody",
        )
        .unwrap();

        let resources = load_resources(ResourceLoaderOptions::new(&cwd, &agent_dir)).unwrap();
        let alpha: Vec<_> = resources
            .skills
            .iter()
            .filter(|skill| skill.name == "alpha")
            .collect();
        assert_eq!(alpha.len(), 1, "same name resolves to one skill");
        assert_eq!(alpha[0].description, "Project alpha");
        assert_eq!(
            alpha[0].source_info.scope,
            crate::skills::SourceScope::Project
        );
        // The loser surfaces as a collision diagnostic.
        assert!(resources
            .skill_diagnostics
            .iter()
            .any(|d| matches!(d, ResourceDiagnostic::Collision { .. })));
    }
}
