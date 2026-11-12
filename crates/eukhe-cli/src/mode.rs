//! The runtime boundary: typed execution modes and options, mirroring the
//! `resolveAppMode` / `runtimeConfigFromArgs` split in `main.ts`. Crates that
//! provide the real runtime (eukhe-core session engine, eukhe-daemon workers,
//! eukhe-tui) plug in behind [`Runtime::run`] at merge time.

use std::path::PathBuf;

use eukhe_core::durable::SessionHost;
use eukhe_core::resources::SystemPromptInput;
use eukhe_types::acceptance::{AcceptanceSeed, CheckSpec};

use crate::args::{Args, AutonomousConfig, Mode};

/// The process-level execution mode, mirroring `AppMode` in main.ts.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AppMode {
    Interactive,
    Print,
    Json,
    Rpc,
    Acp,
    Daemon,
}

impl AppMode {
    /// Resolve the execution mode from parsed args and stdin TTY state,
    /// mirroring `resolveAppMode`.
    #[must_use]
    pub fn resolve(parsed: &Args, stdin_is_tty: bool) -> AppMode {
        match parsed.mode {
            Some(Mode::Daemon) => AppMode::Daemon,
            Some(Mode::Rpc) => AppMode::Rpc,
            Some(Mode::Acp) => AppMode::Acp,
            Some(Mode::Json) => AppMode::Json,
            _ => {
                if parsed.print || !stdin_is_tty {
                    AppMode::Print
                } else {
                    AppMode::Interactive
                }
            }
        }
    }

    #[must_use]
    pub fn as_str(&self) -> &'static str {
        match self {
            AppMode::Interactive => "interactive",
            AppMode::Print => "print",
            AppMode::Json => "json",
            AppMode::Rpc => "rpc",
            AppMode::Acp => "acp",
            AppMode::Daemon => "daemon",
        }
    }

    /// How a session this mode opens is hosted: print and json mode close
    /// it once its runs settle and the process exits; every other mode
    /// keeps it open between runs.
    #[must_use]
    pub fn session_host(self) -> SessionHost {
        match self {
            AppMode::Print | AppMode::Json => SessionHost::EndsWithRuns,
            AppMode::Interactive | AppMode::Rpc | AppMode::Acp | AppMode::Daemon => {
                SessionHost::Resident
            }
        }
    }
}

/// A seeded persistent goal (`initialGoal` in the runtime config).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InitialGoal {
    pub objective: String,
    /// `--goal-token-budget`: a token limit on the session's budget.
    pub token_budget: Option<u32>,
}

/// The acceptance checks the `--accept-*` flags ask for: each command
/// must exit 0, each condition goes to the judge with the output of the
/// `--accept-evidence` commands, and the intent judge joins them unless
/// `--accept-no-intent`; `None` without a check and `--accept-intent`.
fn acceptance_seed(parsed: &Args) -> Option<AcceptanceSeed> {
    let commands = parsed.accept_cmds.iter().map(|command| CheckSpec::Command {
        command: command.clone(),
        expect: 0,
        timeout_ms: None,
        protect: Vec::new(),
    });
    let conditions = parsed
        .accept_judges
        .iter()
        .map(|condition| CheckSpec::Judge {
            condition: condition.clone(),
            evidence: parsed.accept_evidence.clone(),
            model: None,
        });
    let checks: Vec<CheckSpec> = commands.chain(conditions).collect();
    (!checks.is_empty() || parsed.accept_intent).then(|| AcceptanceSeed {
        checks,
        max_returns: parsed.accept_returns.map(u64::from),
        intent: !parsed.accept_no_intent,
    })
}

/// The default `--wait-limit-ms`: one hour.
const DEFAULT_WAIT_LIMIT_MS: u64 = 3_600_000;

/// The typed per-session runtime configuration, mirroring
/// `AgentSessionRuntimeConfig`. This is the API boundary the eukhe-core/eukhe-ai
/// crates consume at merge time.
#[derive(Debug, Clone, Default)]
#[allow(clippy::struct_excessive_bools)] // the mirrored `AgentSessionRuntimeConfig` API shape is deliberate
pub struct RuntimeConfig {
    pub cwd: PathBuf,
    pub agent_dir: PathBuf,
    pub session_dir: Option<PathBuf>,
    pub provider: Option<String>,
    pub model: Option<String>,
    pub api_key: Option<String>,
    /// The replacement prompt input. A file path is absolute.
    pub system_prompt: Option<SystemPromptInput>,
    /// The appended prompt inputs, in order. A file path is absolute.
    pub append_system_prompt: Vec<SystemPromptInput>,
    pub thinking: Option<eukhe_types::ai::ModelThinkingLevel>,
    pub models: Option<Vec<String>>,
    pub skills: Vec<PathBuf>,
    pub no_skills: bool,
    pub prompt_templates: Vec<PathBuf>,
    pub no_prompt_templates: bool,
    pub themes: Vec<PathBuf>,
    pub no_themes: bool,
    pub no_context_files: bool,
    pub autonomous: Option<AutonomousConfig>,
    pub serialized_refine: bool,
    pub initial_goal: Option<InitialGoal>,
    /// The `--budget-*` limits: the budget of the session this run starts
    /// (`None`: no flag was given, the session gets no budget).
    pub budget: Option<eukhe_types::budget::BudgetLimits>,
    /// The acceptance checks of `--accept-cmd` and `--accept-judge`: the
    /// run counts as done only when each passes on the final state.
    pub acceptance: Option<AcceptanceSeed>,
    /// How long print/json mode waits for the session to go quiescent
    /// (background jobs and subagents settled) after a turn ends.
    pub wait_limit: std::time::Duration,
}

/// Session selection options that stay client-side.
#[derive(Debug, Clone, Default)]
#[allow(clippy::struct_excessive_bools)] // the selection's flag set is the deliberate client-side surface
pub struct SessionOptions {
    /// `--continue`/`-c`: the launch reopens the newest saved session for
    /// the cwd (TS `SessionManager.continueRecent`) and falls back to a
    /// fresh session without a candidate.
    pub continue_recent: bool,
    pub resume_bare: bool,
    pub resume: Option<String>,
    pub fork: Option<String>,
    pub no_session: bool,
    pub session_dir: Option<PathBuf>,
    /// True when `--cwd` selected the working directory; resumed sessions
    /// then use that directory instead of the header cwd (main.ts
    /// `explicitCwdOverride`).
    pub cwd_from_flag: bool,
}

/// Everything the CLI hands to the runtime, mirroring what `main.ts` computes
/// before entering the mode runners.
#[derive(Debug, Clone)]
pub struct RunOptions {
    pub app_mode: AppMode,
    pub config: RuntimeConfig,
    pub session: SessionOptions,
    pub messages: Vec<String>,
    pub file_args: Vec<String>,
    pub daemon_socket: Option<String>,
    pub list_models: Option<Option<String>>,
    /// The combined first prompt (stdin + @file text + first message).
    pub initial_message: Option<String>,
    /// The `@file` image attachments for the initial prompt (TS
    /// `initialImages`; only the non-interactive prompt path sends them -
    /// the interactive initial-message image arm is not yet wired).
    pub initial_images: Vec<eukhe_types::pi_ai::ImageContent>,
    pub verbose: bool,
    pub offline: bool,
    pub agents_view_requested: bool,
    pub attach_agent: Option<String>,
}

/// A missing runtime subsystem, reported as a typed error instead of faked
/// output. The enum makes the merge-time work explicit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MissingSubsystem {
    SessionEngine,
    ModelRegistry,
    PackageManager,
}

impl MissingSubsystem {
    #[must_use]
    pub fn subsystem_name(&self) -> &'static str {
        match self {
            MissingSubsystem::SessionEngine => "the session engine (eukhe-core)",
            MissingSubsystem::ModelRegistry => "the model registry (eukhe-ai)",
            MissingSubsystem::PackageManager => "the capability package manager (eukhe-core)",
        }
    }
}

impl std::fmt::Display for MissingSubsystem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.subsystem_name())
    }
}

impl std::error::Error for MissingSubsystem {}

/// The runtime boundary. `run` executes the requested mode; the current build
/// has only the [`UnavailableRuntime`] implementation, which produces typed
/// [`MissingSubsystem`] errors for every mode that needs unmerged crates.
pub trait Runtime {
    /// Execute the requested mode.
    ///
    /// # Errors
    /// Returns a [`MissingSubsystem`] error naming the subsystem the
    /// requested mode needs when it is not linked into the binary.
    fn run(&self, options: &RunOptions) -> Result<i32, MissingSubsystem>;
}

/// The merge-time placeholder runtime: it never fakes output, it fails loudly
/// with the precise missing subsystem for the requested mode.
#[derive(Debug, Clone, Copy, Default)]
pub struct UnavailableRuntime;

impl Runtime for UnavailableRuntime {
    fn run(&self, options: &RunOptions) -> Result<i32, MissingSubsystem> {
        if options.list_models.is_some() {
            return Err(MissingSubsystem::ModelRegistry);
        }
        let _ = options.app_mode;
        Err(MissingSubsystem::SessionEngine)
    }
}

/// A `--system-prompt-file` / `--append-system-prompt-file` that cannot
/// be used; the run stops before a session starts.
#[derive(Debug, thiserror::Error)]
pub enum PromptFileError {
    #[error("{flag} {}: {} is not a file", .file.display(), .path.display())]
    NotAFile {
        flag: &'static str,
        file: PathBuf,
        path: PathBuf,
    },
    #[error("{flag} {}: cannot read {}: {source}", .file.display(), .path.display())]
    Unreadable {
        flag: &'static str,
        file: PathBuf,
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
}

/// Build the runtime config from parsed args, mirroring `runtimeConfigFromArgs`.
///
/// # Errors
///
/// A `--system-prompt-file` or `--append-system-prompt-file` that cannot
/// be opened or is not a file.
pub fn runtime_config_from_args(
    parsed: &Args,
    cwd: PathBuf,
    agent_dir: PathBuf,
    session_dir: Option<PathBuf>,
    app_mode: AppMode,
) -> Result<RuntimeConfig, PromptFileError> {
    // isLocalPath (the compiled core's): only npm:/git:/github:/http(s):/ssh:
    // sources are not local; everything else resolves against the session
    // cwd (utils/paths.ts).
    let resolve_cli_path = |paths: &[String]| -> Vec<PathBuf> {
        paths
            .iter()
            .map(|value| {
                if eukhe_bend::rules::package_source::is_local(value) {
                    if std::path::Path::new(value).is_absolute() {
                        PathBuf::from(value)
                    } else {
                        cwd.join(value)
                    }
                } else {
                    PathBuf::from(value)
                }
            })
            .collect()
    };
    let skills = resolve_cli_path(&parsed.skills);
    let prompt_templates = resolve_cli_path(&parsed.prompt_templates);
    let themes = resolve_cli_path(&parsed.themes);
    // A prompt file resolves against the session cwd, like `--skill`. A file
    // that cannot be opened stops the run here, before a session starts.
    let resolve_prompt_input = |input: &SystemPromptInput,
                                flag: &'static str|
     -> Result<SystemPromptInput, PromptFileError> {
        match input {
            SystemPromptInput::Text(text) => Ok(SystemPromptInput::Text(text.clone())),
            SystemPromptInput::File { file } => {
                let path = cwd.join(file);
                match std::fs::File::open(&path).and_then(|opened| opened.metadata()) {
                    Ok(metadata) if metadata.is_file() => {
                        Ok(SystemPromptInput::File { file: path })
                    }
                    Ok(_) => Err(PromptFileError::NotAFile {
                        flag,
                        file: file.clone(),
                        path,
                    }),
                    Err(source) => Err(PromptFileError::Unreadable {
                        flag,
                        file: file.clone(),
                        path,
                        source,
                    }),
                }
            }
        }
    };
    let system_prompt = parsed
        .system_prompt
        .as_ref()
        .map(|input| resolve_prompt_input(input, "--system-prompt-file"))
        .transpose()?;
    let append_system_prompt = parsed
        .append_system_prompt
        .iter()
        .map(|input| resolve_prompt_input(input, "--append-system-prompt-file"))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(RuntimeConfig {
        cwd,
        agent_dir,
        session_dir,
        provider: parsed.provider.clone(),
        model: parsed.model.clone(),
        api_key: parsed.api_key.clone(),
        system_prompt,
        append_system_prompt,
        thinking: parsed.thinking,
        models: parsed.models.clone(),
        skills,
        no_skills: parsed.no_skills,
        prompt_templates,
        no_prompt_templates: parsed.no_prompt_templates,
        themes,
        no_themes: parsed.no_themes,
        no_context_files: parsed.no_context_files,
        autonomous: AutonomousConfig::from_args(parsed),
        // Serialized refine is only used by print/json/rpc clients.
        serialized_refine: !matches!(app_mode, AppMode::Interactive | AppMode::Daemon),
        initial_goal: parsed.goal.as_ref().map(|objective| InitialGoal {
            objective: objective.clone(),
            token_budget: parsed.goal_token_budget,
        }),
        budget: (!parsed.budget.is_unlimited()).then_some(parsed.budget),
        acceptance: acceptance_seed(parsed),
        wait_limit: std::time::Duration::from_millis(
            parsed.wait_limit_ms.unwrap_or(DEFAULT_WAIT_LIMIT_MS),
        ),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn seed_of(args: &[&str]) -> Option<AcceptanceSeed> {
        let args: Vec<String> = args.iter().map(|arg| (*arg).to_owned()).collect();
        acceptance_seed(&crate::args::parse_args(&args))
    }

    /// The intent judge joins the `--accept-*` checks unless
    /// `--accept-no-intent`; `--accept-intent` alone verifies by intent;
    /// no flag sets no checks.
    #[test]
    fn acceptance_flags_seed_the_checks_with_the_intent_judge() {
        let command = CheckSpec::Command {
            command: "true".to_owned(),
            expect: 0,
            timeout_ms: None,
            protect: Vec::new(),
        };
        assert_eq!(
            seed_of(&["-p", "--accept-cmd", "true", "go"]).map(|seed| seed.specs()),
            Some(vec![command.clone(), CheckSpec::intent()])
        );
        assert_eq!(
            seed_of(&["-p", "--accept-cmd", "true", "--accept-no-intent", "go"])
                .map(|seed| seed.specs()),
            Some(vec![command])
        );
        assert_eq!(
            seed_of(&["-p", "--accept-intent", "go"]).map(|seed| seed.specs()),
            Some(vec![CheckSpec::intent()])
        );
        assert_eq!(seed_of(&["-p", "go"]), None);
    }

    /// `--system-prompt-file ./missing.md` is an error, never the path as
    /// prompt text.
    #[test]
    fn a_missing_system_prompt_file_is_an_error() {
        let cwd = tempfile::tempdir().expect("tempdir");
        let parsed = crate::args::parse_args(&[
            "--system-prompt-file".to_string(),
            "./missing.md".to_string(),
        ]);
        let path = cwd.path().join("./missing.md");
        let io_error = std::fs::File::open(&path).expect_err("the file is missing");
        let Err(error) = runtime_config_from_args(
            &parsed,
            cwd.path().to_path_buf(),
            cwd.path().join("agent"),
            None,
            AppMode::Print,
        ) else {
            panic!("a missing prompt file is an error");
        };
        assert_eq!(
            error.to_string(),
            format!(
                "--system-prompt-file ./missing.md: cannot read {}: {io_error}",
                path.display()
            )
        );
    }

    /// The `--budget-*` flags are the run's budget; without one the run
    /// sets none.
    #[test]
    fn budget_flags_become_the_budget_of_the_run() {
        let cwd = tempfile::tempdir().expect("tempdir");
        let budget = |args: &[&str]| {
            let args: Vec<String> = args.iter().map(ToString::to_string).collect();
            runtime_config_from_args(
                &crate::args::parse_args(&args),
                cwd.path().to_path_buf(),
                cwd.path().join("agent"),
                None,
                AppMode::Print,
            )
            .expect("runtime config")
            .budget
        };
        assert_eq!(
            [
                budget(&["--budget-tokens", "200k", "--budget-time", "10m"]),
                budget(&["-p", "hello"]),
            ],
            [
                Some(eukhe_types::budget::BudgetLimits {
                    tokens: Some(200_000),
                    time_ms: Some(600_000),
                    ..Default::default()
                }),
                None,
            ]
        );
    }
}
