// The Tier-C/D ruling (fleet-uniform, 2026-09-28): stack-resident futures
// by design on hot paths (boxing 130 fns is allocation-churn with zero
// correctness gain); the fn-length threshold is a style gate, not
// correctness (the harness fns are intentionally linear); 64-bit targets -
// the narrowing sits at OS/protocol boundaries where the values are
// bounded (pid syscalls, epoch/elapsed milliseconds, calendar math,
// guarded parses), and checked conversions would add panic paths where
// silent wrap was deliberate (the one genuinely-suspect family, args.rs's
// parse_positive_u32 lacking its u32::MAX bound, is flagged in the lane
// dossier for the conductor).
#![allow(
    clippy::large_futures,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::cast_precision_loss
)]

//! eukhe-cli: the `eukhe` binary. The argument surface, command routing,
//! help output, and validation are faithful ports of the TypeScript product's
//! `packages/coding-agent/src/main.ts` and `src/cli/*.ts`. Runtime execution
//! lives behind the [`mode::Runtime`] boundary.

use std::path::{Path, PathBuf};

// Internal ported modules are crate-private: the only public API is the
// runtime boundary below.
pub(crate) mod args;
pub(crate) mod budget_command;
pub(crate) mod chat_command;
pub(crate) mod client_settings;
pub(crate) mod command_registry;
pub(crate) mod config;
pub(crate) mod config_command;
pub(crate) mod daemon_command;
pub(crate) mod daemon_discovery;
pub(crate) mod daemon_mode;
pub(crate) mod daemon_session_list;
pub(crate) mod dashboard_command;
pub(crate) mod factory_command;
pub(crate) mod file_processor;
pub(crate) mod gateway_command;
pub(crate) mod global_flags;
pub(crate) mod headless_autonomous;
pub(crate) mod headless_children;
pub(crate) mod headless_session;
pub(crate) mod headless_terminal;
pub(crate) mod headless_wait;
pub(crate) mod incident;
pub(crate) mod initial_message;
pub(crate) mod interactive_mode;
pub(crate) mod json_out;
pub(crate) mod kernel_command;
pub(crate) mod list_models;
pub(crate) mod mcp_command;
pub(crate) mod mcp_login;
pub(crate) mod mode;
pub(crate) mod package_command;
pub(crate) mod prompt_command;
pub(crate) mod provider_command;
pub(crate) mod provider_login;
pub(crate) mod public_command;
pub(crate) mod sanitize;
pub(crate) mod session_export;
pub(crate) mod sessions_table_format;
pub(crate) mod styling;
pub(crate) mod subscription_login;
pub(crate) mod tiny_command;
pub(crate) mod tiny_models_command;
pub(crate) mod update_command;

/// The runtime boundary: everything a mode-runner crate implements to plug
/// into the `eukhe` binary, plus the entry point that drives it.
pub use mode::{AppMode, MissingSubsystem, RunOptions, Runtime, UnavailableRuntime};
pub(crate) mod piped_stdin;
pub mod print_runtime;
pub mod util_time;
pub use print_runtime::PrintRuntime;

/// Daemon wiring shared by the interactive runtime and the integration
/// tests: spawn/probe the supervisor on a socket, and map `--daemon-socket`.
pub use interactive_mode::{
    ensure_daemon_running, ensure_daemon_running_with, resolve_socket_path,
};

/// Entry point shared by the binary and the integration tests. Returns the
/// process exit code.
pub fn main_with_runtime(args: &[String], runtime: &dyn mode::Runtime) -> i32 {
    match main_impl(args, runtime) {
        Ok(code) => code,
        Err(error) => {
            eprintln!("Error: {error}");
            error.exit_code()
        }
    }
}

/// Why the CLI stopped before (or instead of) a mode runner; printed once
/// as `Error: <error>` with exit 1.
#[derive(Debug, thiserror::Error)]
enum CliError {
    #[error("attach requires an interactive terminal")]
    AttachNeedsTerminal,
    #[error("agents requires an interactive terminal; `eukhe list` prints the agents")]
    AgentsNeedsTerminal,
    #[error("--resume without a session selector requires an interactive terminal")]
    BareResumeNeedsTerminal,
    #[error("reading the working directory: {0}")]
    ExportCwd(#[source] std::io::Error),
    #[error(transparent)]
    Export(#[from] session_export::SessionExportError),
    #[error("@file arguments are not supported in RPC, daemon, or ACP mode")]
    FileArgsInProtocolMode,
    #[error("--fork cannot be combined with {}", .0.join(", "))]
    ForkConflict(Vec<&'static str>),
    /// The process working directory cannot be read.
    #[error("{0}")]
    CurrentDir(#[source] std::io::Error),
    /// `--cwd` names a directory the process cannot enter (the Node.js
    /// `chdir` message of the TS product).
    #[error("Cannot use cwd {}: {}", .to.display(), node_style_error(.source, "chdir", .from, .to))]
    Chdir {
        from: PathBuf,
        to: PathBuf,
        #[source]
        source: std::io::Error,
    },
    #[error("EUKHE_STARTUP_BENCHMARK only supports interactive mode")]
    StartupBenchmarkMode,
    #[error("{0:#}")]
    SessionDir(#[source] anyhow::Error),
    #[error(transparent)]
    PromptFile(#[from] mode::PromptFileError),
    #[error("this invocation needs {}, which is not linked into the binary yet", .0.subsystem_name())]
    Missing(#[source] mode::MissingSubsystem),
    /// The daemon worker's tokio runtime did not start.
    #[error("{0}")]
    WorkerRuntime(#[source] std::io::Error),
    #[error("{0:#}")]
    Worker(#[source] anyhow::Error),
}

impl CliError {
    /// The exit class: the terminal refusals, flag-shape and cwd errors are
    /// usage or missing-input failures (2); everything else is operational.
    fn exit_code(&self) -> i32 {
        match self {
            Self::AttachNeedsTerminal
            | Self::AgentsNeedsTerminal
            | Self::BareResumeNeedsTerminal
            | Self::FileArgsInProtocolMode
            | Self::ForkConflict(_)
            | Self::Chdir { .. }
            | Self::StartupBenchmarkMode
            | Self::PromptFile(_) => 2,
            Self::ExportCwd(_)
            | Self::Export(_)
            | Self::CurrentDir(_)
            | Self::SessionDir(_)
            | Self::Missing(_)
            | Self::WorkerRuntime(_)
            | Self::Worker(_) => 1,
        }
    }
}

fn main_impl(args: &[String], runtime: &dyn mode::Runtime) -> Result<i32, CliError> {
    use std::io::IsTerminal;

    let offline_mode = args.iter().any(|arg| arg == "--offline")
        || crate::config::is_truthy_env_flag(
            std::env::var(crate::config::ENV_OFFLINE).ok().as_deref(),
        );
    if offline_mode {
        std::env::set_var(crate::config::ENV_OFFLINE, "1");
    }

    // The shared tiny-model worker the tiny client spawns (hidden: never a
    // public command): `eukhe tiny-worker <model> --backend onnx ...`.
    if args.first().map(String::as_str) == Some("tiny-worker") {
        return Ok(tiny_command::run_tiny_worker(&args[1..]));
    }

    // Public command routing: help requests, removed commands, management
    // commands, and the model/session rewrites.
    let public_command = public_command::handle_public_command(args);
    if public_command.handled {
        return Ok(public_command.exit_code.unwrap_or(0));
    }
    let args = public_command.args;

    if args.first().map(String::as_str) == Some("config") {
        return Ok(crate::config_command::run());
    }

    let parsed = args::parse_args(&args);
    // Help is recognized before any other validation: a `--help` anywhere
    // prints help and exits 0, even next to invalid options. `--version`
    // comes next; only then do the parse diagnostics fail the run.
    if parsed.help {
        println!("{}", command_registry::format_top_level_help());
        return Ok(0);
    }
    if parsed.version {
        println!("{}", crate::config::version());
        return Ok(0);
    }
    if !parsed.diagnostics.is_empty() {
        for diagnostic in &parsed.diagnostics {
            let label = if diagnostic.is_error {
                "Error"
            } else {
                "Warning"
            };
            eprintln!("{label}: {}", diagnostic.message);
        }
        if parsed.diagnostics.iter().any(|d| d.is_error) {
            return Ok(2);
        }
    }

    let app_mode = mode::AppMode::resolve(&parsed, std::io::stdin().is_terminal());

    if public_command.attach_agent.is_some() && app_mode != mode::AppMode::Interactive {
        return Err(CliError::AttachNeedsTerminal);
    }
    if public_command.explicit_agents_view && app_mode != mode::AppMode::Interactive {
        return Err(CliError::AgentsNeedsTerminal);
    }
    if parsed.resume_bare && app_mode != mode::AppMode::Interactive {
        return Err(CliError::BareResumeNeedsTerminal);
    }

    if parsed.export.is_some() {
        // The TS product only reaches the export subsystem through the
        // `session export <file> [output]` rewrite; a standalone `--export`
        // already exited as a removed-flag diagnostic above.
        let cwd = std::env::current_dir().map_err(CliError::ExportCwd)?;
        return Ok(session_export::run(
            &parsed,
            &cwd,
            &crate::config::get_agent_dir(),
        )?);
    }

    if matches!(
        parsed.mode,
        Some(args::Mode::Rpc | args::Mode::Daemon | args::Mode::Acp)
    ) && !parsed.file_args.is_empty()
    {
        return Err(CliError::FileArgsInProtocolMode);
    }

    // Daemon worker processes start with the worker role env var set (TS
    // `isDaemonWorkerProcess`, scoped to daemon-mode argv, checked after the
    // shared mode validations): route straight into the worker runtime. The
    // supervisor launches workers as `eukhe worker`.
    let is_worker_process =
        std::env::var(eukhe_daemon::worker::WORKER_ROLE_ENV).unwrap_or_default() == "1";
    if is_worker_process
        && (args.first().map(String::as_str) == Some("worker")
            || args.windows(2).any(|pair| pair == ["--mode", "daemon"]))
    {
        return run_worker_mode();
    }

    if let Some(fork) = &parsed.fork {
        let mut conflicting_flags: Vec<&str> = Vec::new();
        if parsed.continue_ {
            conflicting_flags.push("--continue");
        }
        if parsed.has_resume() {
            conflicting_flags.push("--resume");
        }
        if parsed.no_session {
            conflicting_flags.push("--no-session");
        }
        if !conflicting_flags.is_empty() {
            return Err(CliError::ForkConflict(conflicting_flags));
        }
        let _ = fork;
    }

    // cwd: chdir before anything cwd-bound runs.
    let cwd = match &parsed.cwd {
        Some(cwd) => {
            let cwd = crate::config::expand_tilde_path(cwd);
            let from = std::env::current_dir().map_err(CliError::CurrentDir)?;
            if let Err(source) = std::env::set_current_dir(&cwd) {
                return Err(CliError::Chdir {
                    from,
                    to: cwd,
                    source,
                });
            }
            std::env::current_dir().map_err(CliError::CurrentDir)?
        }
        None => std::env::current_dir().map_err(CliError::CurrentDir)?,
    };

    if crate::config::is_truthy_env_flag(
        std::env::var(crate::config::ENV_STARTUP_BENCHMARK)
            .ok()
            .as_deref(),
    ) && app_mode != mode::AppMode::Interactive
    {
        return Err(CliError::StartupBenchmarkMode);
    }

    let agent_dir = crate::config::get_agent_dir();
    // The one sessionDir precedence (flag, environment, the cwd-scoped
    // setting, default); the default stays `None` here, the agent dir's
    // `sessions`.
    let session_dir = eukhe_core::settings::resolve_session_dir(
        parsed.session_dir.as_deref().map(std::path::Path::new),
        &eukhe_core::settings::SettingsManager::create(&cwd, &agent_dir),
        &agent_dir,
    )
    .map_err(CliError::SessionDir)?;
    let session_dir = (session_dir.source != eukhe_core::settings::SessionDirSource::Default)
        .then_some(session_dir.path);

    let mut cli_messages = parsed.messages.clone();
    // TS main's startup branches read piped stdin for every mode but the
    // stdio-protocol ones (rpc/acp/daemon keep stdin for the transport),
    // with the idle window so an open, silent pipe cannot hang the boot.
    let stdin_content = if matches!(app_mode, AppMode::Rpc | AppMode::Acp | AppMode::Daemon) {
        None
    } else {
        piped_stdin::read_piped_stdin(piped_stdin::resolve_stdin_idle_timeout_ms(
            std::env::var(piped_stdin::STDIN_IDLE_TIMEOUT_MS_ENV)
                .ok()
                .as_deref(),
        ))
    };
    // TS `prepareInitialMessage`: `@file` arguments expand into text and
    // image attachments for the initial prompt; the file blocks ride
    // every mode's first message, the images the non-interactive prompt.
    let (file_text, initial_images) = if parsed.file_args.is_empty() {
        (None, Vec::new())
    } else {
        let auto_resize =
            eukhe_core::settings::SettingsManager::create(&cwd, &agent_dir).get_image_auto_resize();
        match file_processor::process_file_arguments(&parsed.file_args, &cwd, auto_resize) {
            Ok(processed) => (
                Some(processed.text).filter(|text| !text.is_empty()),
                processed.images,
            ),
            Err(error) => {
                // TS prints the failure through chalk on stderr and exits.
                eprintln!("{}", error.message);
                return Ok(1);
            }
        }
    };
    let initial_message = initial_message::build_initial_message(
        &mut cli_messages,
        file_text.as_deref(),
        stdin_content.as_deref(),
    )
    .initial_message;
    let config = match mode::runtime_config_from_args(
        &parsed,
        cwd,
        agent_dir,
        session_dir.clone(),
        app_mode,
    ) {
        Ok(config) => config,
        Err(error) => {
            eprintln!("Error: {error}");
            return Ok(2);
        }
    };
    let options = mode::RunOptions {
        app_mode,
        config,
        session: mode::SessionOptions {
            continue_recent: parsed.continue_,
            resume_bare: parsed.resume_bare,
            resume: parsed.resume.clone(),
            fork: parsed.fork.clone(),
            no_session: parsed.no_session,
            session_dir,
            cwd_from_flag: parsed.cwd.is_some(),
        },
        messages: cli_messages,
        initial_message,
        initial_images,
        file_args: parsed.file_args.clone(),
        daemon_socket: parsed.daemon_socket.clone(),
        list_models: parsed.list_models,
        verbose: parsed.verbose,
        offline: parsed.offline,
        agents_view_requested: public_command.explicit_agents_view,
        attach_agent: public_command.attach_agent,
    };

    runtime.run(&options).map_err(CliError::Missing)
}

/// Run the daemon session-worker runtime (the process the supervisor spawns
/// for each live session).
fn run_worker_mode() -> Result<i32, CliError> {
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .map_err(CliError::WorkerRuntime)?;
    runtime
        .block_on(eukhe_daemon::worker::run_worker())
        .map_err(CliError::Worker)?;
    Ok(0)
}

/// Format an io error the way Node.js prints it for the same syscall, so the
/// `Error: Cannot use cwd <dir>: <message>` text matches the TS product.
fn node_style_error(error: &std::io::Error, syscall: &str, from: &Path, to: &Path) -> String {
    let (from, to) = (from.display(), to.display());
    match error.kind() {
        std::io::ErrorKind::NotFound => {
            format!("ENOENT: no such file or directory, {syscall} '{from}' -> '{to}'")
        }
        std::io::ErrorKind::NotADirectory => {
            format!("ENOTDIR: not a directory, {syscall} '{from}' -> '{to}'")
        }
        std::io::ErrorKind::PermissionDenied => {
            format!("EACCES: permission denied, {syscall} '{from}' -> '{to}'")
        }
        _ => error.to_string(),
    }
}
