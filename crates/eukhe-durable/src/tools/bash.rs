//! The `bash` and `powershell` tools. Port of `tools/bash.ts`.

use std::collections::BTreeMap;
use std::fmt;
use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_chord::json::JsonNumber;
use eukhe_pi_ai::typebox::{Options, TSchema, Type};
use futures::future::BoxFuture;
use serde::Deserialize;

use super::env::require_env;
use crate::env::{
    ExecCommand, ExecutionErrorCode, OnShellOutput, ShellExecOptions, ShellSpillOptions,
};
use crate::harness::define::define_tool;
use crate::harness::types::{
    OutputRetain, ToolDiagnostic, ToolDiagnosticSeverity, ToolExecutionApi, ToolExecutionResult,
    ToolOutputChunk, ToolOutputLimits, ToolRegistration,
};
use crate::session::{SessionError, SessionResult};
use crate::truncate::{DEFAULT_MAX_BYTES, DEFAULT_MAX_LINES};

const MAX_TIMEOUT_SECONDS: f64 = 2_147_483_647.0 / 1000.0;

fn command_schema(description: &str) -> TSchema {
    Type::object([
        (
            "command",
            Type::string_with(Options::new().set("description", description)),
        ),
        (
            "timeout",
            Type::optional(Type::number_with(Options::new().set(
                "description",
                "Timeout in seconds (optional, no default timeout)",
            ))),
        ),
    ])
}

/// Arguments of `bash` (TS `BashToolInput`).
#[derive(Debug, Clone, PartialEq, Deserialize)]
pub struct BashToolInput {
    pub command: String,
    #[serde(default)]
    pub timeout: Option<f64>,
}

/// Arguments of `powershell` (TS `PowerShellToolInput`).
pub type PowerShellToolInput = BashToolInput;

/// A command about to run, which `prepare` may change: the script, its
/// working directory and environment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BashExecution {
    pub command: String,
    pub cwd: String,
    pub env: BTreeMap<String, String>,
    pub inherit_env: bool,
}

/// Changes the execution of one call before it runs (TS `BashPrepare`).
pub type BashPrepare = Arc<
    dyn for<'a> Fn(
            &'a mut BashExecution,
            &'a Arc<dyn ToolExecutionApi>,
            &'a Context,
        ) -> BoxFuture<'a, SessionResult<()>>
        + Send
        + Sync,
>;

/// Options of [`create_bash_tool`].
#[derive(Clone, Default)]
pub struct BashToolOptions {
    pub command_prefix: Option<String>,
    pub prepare: Option<BashPrepare>,
}

impl fmt::Debug for BashToolOptions {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("BashToolOptions")
            .field("command_prefix", &self.command_prefix)
            .field("prepare", &self.prepare.is_some())
            .finish()
    }
}

/// Options of [`create_powershell_tool`].
#[derive(Clone, Default)]
pub struct PowerShellToolOptions {
    /// Lines run before each command.
    pub command_prefix: Option<String>,
    pub prepare: Option<BashPrepare>,
    /// PowerShell programs to try in order; default `pwsh`, then
    /// `powershell`. A program that cannot start is skipped.
    pub programs: Option<Vec<String>>,
}

impl fmt::Debug for PowerShellToolOptions {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("PowerShellToolOptions")
            .field("command_prefix", &self.command_prefix)
            .field("prepare", &self.prepare.is_some())
            .field("programs", &self.programs)
            .finish()
    }
}

/// JS `String(number)` of a finite number.
fn js_number(value: f64) -> String {
    JsonNumber::new(value).map_or_else(|| value.to_string(), |number| number.to_string())
}

fn validate_timeout(timeout: Option<f64>) -> SessionResult<()> {
    let Some(timeout) = timeout else {
        return Ok(());
    };
    if !timeout.is_finite() || timeout <= 0.0 {
        return Err(SessionError::error(
            "Invalid timeout: must be a finite number of seconds",
        ));
    }
    if timeout > MAX_TIMEOUT_SECONDS {
        return Err(SessionError::error(format!(
            "Invalid timeout: maximum is {} seconds",
            js_number(MAX_TIMEOUT_SECONDS)
        )));
    }
    Ok(())
}

/// The execution of one call: the command with its prefix, in the
/// environment's working directory, then `prepare`.
async fn prepare_execution(
    command: String,
    command_prefix: Option<&str>,
    prepare: Option<&BashPrepare>,
    api: &Arc<dyn ToolExecutionApi>,
    cx: &Context,
) -> SessionResult<BashExecution> {
    let mut execution = BashExecution {
        command: match command_prefix {
            Some(prefix) if !prefix.is_empty() => format!("{prefix}\n{command}"),
            Some(_) | None => command,
        },
        cwd: require_env(api.as_ref())?.cwd().to_owned(),
        env: BTreeMap::new(),
        inherit_env: true,
    };
    if let Some(prepare) = prepare {
        prepare(&mut execution, api, cx).await?;
    }
    Ok(execution)
}

/// Run each command form in turn until one starts, streaming output to
/// `api.output()` within the retained window, and turn the result into the
/// tool's outcome: a spill diagnostic, and a thrown error for a failure or a
/// nonzero exit.
async fn run_command(
    commands: &[ExecCommand],
    execution: &BashExecution,
    timeout: Option<f64>,
    api: &Arc<dyn ToolExecutionApi>,
    cx: &Context,
) -> SessionResult<()> {
    let env = require_env(api.as_ref())?;
    let on_output: OnShellOutput = {
        let api = Arc::clone(api);
        Arc::new(move |text, _cx, info| {
            api.output(ToolOutputChunk::Text(text), info.skipped)
                .map_err(Into::into)
        })
    };
    let options = ShellExecOptions {
        cwd: Some(execution.cwd.clone()),
        env: Some(execution.env.clone()),
        inherit_env: Some(execution.inherit_env),
        timeout,
        on_output: Some(on_output),
        spill: Some(ShellSpillOptions {
            after_bytes: DEFAULT_MAX_BYTES,
            after_lines: DEFAULT_MAX_LINES,
        }),
        // An environment may then omit output outside the retained tail and report the omission.
        window: api.output_window(),
    };
    let mut result = None;
    for command in commands {
        let attempt = env.exec(command, &options, cx).await;
        // A program that could not start produced no output; the next form may.
        let started =
            !matches!(&attempt, Err(error) if error.code == ExecutionErrorCode::SpawnError);
        result = Some(attempt);
        if started {
            break;
        }
    }
    let Some(result) = result else {
        return Err(SessionError::error("No command to run"));
    };
    let spill_path = match &result {
        Ok(value) => value.spill_path.as_ref(),
        Err(error) => error.spill_path.as_ref(),
    };
    if let Some(spill_path) = spill_path {
        api.diagnostic(ToolDiagnostic {
            severity: ToolDiagnosticSeverity::Info,
            code: Some("full_output".to_owned()),
            message: format!("Full output: {spill_path}"),
        })?;
    }
    match result {
        Err(error) => match error.code {
            ExecutionErrorCode::Aborted if cx.aborted() => Err(error.into()),
            ExecutionErrorCode::Timeout => Err(SessionError::error(format!(
                "Command timed out after {} seconds",
                timeout.map_or_else(|| "undefined".to_owned(), js_number)
            ))),
            ExecutionErrorCode::Aborted => Err(SessionError::error("Command aborted")),
            ExecutionErrorCode::ShellUnavailable
            | ExecutionErrorCode::SpawnError
            | ExecutionErrorCode::CallbackError
            | ExecutionErrorCode::Unknown => Err(error.into()),
        },
        Ok(value) if value.exit_code != 0 => Err(SessionError::error(format!(
            "Command exited with code {}",
            value.exit_code
        ))),
        Ok(_) => Ok(()),
    }
}

fn tail_limits() -> ToolOutputLimits {
    ToolOutputLimits {
        retain: Some(OutputRetain::Tail),
        ..ToolOutputLimits::default()
    }
}

fn input(args: eukhe_types::pi_ai::JsonValue) -> SessionResult<BashToolInput> {
    serde_json::from_value(args).map_err(SessionError::other)
}

/// Runs a command through the environment's shell. Its output streams to
/// `api.output()`, where the Harness keeps the tail within the default
/// limits; the result content is that retained output. The retained window
/// goes to the environment, which may omit output outside it and report how
/// much it omitted, so dropped counts stay exact. Output beyond the limits is
/// spilled to a file whose path is reported as a diagnostic. A nonzero exit
/// or timeout throws, which makes an error result that still carries the
/// output and diagnostics.
#[must_use]
pub fn create_bash_tool(options: BashToolOptions) -> Arc<ToolRegistration> {
    let options = Arc::new(options);
    let mut tool = ToolRegistration::new(
        "bash",
        format!(
            "Execute a bash command in the current working directory. Returns combined stdout and stderr. Output is truncated to last {DEFAULT_MAX_LINES} lines or {}KB (whichever is hit first). If truncated, full output is saved to a temp file. Optionally provide a timeout in seconds.",
            DEFAULT_MAX_BYTES / 1024
        ),
        command_schema("Bash command to execute"),
        move |args, api, cx| {
            let options = Arc::clone(&options);
            async move {
                let args = input(args)?;
                validate_timeout(args.timeout)?;
                let execution = prepare_execution(
                    args.command,
                    options.command_prefix.as_deref(),
                    options.prepare.as_ref(),
                    &api,
                    &cx,
                )
                .await?;
                let command = ExecCommand::Shell(execution.command.clone());
                run_command(&[command], &execution, args.timeout, &api, &cx).await?;
                Ok(ToolExecutionResult::default())
            }
        },
    );
    tool.output_limits = Some(tail_limits());
    define_tool(tool)
}

/// Output in UTF-8 whatever the console's code page, as the coding agent's
/// `powershell` tool does.
const UTF8_OUTPUT: &str = "try { [Console]::OutputEncoding=[System.Text.Encoding]::UTF8 } catch {}";
const POWERSHELL_ARGS: [&str; 5] = [
    "-NoProfile",
    "-NonInteractive",
    "-ExecutionPolicy",
    "Bypass",
    "-Command",
];

/// Runs a PowerShell command, like `bash` but through PowerShell instead of
/// the environment's shell: `pwsh` (PowerShell 7), else Windows PowerShell,
/// started directly with the command as an argument, so no other shell
/// parses it.
#[must_use]
pub fn create_powershell_tool(options: PowerShellToolOptions) -> Arc<ToolRegistration> {
    let programs = options
        .programs
        .clone()
        .unwrap_or_else(|| vec!["pwsh".to_owned(), "powershell".to_owned()]);
    let options = Arc::new(options);
    let mut tool = ToolRegistration::new(
        "powershell",
        format!(
            "Execute a PowerShell command in the current working directory. Returns combined stdout and stderr. Output is truncated to last {DEFAULT_MAX_LINES} lines or {}KB (whichever is hit first). If truncated, full output is saved to a temp file. Optionally provide a timeout in seconds.",
            DEFAULT_MAX_BYTES / 1024
        ),
        command_schema("PowerShell command to execute"),
        move |args, api, cx| {
            let options = Arc::clone(&options);
            let programs = programs.clone();
            async move {
                let args = input(args)?;
                validate_timeout(args.timeout)?;
                let execution = prepare_execution(
                    args.command,
                    options.command_prefix.as_deref(),
                    options.prepare.as_ref(),
                    &api,
                    &cx,
                )
                .await?;
                let script = format!("{UTF8_OUTPUT}\n{}", execution.command);
                let commands: Vec<ExecCommand> = programs
                    .iter()
                    .map(|program| {
                        let mut command = vec![program.clone()];
                        command.extend(POWERSHELL_ARGS.iter().map(|arg| (*arg).to_owned()));
                        command.push(script.clone());
                        ExecCommand::Argv(command)
                    })
                    .collect();
                run_command(&commands, &execution, args.timeout, &api, &cx).await?;
                Ok(ToolExecutionResult::default())
            }
        },
    );
    tool.output_limits = Some(tail_limits());
    define_tool(tool)
}
