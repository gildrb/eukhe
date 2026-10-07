//! `exec` and `cleanup` of `NativeExecutionEnv`: the `Shell` half of
//! `env/node.ts`.

use std::collections::{BTreeMap, HashSet};
use std::ffi::OsString;
use std::io;
use std::os::unix::process::ExitStatusExt;
use std::process::{ExitStatus, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use eukhe_chord::context::Context;
use nix::sys::signal::{kill, killpg, Signal};
use nix::unistd::Pid;
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWriteExt};
use tokio::time::Instant;
use tokio_util::sync::CancellationToken;

use super::super::decode::StreamDecoder;
use super::super::node_error::{fs_error, uv_code, uv_error_name};
use super::super::{
    ExecCommand, ExecutionError, ExecutionErrorCode, OutputStream, ShellExecOptions,
    ShellExecResult, ShellOutputInfo, ShellSpillOptions, TempFileOptions,
};
use super::{create_temp_file, resolve_path, NativeExecutionEnv};

const MAX_TIMEOUT_MS: f64 = 2_147_483_647.0;
const MAX_TIMEOUT_SECONDS: f64 = MAX_TIMEOUT_MS / 1000.0;
const EXIT_STDIO_GRACE: Duration = Duration::from_millis(100);
/// Bytes read from a pipe at a time, like Node's stream chunks.
const PIPE_CHUNK: usize = 64 * 1024;

/// Test-only slowdown of spill writes, standing in for the TS test's mocked
/// slow `createWriteStream`.
#[cfg(test)]
#[derive(Clone, Debug)]
pub(crate) struct SpillHook {
    pub(crate) write_delay: Duration,
    pub(crate) writes: Arc<std::sync::atomic::AtomicUsize>,
}

/// JS `Number.prototype.toString()` of a finite or infinite double.
pub(crate) fn js_number(value: f64) -> String {
    if value.is_nan() {
        return "NaN".to_owned();
    }
    if value == 0.0 {
        return "0".to_owned();
    }
    if value.is_infinite() {
        return if value > 0.0 { "Infinity" } else { "-Infinity" }.to_owned();
    }
    let sign = if value < 0.0 { "-" } else { "" };
    // Shortest round-trip digits, like the JS algorithm.
    let scientific = format!("{:e}", value.abs());
    let (mantissa, exponent) = scientific.split_once('e').unwrap_or((&scientific, "0"));
    let digits: String = mantissa.chars().filter(char::is_ascii_digit).collect();
    let exponent: i64 = exponent.parse().unwrap_or(0);
    let k = i64::try_from(digits.len()).unwrap_or(i64::MAX);
    let n = exponent + 1;
    let body = if k <= n && n <= 21 {
        format!(
            "{digits}{}",
            "0".repeat(usize::try_from(n - k).unwrap_or(0))
        )
    } else if 0 < n && n <= 21 {
        let split = usize::try_from(n).unwrap_or(0);
        format!("{}.{}", &digits[..split], &digits[split..])
    } else if -6 < n && n <= 0 {
        format!("0.{}{digits}", "0".repeat(usize::try_from(-n).unwrap_or(0)))
    } else {
        let exponent = n - 1;
        let sign = if exponent >= 0 { "+" } else { "-" };
        let (first, rest) = digits.split_at(1);
        let fraction = if rest.is_empty() {
            String::new()
        } else {
            format!(".{rest}")
        };
        format!("{first}{fraction}e{sign}{}", exponent.abs())
    };
    format!("{sign}{body}")
}

fn resolve_timeout_ms(timeout: Option<f64>) -> Result<Option<f64>, ExecutionError> {
    let Some(timeout) = timeout else {
        return Ok(None);
    };
    if !timeout.is_finite() || timeout <= 0.0 {
        return Err(ExecutionError::new(
            ExecutionErrorCode::Timeout,
            "Invalid timeout: must be a finite number of seconds",
        ));
    }
    let timeout_ms = timeout * 1000.0;
    if timeout_ms > MAX_TIMEOUT_MS {
        return Err(ExecutionError::new(
            ExecutionErrorCode::Timeout,
            format!(
                "Invalid timeout: maximum is {} seconds",
                js_number(MAX_TIMEOUT_SECONDS)
            ),
        ));
    }
    Ok(Some(timeout_ms))
}

/// `access(path, F_OK)`, relative paths against the process cwd.
async fn path_exists(path: &str) -> bool {
    tokio::fs::metadata(path).await.is_ok()
}

/// Kill a command's process group, or the process when it has none.
pub(super) fn kill_process_tree(pid: u32) {
    let Ok(pid) = i32::try_from(pid) else {
        return;
    };
    let pid = Pid::from_raw(pid);
    if killpg(pid, Signal::SIGKILL).is_err() {
        // Process already dead when this fails too.
        let _ = kill(pid, Signal::SIGKILL);
    }
}

/// `runCommand`: stdout and exit status of a helper command, killed after
/// `timeout`.
async fn run_command(command: &str, args: &[&str], timeout: Duration) -> (String, Option<i32>) {
    let Ok(mut child) = tokio::process::Command::new(command)
        .args(args)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
    else {
        return (String::new(), None);
    };
    let pid = child.id();
    let mut stdout = child.stdout.take();
    let collect = async {
        let mut bytes = Vec::new();
        if let Some(stdout) = &mut stdout {
            // A read failure ends the output early; the status still decides.
            let _ = stdout.read_to_end(&mut bytes).await;
        }
        let status = child.wait().await;
        (bytes, status)
    };
    tokio::pin!(collect);
    let (bytes, status) = tokio::select! {
        result = &mut collect => result,
        () = tokio::time::sleep(timeout) => {
            if let Some(pid) = pid {
                kill_process_tree(pid);
            }
            collect.await
        }
    };
    match status {
        Ok(status) => (
            super::super::decode::Utf8Decoder::new().decode_all(&bytes),
            status.code(),
        ),
        Err(_) => (String::new(), None),
    }
}

async fn find_bash_on_path() -> Option<String> {
    let (stdout, status) = run_command("which", &["bash"], Duration::from_millis(5000)).await;
    if status != Some(0) || stdout.is_empty() {
        return None;
    }
    let first_match = stdout.trim().lines().next().unwrap_or_default().to_owned();
    (!first_match.is_empty() && path_exists(&first_match).await).then_some(first_match)
}

/// How a shell receives its command.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CommandTransport {
    Argv,
    Stdin,
}

struct ShellConfig {
    shell: String,
    args: Vec<String>,
    transport: CommandTransport,
}

/// `/^[a-z]:\\windows\\(?:system32|sysnative)\\bash\.exe$/` of the path with
/// `/` turned into `\` and lowercased.
fn is_legacy_wsl_bash_path(path: &str) -> bool {
    let normalized = path.replace('/', "\\").to_lowercase();
    let mut chars = normalized.chars();
    let Some(drive) = chars.next() else {
        return false;
    };
    if !drive.is_ascii_lowercase() {
        return false;
    }
    let rest = chars.as_str();
    rest == ":\\windows\\system32\\bash.exe" || rest == ":\\windows\\sysnative\\bash.exe"
}

fn bash_shell_config(shell: String) -> ShellConfig {
    if is_legacy_wsl_bash_path(&shell) {
        ShellConfig {
            shell,
            args: vec!["-s".to_owned()],
            transport: CommandTransport::Stdin,
        }
    } else {
        ShellConfig {
            shell,
            args: vec!["-c".to_owned()],
            transport: CommandTransport::Argv,
        }
    }
}

async fn shell_config(custom_shell_path: Option<&str>) -> Result<ShellConfig, ExecutionError> {
    if let Some(custom) = custom_shell_path.filter(|path| !path.is_empty()) {
        if path_exists(custom).await {
            return Ok(bash_shell_config(custom.to_owned()));
        }
        return Err(ExecutionError::new(
            ExecutionErrorCode::ShellUnavailable,
            format!("Custom shell path not found: {custom}"),
        ));
    }
    if path_exists("/bin/bash").await {
        return Ok(bash_shell_config("/bin/bash".to_owned()));
    }
    if let Some(bash) = find_bash_on_path().await {
        return Ok(bash_shell_config(bash));
    }
    Ok(ShellConfig {
        shell: "sh".to_owned(),
        args: vec!["-c".to_owned()],
        transport: CommandTransport::Argv,
    })
}

/// `getShellEnv`: the process environment, then the environment's variables,
/// then the command's; or only the command's without inheritance.
fn shell_env(
    base_env: Option<&BTreeMap<String, String>>,
    extra_env: Option<&BTreeMap<String, String>>,
    inherit_env: bool,
) -> BTreeMap<OsString, OsString> {
    let mut env = BTreeMap::new();
    if inherit_env {
        env.extend(std::env::vars_os());
        if let Some(base) = base_env {
            env.extend(base.iter().map(|(key, value)| (key.into(), value.into())));
        }
    }
    if let Some(extra) = extra_env {
        env.extend(extra.iter().map(|(key, value)| (key.into(), value.into())));
    }
    env
}

fn spawn_error(message: String, cause: io::Error) -> ExecutionError {
    ExecutionError::new(ExecutionErrorCode::SpawnError, message).with_cause(Arc::new(cause))
}

/// Where the complete output goes once it crosses the spill thresholds.
enum Spill {
    /// Below the thresholds: chunks kept for the spill's prefix.
    Pending(Vec<Vec<u8>>),
    Writing(tokio::fs::File),
    /// Creating or writing the spill failed; output is no longer kept.
    Failed,
    /// The command settled and the spill file was flushed and closed.
    Closed,
}

/// The state of one running command, owned by its I/O task.
struct Run {
    options: ShellExecOptions,
    cx: Context,
    pid: u32,
    stdout_decoder: StreamDecoder,
    stderr_decoder: StreamDecoder,
    callback_error: Option<ExecutionError>,
    spill_error: Option<ExecutionError>,
    spill: Spill,
    spill_path: Option<String>,
    /// Output seen before the spill starts: counted against the thresholds.
    seen_bytes: u64,
    seen_newlines: u64,
    #[cfg(test)]
    spill_hook: Option<SpillHook>,
}

impl Run {
    fn kill(&self) {
        kill_process_tree(self.pid);
    }

    /// Deliver decoded text; no output reaches the caller after a callback
    /// failed.
    fn emit(&mut self, text: &str, stream: OutputStream) {
        if text.is_empty() || self.callback_error.is_some() {
            return;
        }
        let Some(on_output) = &self.options.on_output else {
            return;
        };
        let info = ShellOutputInfo {
            stream,
            skipped: None,
        };
        if let Err(error) = on_output(text, &self.cx, &info) {
            let message = error.to_string();
            self.callback_error = Some(
                ExecutionError::new(ExecutionErrorCode::CallbackError, message)
                    .with_cause(Arc::from(error)),
            );
            self.kill();
        }
    }

    fn fail_spill(&mut self, message: &str, cause: super::super::ErrorCause) {
        self.spill = Spill::Failed;
        if self.spill_error.is_some() {
            return;
        }
        self.spill_error = Some(
            ExecutionError::new(
                ExecutionErrorCode::Unknown,
                format!("Failed to preserve complete shell output: {message}"),
            )
            .with_cause(cause),
        );
        self.kill();
    }

    async fn write_spill(&mut self, chunk: &[u8]) {
        let Spill::Writing(file) = &mut self.spill else {
            return;
        };
        if chunk.is_empty() {
            return;
        }
        #[cfg(test)]
        if let Some(hook) = &self.spill_hook {
            hook.writes.fetch_add(1, Ordering::SeqCst);
            tokio::time::sleep(hook.write_delay).await;
        }
        if let Err(error) = file.write_all(chunk).await {
            let (code, description) = uv_error_name(&error);
            self.fail_spill(&format!("{code}: {description}, write"), Arc::new(error));
        }
    }

    /// Create the spill file and write what was held back, then `chunk`.
    async fn start_spill(&mut self, prefix: Vec<Vec<u8>>, chunk: &[u8]) {
        let options = TempFileOptions {
            prefix: Some("pi-output-".to_owned()),
            suffix: Some(".log".to_owned()),
        };
        let path = match create_temp_file(&options, &self.cx).await {
            Ok(path) => path,
            Err(error) => {
                let message = error.message.clone();
                self.fail_spill(&message, Arc::new(error));
                return;
            }
        };
        self.spill_path = Some(path.clone());
        let file = tokio::fs::OpenOptions::new()
            .append(true)
            .create(true)
            .open(&path)
            .await;
        match file {
            Ok(file) => self.spill = Spill::Writing(file),
            Err(error) => {
                let failure = fs_error(error, "open", &path);
                let message = failure.message.clone();
                self.fail_spill(&message, Arc::new(failure));
                return;
            }
        }
        for queued in prefix {
            self.write_spill(&queued).await;
        }
        self.write_spill(chunk).await;
    }

    /// One chunk of raw output: decode and deliver it, then keep it for the
    /// spill.
    async fn feed(&mut self, stream: OutputStream, chunk: &[u8]) {
        let text = match stream {
            OutputStream::Stdout => self.stdout_decoder.decode(chunk),
            OutputStream::Stderr => self.stderr_decoder.decode(chunk),
        };
        self.emit(&text, stream);
        let Some(ShellSpillOptions {
            after_bytes,
            after_lines,
        }) = self.options.spill
        else {
            return;
        };
        if chunk.is_empty() {
            return;
        }
        match &mut self.spill {
            Spill::Failed | Spill::Closed => {}
            Spill::Writing(_) => self.write_spill(chunk).await,
            Spill::Pending(prefix) => {
                self.seen_bytes += chunk.len() as u64;
                // One more piece than newlines.
                self.seen_newlines += (chunk.split(|&byte| byte == b'\n').count() - 1) as u64;
                let lines = self.seen_newlines + u64::from(chunk.last() != Some(&b'\n'));
                if self.seen_bytes <= after_bytes && lines <= after_lines {
                    prefix.push(chunk.to_vec());
                    return;
                }
                let prefix = std::mem::take(prefix);
                self.start_spill(prefix, chunk).await;
            }
        }
    }

    async fn finish_spill(&mut self) {
        if let Spill::Writing(file) = &mut self.spill {
            if let Err(error) = file.flush().await {
                let (code, description) = uv_error_name(&error);
                self.fail_spill(&format!("{code}: {description}, write"), Arc::new(error));
            }
        }
        if let Spill::Writing(_) = self.spill {
            self.spill = Spill::Closed;
        }
    }
}

/// Read once from an optional pipe; `None` once it ended.
async fn read_pipe<R: AsyncRead + Unpin>(pipe: &mut Option<R>, buffer: &mut [u8]) -> Option<usize> {
    let reader = pipe.as_mut()?;
    match reader.read(buffer).await {
        Ok(0) | Err(_) => None,
        Ok(read) => Some(read),
    }
}

/// Removes the command from the active set and stops its timeout and abort
/// watcher when the command settles, also if its task unwinds.
struct Settle {
    active: Arc<Mutex<HashSet<u32>>>,
    pid: u32,
    watcher: CancellationToken,
}

impl Drop for Settle {
    fn drop(&mut self) {
        self.watcher.cancel();
        self.active
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .remove(&self.pid);
    }
}

/// The exit code of a finished command: a process killed by a signal (e.g.
/// the OOM killer) has no exit code; map it to the conventional 128 + signal
/// number so callers do not mistake it for a successful exit.
fn exit_code(status: ExitStatus) -> i32 {
    status
        .code()
        .unwrap_or_else(|| status.signal().map_or(1, |signal| 128 + signal))
}

/// What to spawn: program, arguments, and the command a shell reads from
/// stdin. A string runs through the shell; an argv array runs its program
/// directly, without shell parsing.
async fn resolve_command(
    env: &NativeExecutionEnv,
    command: &ExecCommand,
) -> Result<(String, Vec<String>, Option<String>), ExecutionError> {
    match command {
        ExecCommand::Shell(command) => {
            let config = shell_config(env.shell_path.as_deref()).await?;
            let mut args = config.args;
            match config.transport {
                CommandTransport::Stdin => Ok((config.shell, args, Some(command.clone()))),
                CommandTransport::Argv => {
                    args.push(command.clone());
                    Ok((config.shell, args, None))
                }
            }
        }
        ExecCommand::Argv(argv) => {
            let Some((first, rest)) = argv.split_first() else {
                return Err(ExecutionError::new(
                    ExecutionErrorCode::SpawnError,
                    "Empty argv: no program to run",
                ));
            };
            Ok((first.clone(), rest.to_vec(), None))
        }
    }
}

/// Spawn the command in its own process group and return it with its pid.
fn spawn_command(
    env: &NativeExecutionEnv,
    options: &ShellExecOptions,
    cwd: &str,
    program: &str,
    args: &[String],
    stdin: Stdio,
) -> Result<(tokio::process::Child, u32), ExecutionError> {
    let child = tokio::process::Command::new(program)
        .args(args)
        .current_dir(cwd)
        .env_clear()
        .envs(shell_env(
            env.shell_env.as_ref(),
            options.env.as_ref(),
            options.inherit_env.unwrap_or(true),
        ))
        .stdin(stdin)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        // Its own process group, so a kill reaches every descendant.
        .process_group(0)
        .spawn()
        .map_err(|error| {
            let message = format!("spawn {program} {}", uv_code(&error));
            spawn_error(message, error)
        })?;
    // A child that was never waited for still has its pid.
    let pid = child.id().ok_or_else(|| {
        ExecutionError::new(
            ExecutionErrorCode::SpawnError,
            format!("spawn {program} ESRCH"),
        )
    })?;
    Ok((child, pid))
}

pub(super) async fn exec(
    env: &NativeExecutionEnv,
    command: &ExecCommand,
    options: &ShellExecOptions,
    cx: &Context,
) -> Result<ShellExecResult, ExecutionError> {
    if cx.aborted() {
        return Err(ExecutionError::new(ExecutionErrorCode::Aborted, "aborted"));
    }
    let timeout_ms = resolve_timeout_ms(options.timeout)?;
    let cwd = match options.cwd.as_deref() {
        Some(cwd) if !cwd.is_empty() => resolve_path(&env.cwd, cwd),
        _ => env.cwd.clone(),
    };
    let (program, args, stdin_command) = resolve_command(env, command).await?;
    if let Err(error) = tokio::fs::metadata(&cwd).await {
        return Err(spawn_error(
            format!("Working directory does not exist: {cwd}\nCannot execute bash commands."),
            error,
        ));
    }

    let stdin = if stdin_command.is_some() {
        Stdio::piped()
    } else {
        Stdio::null()
    };
    let (mut child, pid) = spawn_command(env, options, &cwd, &program, &args, stdin)?;
    env.active_child_pids
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .insert(pid);
    let watcher = CancellationToken::new();
    let settle = Settle {
        active: Arc::clone(&env.active_child_pids),
        pid,
        watcher: watcher.clone(),
    };

    if let (Some(command), Some(mut stdin)) = (stdin_command, child.stdin.take()) {
        tokio::spawn(async move {
            // A shell that exits before reading its command closes the pipe;
            // Node ignores the resulting stdin errors.
            let _ = stdin.write_all(command.as_bytes()).await;
            let _ = stdin.shutdown().await;
        });
    }

    let timed_out = Arc::new(AtomicBool::new(false));
    tokio::spawn(watch_timeout_and_abort(
        pid,
        timeout_ms,
        cx.clone(),
        Arc::clone(&timed_out),
        watcher,
    ));

    let run = Run {
        options: options.clone(),
        cx: cx.clone(),
        pid,
        stdout_decoder: StreamDecoder::new(),
        stderr_decoder: StreamDecoder::new(),
        callback_error: None,
        spill_error: None,
        spill: Spill::Pending(Vec::new()),
        spill_path: None,
        seen_bytes: 0,
        seen_newlines: 0,
        #[cfg(test)]
        spill_hook: env.spill_hook.clone(),
    };
    // The command runs to completion even if the caller stops waiting, like
    // the JS promise.
    let task = tokio::spawn(async move {
        let result = drive(child, run, &timed_out).await;
        drop(settle);
        result
    });
    match task.await {
        Ok(result) => result,
        Err(error) => match error.try_into_panic() {
            Ok(panic) => std::panic::resume_unwind(panic),
            Err(error) => Err(ExecutionError::new(
                ExecutionErrorCode::Unknown,
                error.to_string(),
            )),
        },
    }
}

/// Kill the command on timeout or abort until it settles.
async fn watch_timeout_and_abort(
    pid: u32,
    timeout_ms: Option<f64>,
    cx: Context,
    timed_out: Arc<AtomicBool>,
    settled: CancellationToken,
) {
    let timeout = async {
        match timeout_ms {
            Some(ms) => tokio::time::sleep(Duration::from_secs_f64(ms.max(1.0) / 1000.0)).await,
            None => std::future::pending().await,
        }
    };
    let aborted = async {
        match cx.abort_signal() {
            Some(signal) => {
                signal.cancelled().await;
            }
            None => std::future::pending().await,
        }
    };
    tokio::pin!(timeout, aborted);
    let (mut timeout_done, mut abort_done) = (false, false);
    loop {
        tokio::select! {
            () = settled.cancelled() => return,
            () = &mut timeout, if !timeout_done => {
                timeout_done = true;
                timed_out.store(true, Ordering::SeqCst);
                kill_process_tree(pid);
            }
            () = &mut aborted, if !abort_done => {
                abort_done = true;
                kill_process_tree(pid);
            }
        }
    }
}

/// Read both pipes until the command exited and its output ended, or until
/// its output stayed idle for the grace period after it exited (a descendant
/// may hold the pipes open), then settle.
async fn drive(
    mut child: tokio::process::Child,
    mut run: Run,
    timed_out: &AtomicBool,
) -> Result<ShellExecResult, ExecutionError> {
    let mut stdout = child.stdout.take();
    let mut stderr = child.stderr.take();
    let mut stdout_buffer = vec![0; PIPE_CHUNK];
    let mut stderr_buffer = vec![0; PIPE_CHUNK];
    // The exit status and when the output counts as idle after the exit.
    let mut exited: Option<(ExitStatus, Instant)> = None;
    let status = loop {
        if let Some((status, _)) = exited {
            if stdout.is_none() && stderr.is_none() {
                break status;
            }
        }
        let exit_state = exited;
        let idle = async move {
            match exit_state {
                Some((status, deadline)) => {
                    tokio::time::sleep_until(deadline).await;
                    status
                }
                None => std::future::pending().await,
            }
        };
        tokio::select! {
            read = read_pipe(&mut stdout, &mut stdout_buffer), if stdout.is_some() => match read {
                None => stdout = None,
                Some(read) => {
                    let chunk = stdout_buffer[..read].to_vec();
                    run.feed(OutputStream::Stdout, &chunk).await;
                    if let Some((_, deadline)) = &mut exited {
                        *deadline = Instant::now() + EXIT_STDIO_GRACE;
                    }
                }
            },
            read = read_pipe(&mut stderr, &mut stderr_buffer), if stderr.is_some() => match read {
                None => stderr = None,
                Some(read) => {
                    let chunk = stderr_buffer[..read].to_vec();
                    run.feed(OutputStream::Stderr, &chunk).await;
                    if let Some((_, deadline)) = &mut exited {
                        *deadline = Instant::now() + EXIT_STDIO_GRACE;
                    }
                }
            },
            result = child.wait(), if exited.is_none() => match result {
                Ok(status) => exited = Some((status, Instant::now() + EXIT_STDIO_GRACE)),
                Err(error) => {
                    return Err(ExecutionError::new(ExecutionErrorCode::SpawnError, error.to_string())
                        .with_cause(Arc::new(error)));
                }
            },
            status = idle => break status,
        }
    };
    // Settling destroys the pipes: no output reaches the caller after exec
    // settled, for example from a descendant holding stdio open.
    drop(stdout);
    drop(stderr);

    run.finish_spill().await;
    let text = run.stdout_decoder.finish();
    run.emit(&text, OutputStream::Stdout);
    let text = run.stderr_decoder.finish();
    run.emit(&text, OutputStream::Stderr);
    if let Some(error) = run.callback_error.take() {
        return Err(error);
    }
    let interrupted = if timed_out.load(Ordering::SeqCst) {
        let timeout = run
            .options
            .timeout
            .map_or_else(|| "undefined".to_owned(), js_number);
        Some(ExecutionError::new(
            ExecutionErrorCode::Timeout,
            format!("timeout:{timeout}"),
        ))
    } else if run.cx.aborted() {
        Some(ExecutionError::new(ExecutionErrorCode::Aborted, "aborted"))
    } else {
        None
    };
    if let Some(mut interrupted) = interrupted {
        interrupted.spill_path = run.spill_path.take();
        return Err(interrupted);
    }
    if let Some(error) = run.spill_error.take() {
        return Err(error);
    }
    Ok(ShellExecResult {
        exit_code: exit_code(status),
        spill_path: run.spill_path.take(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn js_number_formats_like_javascript() {
        assert_eq!(js_number(2_147_483.647), "2147483.647");
        assert_eq!(js_number(0.01), "0.01");
        assert_eq!(js_number(5.0), "5");
        assert_eq!(js_number(1e-7), "1e-7");
        assert_eq!(js_number(1.5e-7), "1.5e-7");
        assert_eq!(js_number(0.000_001), "0.000001");
        assert_eq!(js_number(1e21), "1e+21");
        assert_eq!(
            js_number(123_456_789_012_345_680_000.0),
            "123456789012345680000"
        );
        assert_eq!(js_number(-0.5), "-0.5");
    }

    #[test]
    fn legacy_wsl_bash_paths_use_stdin_transport() {
        assert!(is_legacy_wsl_bash_path("C:\\Windows\\System32\\bash.exe"));
        assert!(is_legacy_wsl_bash_path("c:/windows/sysnative/bash.exe"));
        assert!(!is_legacy_wsl_bash_path(
            "C:\\Program Files\\Git\\bin\\bash.exe"
        ));
        assert!(!is_legacy_wsl_bash_path("/bin/bash"));
    }
}
