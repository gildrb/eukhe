//! The check an agent tree's node runs on its work: in a child's checkout
//! before it reports, in the parent's workspace after integration. The
//! project's configured command (`agentTree.checkCommand`) when set, else
//! the narrowest check detected for the touched files:
//! - Cargo: `cargo test -p <crate>` for each crate owning a touched file
//!   (the nearest `Cargo.toml` with a `[package]`);
//! - npm: `npm test` in the nearest directory with a `package.json`;
//! - Python: `python -m pytest` over the touched test directories (else
//!   the nearest `pyproject.toml`'s directory).
//!
//! The command runs under `sh -c` in its own process group, killed at the
//! timeout, with the mise trust a child's copy keeps ([`super::tool_env`]);
//! the report keeps the output's tail. While it runs, the caller hears from
//! it at its start, at each interval (time since the start, the last line
//! it printed) and at its end (how it ended, its last lines). The
//! workspace is not frozen while the check runs (a copy would lack the
//! build caches and dependency dirs the command needs): stamps of it
//! before and after name each path written meanwhile ([`WorkspaceDrift`]),
//! so a result that judged no single tree state says so.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Stdio;
use std::time::{Duration, Instant};

use eukhe_types::daemon::agent_tree::{CheckOutcome, CheckPhase};
use serde::{Deserialize, Serialize};
use tokio::io::AsyncReadExt;
use tokio::process::Command;

use super::stamp::{TreeStamp, WorkspaceDrift};
use crate::platform::process::{signal_process_group, Signal};

/// The output bytes a check report keeps (the tail).
const OUTPUT_TAIL_BYTES: usize = 16 * 1024;

/// The last output lines a failed check's verdict names.
const VERDICT_LINES: usize = 3;

/// The most chars of one output line a verdict or a status names.
const LINE_CHARS: usize = 200;

/// The interval of a running check's reports.
pub(crate) const PROGRESS_EVERY: Duration = Duration::from_secs(30);

/// How a node's check runs (`agentTree.checkCommand`,
/// `agentTree.checkTimeoutSecs`; `SettingsManager::get_agent_tree_check`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckConfig {
    /// The project's check command; `None`: detect one.
    pub command: Option<String>,
    /// The check is killed and reported timed out past it.
    pub timeout: Duration,
    /// The interval of the running check's reports ([`PROGRESS_EVERY`]).
    pub progress_every: Duration,
}

/// A check's report.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum CheckRun {
    /// No command configured and none detected for the touched files.
    None,
    /// Not run yet: the hand-back took the child's work, and the check
    /// runs after it.
    Pending,
    /// The host could not run it (the error says why).
    NotRun { error: String },
    Ran {
        command: String,
        outcome: CheckOutcome,
        /// The tail of stdout and stderr, interleaved.
        output: String,
        duration_ms: u64,
        /// Whether the workspace changed while the check ran.
        #[serde(default = "WorkspaceDrift::unrecorded")]
        workspace: WorkspaceDrift,
    },
}

impl CheckRun {
    /// The check as the node reads it: the verdict (a failed or timed out
    /// check's with its last output lines), then the output's tail.
    #[must_use]
    pub fn text(&self) -> String {
        match self {
            CheckRun::None => "Check: none configured or detected.".to_owned(),
            CheckRun::Pending => {
                "Check: runs after the integration; its result follows.".to_owned()
            }
            CheckRun::NotRun { error } => format!("Check: did not run: {error}."),
            CheckRun::Ran {
                command,
                outcome,
                output,
                duration_ms,
                workspace,
            } => {
                let (seconds, tenths) = (duration_ms / 1000, duration_ms % 1000 / 100);
                let lines = match outcome {
                    CheckOutcome::Passed => Vec::new(),
                    CheckOutcome::Failed { .. } | CheckOutcome::TimedOut => {
                        last_lines(output, VERDICT_LINES)
                    }
                };
                let verdict = outcome.verdict();
                let head = if lines.is_empty() {
                    format!("Check `{command}`: {verdict} in {seconds}.{tenths} s.")
                } else {
                    format!(
                        "Check `{command}`: {verdict} in {seconds}.{tenths} s; last lines: {}.",
                        lines.join(" | ")
                    )
                };
                let head = match workspace.text("the check") {
                    Some(drift) => format!("{head}\n{drift}"),
                    None => head,
                };
                if output.is_empty() {
                    head
                } else {
                    format!("{head}\n{output}")
                }
            }
        }
    }
}

/// One report of a check: its command, the time since its start, and
/// whether it runs or how it ended.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckReport {
    pub command: String,
    pub elapsed_ms: u64,
    pub phase: CheckPhase,
}

/// The last `count` non-empty lines of `output`, oldest first, each
/// trimmed and cut at [`LINE_CHARS`] chars.
fn last_lines(output: &str, count: usize) -> Vec<String> {
    let mut lines: Vec<String> = output
        .lines()
        .rev()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .take(count)
        .map(|line| line.chars().take(LINE_CHARS).collect())
        .collect();
    lines.reverse();
    lines
}

/// Run the check of `touched` (paths relative to `dir`, or absolute under
/// it) in `dir`: the configured command, else the detected one; `dir`
/// stamped before and after it. `report` hears from it at its start, at
/// each `config.progress_every` while it runs, and at its end.
#[tracing::instrument(skip(touched, report))]
pub async fn run_check(
    dir: &Path,
    touched: &[PathBuf],
    config: &CheckConfig,
    report: &(dyn Fn(CheckReport) + Sync),
) -> CheckRun {
    let command = match &config.command {
        Some(command) => command.clone(),
        None => match detect(dir, touched) {
            Some(command) => command,
            None => return CheckRun::None,
        },
    };
    let before = TreeStamp::take(dir).await;
    let started = Instant::now();
    let (outcome, output) = run(dir, &command, config, started, report).await;
    let duration_ms = whole_ms(started.elapsed());
    let workspace = before.drift(&TreeStamp::take(dir).await);
    report(CheckReport {
        command: command.clone(),
        elapsed_ms: duration_ms,
        phase: CheckPhase::Ended {
            outcome: outcome.clone(),
            last_lines: last_lines(&output, VERDICT_LINES),
        },
    });
    CheckRun::Ran {
        command,
        outcome,
        output,
        duration_ms,
        workspace,
    }
}

/// `elapsed` in whole milliseconds, saturating.
fn whole_ms(elapsed: Duration) -> u64 {
    u64::try_from(elapsed.as_millis()).unwrap_or(u64::MAX)
}

/// The narrowest check of `touched` under `dir`: every kind detected,
/// joined with `&&`; `None` when none is.
pub(super) fn detect(dir: &Path, touched: &[PathBuf]) -> Option<String> {
    let relative: Vec<PathBuf> = touched
        .iter()
        .map(|path| path.strip_prefix(dir).unwrap_or(path).to_path_buf())
        .collect();
    let crates: BTreeSet<String> = relative
        .iter()
        .filter_map(|path| nearest(dir, path, |at| crate_name(&at.join("Cargo.toml"))))
        .map(|(_, name)| name)
        .collect();
    let packages: BTreeSet<PathBuf> = relative
        .iter()
        .filter_map(|path| nearest_with(dir, path, "package.json"))
        .collect();
    let projects: BTreeSet<PathBuf> = relative
        .iter()
        .filter_map(|path| nearest_with(dir, path, "pyproject.toml"))
        .collect();
    let mut steps = Vec::new();
    if !crates.is_empty() {
        let args: Vec<String> = crates
            .iter()
            .map(|name| format!("-p {}", quote(name)))
            .collect();
        steps.push(format!("cargo test {}", args.join(" ")));
    }
    steps.extend(packages.iter().map(|package| {
        if package.as_os_str().is_empty() {
            "npm test".to_owned()
        } else {
            format!("npm --prefix {} test", quote(&package.to_string_lossy()))
        }
    }));
    if !projects.is_empty() {
        let tests: BTreeSet<PathBuf> = relative
            .iter()
            .filter(|path| is_python_test(path))
            .filter_map(|path| path.parent().map(Path::to_path_buf))
            .collect();
        let targets = if tests.is_empty() { projects } else { tests };
        let args: Vec<String> = targets
            .iter()
            .map(|target| match target.to_string_lossy() {
                name if name.is_empty() => ".".to_owned(),
                name => quote(&name),
            })
            .collect();
        steps.push(format!("python -m pytest {}", args.join(" ")));
    }
    (!steps.is_empty()).then(|| steps.join(" && "))
}

/// The nearest of `path`'s directories (relative to `dir`, up to `dir`
/// itself as `""`) where `found` finds a value, with the value.
fn nearest<T>(dir: &Path, path: &Path, found: impl Fn(&Path) -> Option<T>) -> Option<(PathBuf, T)> {
    path.ancestors()
        .skip(1)
        .find_map(|at| found(&dir.join(at)).map(|value| (at.to_path_buf(), value)))
}

/// The nearest directory of `path` holding the file `name`.
fn nearest_with(dir: &Path, path: &Path, name: &str) -> Option<PathBuf> {
    nearest(dir, path, |at| at.join(name).is_file().then_some(())).map(|(at, ())| at)
}

/// The `[package]` name of the manifest at `manifest`; `None` without one
/// (no file, or a virtual workspace manifest).
fn crate_name(manifest: &Path) -> Option<String> {
    let text = fs::read_to_string(manifest).ok()?;
    let document: toml::Table = text.parse().ok()?;
    document
        .get("package")?
        .get("name")?
        .as_str()
        .map(str::to_owned)
}

/// A pytest file by its name (`test_*.py`, `*_test.py`) or a Python file
/// under a `tests` directory.
fn is_python_test(path: &Path) -> bool {
    let is_python = path.extension().is_some_and(|extension| extension == "py");
    let name = path
        .file_name()
        .map(|name| name.to_string_lossy())
        .unwrap_or_default();
    is_python
        && (name.starts_with("test_")
            || name.ends_with("_test.py")
            || path.components().any(|part| part.as_os_str() == "tests"))
}

/// `text` as one `sh` word.
fn quote(text: &str) -> String {
    format!("'{}'", text.replace('\'', r"'\''"))
}

/// Run `command` under `sh -c` in `dir`, stdout and stderr in one stream,
/// killed with its process group at `config.timeout`: how it ended and the
/// output's tail. `report` hears that it runs at its start and at each
/// `config.progress_every`, with the time since `started` and the last
/// line it printed.
async fn run(
    dir: &Path,
    command: &str,
    config: &CheckConfig,
    started: Instant,
    report: &(dyn Fn(CheckReport) + Sync),
) -> (CheckOutcome, String) {
    let trust = super::tool_env(dir);
    let spawned = Command::new("sh")
        .arg("-c")
        .arg(format!("exec 2>&1\n{command}"))
        .current_dir(dir)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .process_group(0)
        .kill_on_drop(true)
        .envs(trust)
        .spawn();
    let mut child = match spawned {
        Ok(child) => child,
        Err(error) => {
            return (
                CheckOutcome::Failed { code: None },
                format!("sh did not start: {error}"),
            )
        }
    };
    let Some(stdout) = child.stdout.take() else {
        return (
            CheckOutcome::Failed { code: None },
            "sh has no output pipe".to_owned(),
        );
    };
    let running = |tail: &[u8]| {
        report(CheckReport {
            command: command.to_owned(),
            elapsed_ms: whole_ms(started.elapsed()),
            phase: CheckPhase::Running {
                last_line: last_lines(&String::from_utf8_lossy(tail), 1).pop(),
            },
        });
    };
    running(&[]);
    let mut tail = Vec::new();
    let ended = tokio::time::timeout(config.timeout, async {
        keep_tail(stdout, &mut tail, config.progress_every, running).await?;
        child.wait().await
    })
    .await;
    let outcome = match ended {
        Ok(Ok(status)) => match status.code() {
            Some(0) => CheckOutcome::Passed,
            code => CheckOutcome::Failed { code },
        },
        Ok(Err(error)) => {
            tail.extend_from_slice(format!("\nreading the check failed: {error}").as_bytes());
            CheckOutcome::Failed { code: None }
        }
        Err(_elapsed) => {
            if let Some(group) = child.id().and_then(|pid| i32::try_from(pid).ok()) {
                let _gone = signal_process_group(group, Signal::Kill);
            }
            // Reaped so no zombie stays; the kill already ended it.
            let _reaped = child.wait().await;
            CheckOutcome::TimedOut
        }
    };
    let start = tail.len().saturating_sub(OUTPUT_TAIL_BYTES);
    (
        outcome,
        String::from_utf8_lossy(&tail[start..]).into_owned(),
    )
}

/// Read `reader` to its end into `tail`, keeping at most twice
/// [`OUTPUT_TAIL_BYTES`] (the caller keeps the last
/// [`OUTPUT_TAIL_BYTES`]); `tick` reads the tail at each `every`.
async fn keep_tail(
    mut reader: impl tokio::io::AsyncRead + Unpin,
    tail: &mut Vec<u8>,
    every: Duration,
    tick: impl Fn(&[u8]),
) -> std::io::Result<()> {
    let mut ticks = tokio::time::interval_at(tokio::time::Instant::now() + every, every);
    ticks.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Delay);
    let mut chunk = [0u8; 8192];
    loop {
        tokio::select! {
            read = reader.read(&mut chunk) => {
                let read = read?;
                if read == 0 {
                    return Ok(());
                }
                tail.extend_from_slice(&chunk[..read]);
                if tail.len() > 2 * OUTPUT_TAIL_BYTES {
                    tail.drain(..tail.len() - OUTPUT_TAIL_BYTES);
                }
            }
            _ = ticks.tick() => tick(tail),
        }
    }
}
