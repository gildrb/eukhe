//! The command runner of the acceptance checks and the loop's
//! until-condition: a shell command in the session cwd with a time limit
//! and capped output, and a snapshot of the git worktree as evidence.

use std::path::{Path, PathBuf};
use std::pin::Pin;

use sha2::{Digest, Sha256};

/// Output cap for gate child processes (both streams combined per stream).
const MAX_CHILD_PROCESS_OUTPUT_CHARS: usize = 1024 * 1024;
/// Timeout for the git commands that capture a worktree snapshot.
const SNAPSHOT_TIMEOUT_MS: u64 = 10_000;

/// Future returned by [`GateCommandRunner`] methods.
pub type GateRunFuture<'a> =
    Pin<Box<dyn std::future::Future<Output = anyhow::Result<ChildProcessResult>> + Send + 'a>>;
/// Future returned by [`GateCommandRunner::capture_snapshot`].
pub type SnapshotFuture<'a> =
    Pin<Box<dyn std::future::Future<Output = Option<GitWorktreeSnapshot>> + Send + 'a>>;

/// Runs check commands and captures workspace evidence for them. The
/// product implementation shells out in the session cwd; tests and eval
/// harnesses implement scripted, deterministic runners.
///
/// Contract: `run_gate` always resolves (a spawn failure is an `Err`), and
/// `capture_snapshot` returns `None` when the workspace state is
/// unavailable.
pub trait GateCommandRunner: Send + Sync {
    /// Run one command with its time limit.
    fn run_gate(&self, command: &str, timeout_ms: u64) -> GateRunFuture<'_>;

    /// Capture the workspace snapshot a judge reads as evidence.
    fn capture_snapshot(&self) -> SnapshotFuture<'_> {
        Box::pin(async { None })
    }
}

/// The product runner: `bash -c <command>` in the session cwd.
#[derive(Debug, Clone)]
pub struct ShellGateRunner {
    cwd: PathBuf,
}

impl ShellGateRunner {
    pub fn new(cwd: impl Into<PathBuf>) -> Self {
        Self { cwd: cwd.into() }
    }
}

impl GateCommandRunner for ShellGateRunner {
    fn run_gate(&self, command: &str, timeout_ms: u64) -> GateRunFuture<'_> {
        let command = command.to_string();
        let cwd = self.cwd.clone();
        Box::pin(async move { run_gate_command(&command, &cwd, timeout_ms).await })
    }

    fn capture_snapshot(&self) -> SnapshotFuture<'_> {
        let cwd = self.cwd.clone();
        Box::pin(async move { capture_git_worktree_snapshot(&cwd).await })
    }
}

/// Result of one gate child process.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct ChildProcessResult {
    pub status: Option<i32>,
    pub stdout: String,
    pub stderr: String,
    pub error: Option<String>,
    pub timed_out: bool,
    pub output_truncated: bool,
}

/// The git worktree: porcelain status, the HEAD diff, a hash of the
/// untracked files.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct GitWorktreeSnapshot {
    pub status: String,
    pub diff: String,
    pub untracked_hash: String,
}

/// Pathspec entries excluded from gate snapshots: harness workspaces churn
/// in these paths between attempts, and none of them is gate-relevant work.
const SNAPSHOT_EXCLUDES: [&str; 6] = [
    "verification",
    "target",
    ".vf-eukhe",
    "Cargo.lock",
    "submission.tar.gz",
    "runner_args.log",
];

/// Snapshot the git worktree state: porcelain status, the HEAD diff, and a
/// content hash of untracked files. `None` when any capture step fails (the
/// gate loop then treats the workspace as always-changed).
pub async fn capture_git_worktree_snapshot(cwd: &Path) -> Option<GitWorktreeSnapshot> {
    if !cwd.is_dir() {
        return None;
    }
    let mut pathspec: Vec<String> = vec!["--".to_string(), ".".to_string()];
    for exclude in SNAPSHOT_EXCLUDES {
        pathspec.push(format!(":(exclude){exclude}"));
    }
    let status = run_git(
        &[
            "--no-optional-locks",
            "status",
            "--porcelain=v1",
            "-z",
            "-uall",
            "--no-renames",
        ],
        &pathspec,
        cwd,
    )
    .await?;
    let diff = run_git(
        &[
            "--no-optional-locks",
            "diff",
            "--no-ext-diff",
            "--binary",
            "HEAD",
        ],
        &pathspec,
        cwd,
    )
    .await?;
    let untracked_hash = hash_untracked_files(cwd, &status);
    Some(GitWorktreeSnapshot {
        status,
        diff,
        untracked_hash,
    })
}

/// One git invocation: `None` on any non-zero exit, timeout, or truncation.
async fn run_git(prefix: &[&str], pathspec: &[String], cwd: &Path) -> Option<String> {
    let mut args: Vec<String> = eukhe_shell::GIT_UNTRUSTED_REPO_ARGS
        .iter()
        .chain(prefix)
        .map(std::string::ToString::to_string)
        .collect();
    args.extend(pathspec.iter().cloned());
    let result = run_child_process("git", &args, cwd, SNAPSHOT_TIMEOUT_MS)
        .await
        .ok()?;
    if result.status != Some(0)
        || result.error.is_some()
        || result.timed_out
        || result.output_truncated
    {
        return None;
    }
    Some(result.stdout)
}

/// Aggregate content hash over the untracked files named in a porcelain
/// status stream: path, then file/symlink/other digest, NUL-separated.
fn hash_untracked_files(cwd: &Path, status: &str) -> String {
    let mut aggregate = Sha256::new();
    for path in untracked_paths_from_status(status) {
        aggregate.update(path.as_bytes());
        aggregate.update([0]);
        aggregate.update(hash_untracked_path(&cwd.join(path)).as_bytes());
        aggregate.update([0]);
    }
    format!("{:x}", aggregate.finalize())
}

fn untracked_paths_from_status(status: &str) -> Vec<String> {
    let mut paths: Vec<String> = status
        .split('\0')
        .filter(|entry| entry.starts_with("?? "))
        .map(|entry| entry[3..].to_string())
        .collect();
    paths.sort();
    paths
}

/// Digest of one untracked path: symlink target, file content, or metadata
/// for everything else; capture failures hash their message (a partial
/// digest is still a stable comparison basis between attempts).
fn hash_untracked_path(path: &Path) -> String {
    let Ok(metadata) = std::fs::symlink_metadata(path) else {
        return "missing".to_string();
    };
    if metadata.file_type().is_symlink() {
        let target = std::fs::read_link(path).map_or_else(
            |error| error.to_string(),
            |target| target.to_string_lossy().to_string(),
        );
        return format!("symlink:{target}");
    }
    if !metadata.is_file() {
        return format!(
            "other:{}:{}",
            metadata.len(),
            metadata
                .modified()
                .ok()
                .and_then(|time| time.duration_since(std::time::UNIX_EPOCH).ok())
                .map_or(0, |duration| duration.as_millis())
        );
    }
    match std::fs::read(path) {
        Ok(bytes) => {
            let mut hasher = Sha256::new();
            hasher.update(&bytes);
            format!("file:{:x}", hasher.finalize())
        }
        Err(error) => format!("error:{error}"),
    }
}

/// Run a child process with a timeout, draining both output pipes
/// concurrently (a chatty command cannot wedge the wait on a full pipe).
async fn run_child_process(
    program: &str,
    args: &[String],
    cwd: &Path,
    timeout_ms: u64,
) -> anyhow::Result<ChildProcessResult> {
    let mut child = tokio::process::Command::new(program)
        .args(args)
        .current_dir(cwd)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .kill_on_drop(true)
        .spawn()?;
    let stdout = read_pipe_capped(child.stdout.take());
    let stderr = read_pipe_capped(child.stderr.take());
    let timeout = tokio::time::Duration::from_millis(timeout_ms.max(1));
    let wait = async {
        let status = child.wait().await?;
        Ok::<_, std::io::Error>(status)
    };
    tokio::select! {
        status = wait => {
            let status = status.map_err(|error| anyhow::anyhow!("{error}"))?;
            let (stdout, stdout_truncated) = stdout.await;
            let (stderr, stderr_truncated) = stderr.await;
            Ok(ChildProcessResult {
                status: status.code(),
                stdout,
                stderr,
                error: None,
                timed_out: false,
                output_truncated: stdout_truncated || stderr_truncated,
            })
        }
        () = tokio::time::sleep(timeout) => {
            let _ = child.kill().await;
            let (stdout, stdout_truncated) = stdout.await;
            let (stderr, stderr_truncated) = stderr.await;
            Ok(ChildProcessResult {
                status: None,
                stdout,
                stderr,
                error: None,
                timed_out: true,
                output_truncated: stdout_truncated || stderr_truncated,
            })
        }
    }
}

/// Run a shell gate command with the configured timeout and output caps.
pub async fn run_gate_command(
    command: &str,
    cwd: &Path,
    timeout_ms: u64,
) -> anyhow::Result<ChildProcessResult> {
    let args = ["-c".to_string(), command.to_string()];
    run_child_process("bash", &args, cwd, timeout_ms).await
}

/// Read one output pipe to EOF, keeping at most `cap` characters; the
/// remainder is drained so a full pipe never blocks the child.
async fn read_pipe_capped<R: tokio::io::AsyncRead + Unpin>(mut pipe: Option<R>) -> (String, bool) {
    use tokio::io::AsyncReadExt;
    let cap = MAX_CHILD_PROCESS_OUTPUT_CHARS;
    let mut kept = String::new();
    let mut truncated = false;
    let mut buffer = [0u8; 8192];
    if let Some(pipe) = pipe.as_mut() {
        loop {
            match pipe.read(&mut buffer).await {
                Ok(0) | Err(_) => break,
                Ok(read) => {
                    let chunk = String::from_utf8_lossy(&buffer[..read]);
                    if kept.len() < cap {
                        let remaining = cap - kept.len();
                        if chunk.len() <= remaining {
                            kept.push_str(&chunk);
                        } else {
                            kept.push_str(&chunk[..remaining]);
                            truncated = true;
                        }
                    } else {
                        truncated = true;
                    }
                }
            }
        }
    }
    (kept, truncated)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn shell_runner_runs_gates_and_snapshots() {
        let dir = tempfile::TempDir::new().unwrap();
        let runner = ShellGateRunner::new(dir.path());
        let passing = runner.run_gate("exit 0", 5_000).await.unwrap();
        assert_eq!(passing.status, Some(0));
        let failing = runner
            .run_gate("echo boom >&2; exit 3", 5_000)
            .await
            .unwrap();
        assert_eq!(failing.status, Some(3));
        assert_eq!(failing.stderr.trim(), "boom");
        // Timeout: a sleeping gate is killed and reported as timed out.
        let timed_out = runner.run_gate("sleep 5", 50).await.unwrap();
        assert!(timed_out.timed_out);
        // Outside a git worktree no snapshot is captured.
        assert!(runner.capture_snapshot().await.is_none());
    }

    #[tokio::test]
    async fn shell_runner_snapshot_tracks_workspace_changes() {
        let dir = tempfile::TempDir::new().unwrap();
        let run = |args: &[&str]| {
            let mut command = std::process::Command::new("git");
            command.args(args).current_dir(dir.path());
            command
                .output()
                .map(|output| {
                    (
                        output.status.success(),
                        String::from_utf8_lossy(&output.stderr).to_string(),
                    )
                })
                .unwrap()
        };
        assert!(run(&["init", "-q"]).0);
        run(&["config", "user.email", "t@example.com"]);
        run(&["config", "user.name", "t"]);
        std::fs::write(dir.path().join("tracked.txt"), "one\n").unwrap();
        assert!(run(&["add", "."]).0);
        assert!(run(&["commit", "-q", "-m", "init"]).0);
        let runner = ShellGateRunner::new(dir.path());
        let empty = runner.capture_snapshot().await.unwrap();
        // An untracked file changes the snapshot (content-hashed).
        std::fs::write(dir.path().join("untracked.txt"), "hello\n").unwrap();
        let with_file = runner.capture_snapshot().await.unwrap();
        assert!(with_file.status.contains("?? untracked.txt"));
        assert_ne!(with_file.untracked_hash, empty.untracked_hash);
        // Same content again: an identical snapshot (the comparison basis).
        let same = runner.capture_snapshot().await.unwrap();
        assert_eq!(same, with_file);
        // A tracked modification changes the diff instead.
        std::fs::write(dir.path().join("tracked.txt"), "two\n").unwrap();
        let modified = runner.capture_snapshot().await.unwrap();
        assert!(modified.diff.contains("+two"));
        assert_ne!(modified, with_file);
        assert_eq!(
            untracked_paths_from_status(&modified.status),
            vec!["untracked.txt".to_string()]
        );
        let digest = hash_untracked_path(&dir.path().join("untracked.txt"));
        assert!(digest.starts_with("file:"));
    }
}
