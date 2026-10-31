//! One benchmark run: `bash autoresearch.sh` in the repository root,
//! through the approval gate of the `bash` tool (the in-process
//! [`Shell`] with the session's auto set, path policy and approval sink:
//! a step that runs a program runs unasked only when `exec` is in
//! `shell.autoEffects`), bounded by a timeout. Its stdout and stderr go
//! to the run's `benchmark.log` as they arrive, and each whole line goes
//! to the caller, which feeds it to the Lab.

use std::collections::HashMap;
use std::fs::File;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::sync::{Mutex, MutexGuard, PoisonError};
use std::time::Duration;

use anyhow::Context as _;
use eukhe_shell::{End, Shell, Sink, Stream};
use eukhe_types::path_policy::PathPolicy;
use eukhe_types::shell::AutoSet;
use tokio::sync::mpsc;

use crate::durable::shell::{RefusalText, SinkApprover};

/// The benchmark entrypoint; the model never chooses the command.
pub(crate) const SCRIPT: &str = "bash autoresearch.sh";

/// The harness file in the repository root.
pub(crate) const HARNESS: &str = "autoresearch.sh";

/// The exit code a run that hit its timeout reports (as `timeout(1)`).
pub(crate) const TIMEOUT_EXIT: i32 = 124;

/// What the approval gate of one run needs: the environment of external
/// steps, the auto set, the path policy, and who asks the user.
pub(crate) struct RunGate {
    pub(crate) env: HashMap<String, String>,
    pub(crate) auto: AutoSet,
    pub(crate) paths: PathPolicy,
    pub(crate) approver: SinkApprover,
}

/// How a run ended.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum RunEnd {
    /// The script ended with this exit code.
    Exited(i32),
    /// The timeout killed the script and every process it started.
    TimedOut,
    /// The gate did not let the script run; the text says why and what
    /// to do.
    Refused(String),
}

/// The streams of one run: the log file, the bytes of each stream after
/// its last newline, and the channel of whole lines.
struct Lines {
    log: Mutex<File>,
    write_failed: Mutex<Option<std::io::Error>>,
    partial: Mutex<HashMap<Stream, Vec<u8>>>,
    sender: mpsc::UnboundedSender<String>,
}

impl Lines {
    fn send(&self, bytes: &[u8]) {
        let bytes = bytes.strip_suffix(b"\r").unwrap_or(bytes);
        // The receiver lives until the run ends: a send fails only after.
        let _ = self
            .sender
            .send(String::from_utf8_lossy(bytes).into_owned());
    }
}

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

impl Sink for Lines {
    fn begin(&self, _step: u64, _command: &str) {}

    fn output(&self, _step: u64, stream: Stream, bytes: &[u8]) {
        if let Err(error) = lock(&self.log).write_all(bytes) {
            lock(&self.write_failed).get_or_insert(error);
        }
        let mut partial = lock(&self.partial);
        let buffer = partial.entry(stream).or_default();
        buffer.extend_from_slice(bytes);
        while let Some(end) = buffer.iter().position(|byte| *byte == b'\n') {
            let line: Vec<u8> = buffer.drain(..=end).collect();
            self.send(&line[..end]);
        }
    }

    fn end(&self, _step: u64, _status: i32) {
        for (_, rest) in lock(&self.partial).drain() {
            if !rest.is_empty() {
                self.send(&rest);
            }
        }
    }
}

/// Run the harness in `root` under `gate`, writing its output to `log`;
/// `on_line` gets every whole output line in order, as it arrives.
///
/// # Errors
///
/// The log cannot be created or written, the script's task failed, or
/// `on_line` fails (the run is then stopped).
pub(crate) async fn run(
    gate: RunGate,
    root: PathBuf,
    log: &Path,
    timeout: Duration,
    mut on_line: impl FnMut(String) -> anyhow::Result<()>,
) -> anyhow::Result<RunEnd> {
    let file = File::create(log).with_context(|| format!("could not create {}", log.display()))?;
    let (sender, mut receiver) = mpsc::unbounded_channel();
    let lines = std::sync::Arc::new(Lines {
        log: Mutex::new(file),
        write_failed: Mutex::new(None),
        partial: Mutex::new(HashMap::new()),
        sender,
    });
    let task = {
        let lines = std::sync::Arc::clone(&lines);
        tokio::spawn(async move {
            let RunGate {
                env,
                auto,
                paths,
                approver,
            } = gate;
            Shell::new(root, env, "bash")
                .run(SCRIPT, auto, &paths, &approver, &*lines)
                .await
        })
    };
    // Kills the script (its process group) if this call is dropped.
    let abort = AbortOnDrop(task.abort_handle());
    let deadline = tokio::time::Instant::now() + timeout;
    let mut task = task;
    // `None`: the timeout killed the script.
    let ran = loop {
        tokio::select! {
            line = receiver.recv() => {
                if let Some(line) = line {
                    on_line(line)?;
                }
            }
            ran = &mut task => break Some(ran),
            () = tokio::time::sleep_until(deadline) => break None,
        }
    };
    drop(abort);
    // The lines the script wrote before it ended or was killed.
    while let Ok(line) = receiver.try_recv() {
        on_line(line)?;
    }
    if let Some(error) = lock(&lines.write_failed).take() {
        return Err(error).with_context(|| format!("could not write {}", log.display()));
    }
    lock(&lines.log)
        .sync_data()
        .with_context(|| format!("could not sync {}", log.display()))?;
    let ran = match ran {
        Some(Ok(ran)) => ran,
        Some(Err(error)) => anyhow::bail!("the benchmark's task failed: {error}"),
        None => return Ok(RunEnd::TimedOut),
    };
    Ok(match ran.end {
        End::Finished { status } | End::Exited { status } => RunEnd::Exited(status),
        End::Refused {
            command, refusal, ..
        } => RunEnd::Refused(format!(
            "`{command}` did not run: {}",
            RefusalText::of(refusal)
        )),
    })
}

struct AbortOnDrop(tokio::task::AbortHandle);

impl Drop for AbortOnDrop {
    fn drop(&mut self) {
        self.0.abort();
    }
}
