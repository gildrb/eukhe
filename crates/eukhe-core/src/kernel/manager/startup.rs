//! Startup and child wiring: kernel process spawn, python resolution, stderr
//! capture, and readiness handshake.

use std::ops::ControlFlow;

use super::frames::{
    Admission, FrameSplitter, Gate, ProtocolFault, Refusal, MAX_PROTOCOL_LINE_BYTES,
};
use super::{
    anyhow, live_kernels, lock, oneshot, orphan_journal, Arc, AsyncReadExt, BufReader, ChildHandle,
    Duration, ExitInfo, HashMap, Inner, KernelShutdownOptions, KernelStartOptions, KernelState,
    Mutex, Ordering, OrphanReap, Signal, StderrLog, Write, KERNEL_STDERR_LOG_BUDGET_MARKER,
    MAX_KERNEL_STDERR_CHARS, MAX_KERNEL_STDERR_LOG_BYTES, READY_TIMEOUT_MS, REPL_PROTOCOL_VERSION,
};

use crate::kernel::transport::{KernelTransport, KernelWrapper};

// ---------------------------------------------------------------------------
// Startup and child wiring
// ---------------------------------------------------------------------------

/// Numbers each spawned kernel's orphan journal within this host process.
static NEXT_ORPHAN_JOURNAL: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// What one start runs: the host interpreter it resolved, or the
/// transport's wrapper.
enum Launch<'a> {
    Local(std::path::PathBuf),
    Wrapped(&'a KernelWrapper),
}

/// The environment of a local kernel, and of every program the host runs
/// for an agent the same way (the `bash` tool's external steps): this
/// process's environment with `overlay` over it.
pub(crate) fn local_env(overlay: &HashMap<String, String>) -> HashMap<String, String> {
    let mut env: HashMap<String, String> = std::env::vars().collect();
    env.extend(
        overlay
            .iter()
            .map(|(key, value)| (key.clone(), value.clone())),
    );
    env
}

impl Inner {
    /// True when a teardown (or newer start) superseded the start that
    /// captured `generation`.
    pub(crate) fn start_stale(&self, generation: u64) -> bool {
        lock(&self.guarded).start_generation != generation
    }

    /// Child stderr tail for error messages: at most the last 1024 chars.
    fn stderr_tail(&self, limit: usize) -> String {
        let stderr = lock(&self.guarded).kernel_stderr.clone();
        let chars: Vec<char> = stderr.chars().collect();
        let start = chars.len().saturating_sub(limit);
        chars[start..].iter().collect()
    }

    /// Append raw kernel stderr text to the diagnostics tail (last 8 KiB).
    fn append_kernel_stderr_text(&self, text: &str) {
        let mut g = lock(&self.guarded);
        g.kernel_stderr.push_str(text);
        if g.kernel_stderr.len() > MAX_KERNEL_STDERR_CHARS {
            let chars: Vec<char> = g.kernel_stderr.chars().collect();
            let start = chars.len().saturating_sub(MAX_KERNEL_STDERR_CHARS);
            g.kernel_stderr = chars[start..].iter().collect();
        }
    }

    /// Append one `[kernel]`-prefixed diagnostic line.
    pub(crate) fn append_diagnostic(&self, message: &str) {
        let line = if message.ends_with('\n') {
            format!("[kernel] {message}")
        } else {
            format!("[kernel] {message}\n")
        };
        self.append_kernel_stderr_text(&line);
    }

    /// Open (and rotate when oversized) the kernel stderr log. The write budget
    /// is the file's remaining capacity, so current and `.old` each stay near
    /// the ceiling.
    fn open_stderr_log(&self) -> Option<Arc<Mutex<StderrLog>>> {
        let path = self.options.stderr_log_path.as_ref()?;
        match self.open_stderr_log_at(path) {
            Ok(log) => Some(log),
            Err(error) => {
                self.append_diagnostic(&format!("cannot open kernel stderr log: {error}"));
                None
            }
        }
    }

    fn open_stderr_log_at(&self, path: &std::path::Path) -> anyhow::Result<Arc<Mutex<StderrLog>>> {
        if let Some(parent) = path.parent() {
            // Owner-only directory, matching the other private session
            // artifacts the kernel manager creates.
            crate::platform::perms::create_dir_all_private(parent)?;
        }
        let mut size = path.metadata().map_or(0, |m| m.len());
        if size > MAX_KERNEL_STDERR_LOG_BYTES {
            let old = path.with_extension("log.old");
            // Tighten before the move: a renamed log keeps its mode, and the
            // rotated file holds the exception payloads worth protecting.
            if let Err(error) = crate::platform::perms::restrict_file(path) {
                self.append_diagnostic(&format!("cannot rotate kernel stderr log: {error}"));
            } else {
                let _ = std::fs::remove_file(&old);
                match std::fs::rename(path, &old) {
                    Ok(()) => size = 0,
                    Err(error) => {
                        // A failed rotation must not cost the log: keep appending.
                        self.append_diagnostic(&format!(
                            "cannot rotate kernel stderr log: {error}"
                        ));
                    }
                }
            }
        }
        let mut options = std::fs::OpenOptions::new();
        options.create(true).append(true);
        // Owner-only file bits on create; kernel stderr can carry exception payloads.
        crate::platform::perms::set_private_mode(&mut options);
        let file = options.open(path)?;
        // Exact bits despite the umask; tightens a pre-existing loose log.
        crate::platform::perms::restrict_open_file(&file)?;
        Ok(Arc::new(Mutex::new(StderrLog {
            file,
            budget: MAX_KERNEL_STDERR_LOG_BYTES.saturating_sub(size),
        })))
    }

    /// The Python interpreter this kernel runs on: the explicit option when
    /// present, else the auto-bootstrapped kernel venv.
    async fn resolve_python(
        self: &Arc<Self>,
        options: &KernelStartOptions,
    ) -> anyhow::Result<std::path::PathBuf> {
        if let Some(python) = &self.options.python {
            return Ok(python.clone());
        }
        if let Some(cached) = lock(&self.resolved_python).clone() {
            return Ok(cached);
        }
        let progress = options.on_bootstrap_progress.clone();
        let skills = self.options.python_skills.clone();
        let python = crate::kernel::bootstrap::ensure_kernel_python(
            crate::kernel::bootstrap::EnsureKernelPythonOptions {
                python_skills: skills,
                on_progress: progress,
            },
        )
        .await?;
        *lock(&self.resolved_python) = Some(python.clone());
        Ok(python)
    }

    /// Perform the startup: resolve the interpreter, spawn `python -m rlm.repl`,
    /// complete the protocol handshake, and mark the kernel running.
    pub(crate) async fn do_start(
        self: &Arc<Self>,
        options: &KernelStartOptions,
    ) -> anyhow::Result<()> {
        {
            let mut g = lock(&self.guarded);
            if g.state != KernelState::Idle {
                return Ok(());
            }
            g.start_generation += 1;
            g.state = KernelState::Starting;
        }
        // Tracked from the moment startup begins so cleanup can dispose a
        // kernel that is still booting.
        live_kernels::add(self);

        // A wrapped kernel runs the sandbox's interpreter: the host venv
        // bootstrap is for a local kernel only.
        let launch = match &self.options.transport {
            KernelTransport::Local => match self.resolve_python(options).await {
                Ok(python) => Launch::Local(python),
                Err(error) => {
                    if self.start_stale(self.current_generation()) {
                        // Never touch a newer start's state.
                        return Err(error);
                    }
                    live_kernels::remove(self);
                    let mut g = lock(&self.guarded);
                    if g.state != KernelState::Shutdown {
                        g.state = KernelState::Idle;
                    }
                    return Err(error);
                }
            },
            KernelTransport::Wrapped(wrapper) => Launch::Wrapped(wrapper),
        };
        let generation = self.current_generation();
        if self.start_stale(generation) {
            return Err(anyhow!("Kernel start superseded"));
        }
        if lock(&self.guarded).state == KernelState::Shutdown {
            return Err(anyhow!("Kernel was disposed during startup"));
        }

        let cwd = self.options.cwd.clone();
        let (command, orphan_reap, program) = match &launch {
            Launch::Local(python) => {
                // bash.py journals its process groups under this pid into
                // the kernel's own journal so the host can reap them if the
                // runtime dies without running its shutdown hook.
                let orphan_journal = std::env::temp_dir().join(format!(
                    "eukhe-kernel-orphans-{}-{}.jsonl",
                    std::process::id(),
                    NEXT_ORPHAN_JOURNAL.fetch_add(1, Ordering::Relaxed)
                ));
                let mut env = local_env(&self.options.env);
                env.insert(
                    "EUKHE_KERNEL_OWNER_PID".to_string(),
                    std::process::id().to_string(),
                );
                env.insert(
                    orphan_journal::ORPHAN_PROCESS_JOURNAL_ENV.to_string(),
                    orphan_journal.to_string_lossy().into_owned(),
                );
                let mut command = tokio::process::Command::new(python);
                // `-P` (Python >= 3.11, the runtime's floor): the working
                // directory is not prepended to `sys.path`, so a project's
                // own `rlm/`, `json.py`, ... cannot shadow the runtime or
                // the stdlib. `rlm.repl` appends the cwd at the END of
                // `sys.path` after boot, so cells still import project-only
                // modules; cells run with `cwd` as their working dir.
                command.args(["-P", "-m", "rlm.repl"]);
                if let Some(cwd) = &cwd {
                    command.current_dir(cwd);
                }
                command.env_clear().envs(env);
                (
                    Ok(command),
                    OrphanReap::Journal(orphan_journal),
                    python.display().to_string(),
                )
            }
            Launch::Wrapped(wrapper) => {
                // The wrapper is a host process with the host's environment
                // (docker and ssh need theirs); the kernel in the sandbox
                // gets only the entries the launch script sets. A remote
                // kernel's process groups are not host pids: no journal, no
                // host reap (its own shutdown and stdin-EOF exit reap them).
                let mut kernel_env: Vec<(String, String)> = self
                    .options
                    .env
                    .iter()
                    .map(|(key, value)| (key.clone(), value.clone()))
                    .collect();
                kernel_env.sort();
                let python_paths: Vec<std::path::PathBuf> = self
                    .options
                    .python_skills
                    .iter()
                    .flat_map(|skill| [skill.package_path.clone(), skill.package_path.join("src")])
                    .collect();
                let launch_cwd = cwd
                    .clone()
                    .or_else(|| std::env::current_dir().ok())
                    .unwrap_or_default();
                let started = wrapper
                    .launch(
                        &launch_cwd,
                        &kernel_env,
                        |name| std::env::var(name).ok(),
                        &python_paths,
                    )
                    .map_err(|error| format!("kernel transport: {error}"));
                let program = wrapper.argv_prefix.join(" ");
                let command = started.map(|launch| {
                    for key in &launch.unmapped_env {
                        self.append_diagnostic(&format!(
                            "kernel transport: {key} left out (its host path is outside every mapped path)"
                        ));
                    }
                    let mut command = tokio::process::Command::new(&launch.argv[0]);
                    command.args(&launch.argv[1..]);
                    command
                });
                (command, OrphanReap::Stub, program)
            }
        };
        let spawned = command.and_then(|mut command| {
            command
                .stdin(std::process::Stdio::piped())
                .stdout(std::process::Stdio::piped())
                .stderr(std::process::Stdio::piped());
            // Its own process group: an abort the cell ignores past the
            // grace kills the group, so subprocesses the cell started die
            // with it. A wrapped kernel's group is the wrapper's: killing
            // it ends the wrapper, and the stub sees its stdin close.
            command.process_group(0);
            command.spawn().map_err(|error| error.to_string())
        });
        let child = match spawned {
            Ok(child) => child,
            Err(error) => {
                // Fail a pending start promptly instead of riding out the
                // ready timeout. The interpreter itself failed to launch, so
                // the memoized runtime-ready result is stale: drop it so a
                // startup retry re-probes (and rebuilds when the probe fails).
                crate::kernel::bootstrap::invalidate_runtime_probe_cache();
                self.append_diagnostic(&format!("spawn error: {error}"));
                {
                    let mut g = lock(&self.guarded);
                    g.state = KernelState::Shutdown;
                }
                live_kernels::remove(self);
                if let Some(tx) = lock(&self.guarded).ready_tx.take() {
                    let _ = tx.send(Err(anyhow!("spawn error: {error}")));
                }
                self.cleanup_resources(Signal::Term);
                return Err(anyhow!("failed to spawn kernel {program}: {error}"));
            }
        };
        let (ready_tx, ready_rx) = oneshot::channel::<anyhow::Result<i64>>();
        {
            let mut g = lock(&self.guarded);
            g.startup_protocol_error = None;
            g.ready_tx = Some(ready_tx);
        }
        self.wire_child(child, generation, orphan_reap);

        let protocol = match self.wait_for_ready(ready_rx, generation).await {
            Ok(protocol) => protocol,
            Err(error) => {
                if self.start_stale(generation) {
                    // Never tear down a newer start's kernel.
                    return Err(error);
                }
                // The child died or never reached ready, so the memoized
                // runtime-ready result is stale: drop it and let a startup
                // retry re-probe (and rebuild the venv when the probe fails).
                crate::kernel::bootstrap::invalidate_runtime_probe_cache();
                let can_retry_startup = lock(&self.guarded).state != KernelState::Shutdown;
                // Only the call that performed the cleanup may resurrect to
                // idle; a concurrent kill()/teardown owns the state otherwise.
                let performed = self
                    .perform_shutdown(KernelShutdownOptions::default())
                    .await;
                if performed && can_retry_startup {
                    lock(&self.guarded).state = KernelState::Idle;
                }
                return Err(error);
            }
        };
        if self.start_stale(generation) {
            return Err(anyhow!("Kernel start superseded"));
        }
        if let Some(startup_error) = lock(&self.guarded).startup_protocol_error.clone() {
            return Err(anyhow!("{startup_error}"));
        }
        if protocol != REPL_PROTOCOL_VERSION as i64 {
            // A stale runtime passed a memoized probe's key but speaks the
            // wrong protocol: the memo is stale, so a retry re-probes.
            crate::kernel::bootstrap::invalidate_runtime_probe_cache();
            return Err(anyhow!(
                "Kernel runtime speaks protocol {protocol}, expected {REPL_PROTOCOL_VERSION}. \
                 Update eukhe-runtime in the kernel Python (EUKHE_KERNEL_PYTHON) to match this eukhe."
            ));
        }
        {
            let mut g = lock(&self.guarded);
            g.state = KernelState::Running;
            // The freshness memo describes the namespace of the kernel
            // that committed it: a freshly started kernel has no committed
            // description yet (its restore/bootstrap settles clear it too,
            // see resolve_execution — this is the boundary itself).
            g.capture_freshness = None;
            g.freshness_epoch += 1;
        }
        Ok(())
    }

    pub(crate) fn current_generation(&self) -> u64 {
        lock(&self.guarded).start_generation
    }

    /// Wire the spawned child: protocol reader, stderr tail + log, and the
    /// exit watcher that settles the manager when the process dies.
    fn wire_child(
        self: &Arc<Self>,
        mut child: tokio::process::Child,
        generation: u64,
        orphan_reap: OrphanReap,
    ) {
        let pid = child.id().map_or(-1, |p| p as i32);
        let stdin = child.stdin.take();
        let stdout = child.stdout.take();
        let stderr = child.stderr.take();
        let stdin = Arc::new(tokio::sync::Mutex::new(stdin));
        let (exit_tx, exit_rx) = tokio::sync::watch::channel::<Option<ExitInfo>>(None);
        *lock(&self.child) = Some(ChildHandle {
            pid,
            stdin: stdin.clone(),
            exit_rx,
            orphan_reap,
        });

        if let Some(stdout) = stdout {
            // Weak, upgraded per event: the readers stay blocked on the
            // child's pipes for the kernel's whole life, so a strong handle
            // here would outlive every manager clone and the process would
            // survive the drop that should have torn it down (#232 hygiene:
            // a dropped session leaked its live kernel until the runtime's
            // owner watchdog reaped it, if ever).
            let inner = Arc::downgrade(self);
            let stdin_for_error = stdin;
            tokio::spawn(async move {
                // The reader holds the stdin handle for its whole life.
                let _stdin = stdin_for_error;
                let mut reader = BufReader::new(stdout);
                let mut splitter = FrameSplitter::new(MAX_PROTOCOL_LINE_BYTES);
                let mut gate = Gate::new(MAX_PROTOCOL_LINE_BYTES);
                // An unrecoverable stream's residue must not reach a handler
                // before the protocol repair kills the child: keep draining
                // the pipe (so a wedged child cannot block on backpressure)
                // and discard.
                let mut poisoned = false;
                let mut refused: Vec<(String, Refusal)> = Vec::new();
                let mut chunk = vec![0u8; 64 * 1024];
                loop {
                    let n = match reader.read(&mut chunk).await {
                        Ok(0) | Err(_) => break,
                        Ok(n) => n,
                    };
                    if poisoned {
                        continue;
                    }
                    let Some(inner) = inner.upgrade() else {
                        break;
                    };
                    let serves = |kind: &str| inner.options.host_handlers.serves(kind);
                    // The gate decides on every frame in order; refusals
                    // are answered in that order once the read is cut.
                    let _ = splitter.feed(&chunk[..n], &mut |frame| {
                        match gate.admit(frame, &serves) {
                            Admission::Serve(event) => inner.handle_event(event),
                            Admission::Refuse { id, refusal } => refused.push((id, refusal)),
                            Admission::Drop(fault) => {
                                inner.append_diagnostic(&format!("dropped kernel frame: {fault}"));
                            }
                            Admission::Fail(fault) => {
                                inner.fail_protocol_frame(generation, &fault.to_string());
                                // A malformed line ends at its newline: the
                                // frames after it still frame (the shutdown
                                // reply of a corrupt child among them).
                                match fault {
                                    ProtocolFault::Malformed(_) => {}
                                    ProtocolFault::Oversize { .. } | ProtocolFault::NotUtf8 => {
                                        poisoned = true;
                                        return ControlFlow::Break(());
                                    }
                                }
                            }
                        }
                        ControlFlow::Continue(())
                    });
                    for (id, refusal) in refused.drain(..) {
                        inner.send_host_refusal(&id, &refusal).await;
                    }
                }
            });
        }

        if let Some(stderr) = stderr {
            // Weak like the stdout reader (same drop semantics), upgraded
            // per chunk; the log file drains to EOF regardless.
            let inner = Arc::downgrade(self);
            let log = self.open_stderr_log();
            // Keep the host-side handle so teardown drops its reference; the
            // reader task's handle closes the file when the stream ends.
            (*lock(&self.stderr_log)).clone_from(&log);
            tokio::spawn(async move {
                let mut reader = BufReader::new(stderr);
                let mut pending: Vec<u8> = Vec::new();
                let mut buffer = [0u8; 4096];
                // Incremental UTF-8 decoding: a chunk boundary can split a
                // multi-byte character, so only complete sequences surface.
                let decode = |pending: &mut Vec<u8>| {
                    let text = String::from_utf8_lossy(pending);
                    let decoded = text.into_owned();
                    pending.clear();
                    decoded
                };
                loop {
                    match reader.read(&mut buffer).await {
                        Ok(0) | Err(_) => break,
                        Ok(n) => {
                            pending.extend_from_slice(&buffer[..n]);
                            let decoded = decode(&mut pending);
                            let Some(inner) = inner.upgrade() else {
                                break;
                            };
                            inner.append_kernel_stderr_text(&decoded);
                            if let Some(log) = &log {
                                let mut log = lock(log);
                                if log.budget >= n as u64 {
                                    let _ = log.file.write_all(&buffer[..n]);
                                    let _ = log.file.flush();
                                    log.budget -= n as u64;
                                } else if log.budget > 0 {
                                    let _ = log
                                        .file
                                        .write_all(KERNEL_STDERR_LOG_BUDGET_MARKER.as_bytes());
                                    let _ = log.file.flush();
                                    log.budget = 0;
                                }
                            }
                        }
                    }
                }
                if let Some(inner) = inner.upgrade() {
                    if !pending.is_empty() {
                        inner.append_kernel_stderr_text(&decode(&mut pending));
                    }
                    // Both the natural EOF and the kill path end here; the ready
                    // handshake waits on this notification for the final tail.
                    inner.stderr_closed_flag.store(true, Ordering::SeqCst);
                    inner.stderr_closed.notify_waiters();
                }
            });
        }

        // Weak like the readers: the watcher stays blocked on the child's
        // exit for the kernel's whole life, and owning the manager strongly
        // would keep the kernel alive past the last manager's drop (the very
        // retention the readers no longer hold). The child handle stays here
        // so the exit is still reaped after a teardown kill.
        let inner = Arc::downgrade(self);
        tokio::spawn(async move {
            let exit = match child.wait().await {
                Ok(status) => ExitInfo {
                    code: status.code(),
                    signal: crate::platform::process::termination_signal(&status),
                },
                Err(_) => ExitInfo {
                    code: None,
                    signal: None,
                },
            };
            let _ = exit_tx.send(Some(exit));
            let Some(inner) = inner.upgrade() else {
                return;
            };
            if inner.start_stale(generation) {
                return;
            }
            // append_diagnostic re-locks `guarded`, so it must run OUTSIDE
            // this lock scope (a std Mutex is not reentrant).
            let was_live = {
                let mut g = lock(&inner.guarded);
                let was_live = g.state != KernelState::Shutdown;
                g.state = KernelState::Shutdown;
                was_live
            };
            if was_live {
                inner.append_diagnostic(&format!(
                    "unexpected exit code={} signal={}",
                    exit.code.map_or("null".to_string(), |c| c.to_string()),
                    exit.signal.map_or("null".to_string(), |s| s.to_string()),
                ));
            }
            live_kernels::remove(&inner);
            // This exit is part of an in-flight graceful shutdown(): that call
            // owns the teardown and runs cleanup itself.
            // Scoped reads: locking the same std Mutex twice in one
            // expression self-deadlocks (non-reentrant).
            let graceful_in_flight = {
                let g = lock(&inner.guarded);
                g.graceful_shutdown_generation == Some(g.start_generation)
            };
            if graceful_in_flight {
                return;
            }
            inner.cleanup_resources(Signal::Term);
        });
    }

    /// The protocol handshake: the runtime's `ready` frame, the child dying
    /// first, or the 30-second ceiling — whichever comes first.
    async fn wait_for_ready(
        &self,
        ready_rx: oneshot::Receiver<anyhow::Result<i64>>,
        generation: u64,
    ) -> anyhow::Result<i64> {
        let mut ready_rx = ready_rx;
        let mut exit_rx = lock(&self.child)
            .as_ref()
            .map(|c| c.exit_rx.clone())
            .ok_or_else(|| anyhow!("Kernel ready state is missing"))?;
        let deadline = tokio::time::Instant::now() + Duration::from_millis(READY_TIMEOUT_MS);
        let mut protocol = None;
        while protocol.is_none() {
            let timeout = tokio::time::sleep_until(deadline);
            tokio::select! {
                ready = &mut ready_rx => {
                    match ready {
                        Ok(Ok(value)) => protocol = Some(value),
                        Ok(Err(error)) => return Err(error),
                        // Dropped only by teardown, which resolves the wait itself.
                        Err(_) => return Err(anyhow!("Kernel ready state is missing")),
                    }
                }
                _ = exit_rx.changed() => {
                    if exit_rx.borrow().is_some() {
                        // Final stderr chunks can still be in flight; wait for
                        // the drained pipe (the ready deadline still bounds it).
                        let stderr_drain = async {
                            loop {
                                if self.stderr_closed_flag.load(Ordering::SeqCst) {
                                    return;
                                }
                                self.stderr_closed.notified().await;
                            }
                        };
                        tokio::select! {
                            () = stderr_drain => {}
                            () = tokio::time::sleep_until(deadline) => {}
                        }
                        let tail = self.stderr_tail(1024);
                        return Err(anyhow!("Kernel exited before ready. stderr:\n{}", if tail.is_empty() { "(empty)".to_string() } else { tail }));
                    }
                }
                () = timeout => {
                    let tail = self.stderr_tail(1024);
                    return Err(anyhow!("Kernel did not become ready within {READY_TIMEOUT_MS}ms. stderr tail:\n{}", if tail.is_empty() { "(empty)".to_string() } else { tail }));
                }
            }
        }
        let _ = generation;
        Ok(protocol.expect("loop only exits with a protocol value"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::manager::ReplKernelManager;
    use crate::kernel::shared::KernelManagerOptions;

    fn manager() -> ReplKernelManager {
        ReplKernelManager::new(KernelManagerOptions::default())
    }

    fn temp_root(tag: &str) -> std::path::PathBuf {
        let dir =
            std::env::temp_dir().join(format!("pa-stderr-perms-{}-{tag}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        dir
    }

    #[test]
    fn kernel_stderr_log_is_owner_only() {
        let root = temp_root("create");
        let path = root.join("artifacts").join("kernel-stderr.log");
        let log = manager()
            .inner
            .open_stderr_log_at(&path)
            .expect("stderr log opens");
        drop(log);
        assert_eq!(
            crate::platform::perms::file_mode(&path),
            Some(eukhe_types::platform::access::PRIVATE_FILE_MODE)
        );
        assert_eq!(
            crate::platform::perms::file_mode(path.parent().expect("parent")),
            Some(eukhe_types::platform::access::PRIVATE_DIR_MODE)
        );
        let _ = std::fs::remove_dir_all(&root);
    }

    #[test]
    fn kernel_stderr_log_rotation_tightens_a_world_readable_log() {
        use std::io::Write;

        let root = temp_root("rotate");
        let path = root.join("kernel-stderr.log");
        std::fs::create_dir_all(&root).expect("dir");
        let mut loose = std::fs::OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(&path)
            .expect("loose log");
        {
            use std::os::unix::fs::PermissionsExt;
            let _ = loose.set_permissions(std::fs::Permissions::from_mode(0o644));
        }
        loose
            .write_all(&vec![0u8; (MAX_KERNEL_STDERR_LOG_BYTES + 1) as usize])
            .expect("fill");
        drop(loose);
        let log = manager()
            .inner
            .open_stderr_log_at(&path)
            .expect("stderr log opens");
        drop(log);
        let old = path.with_extension("log.old");
        assert_eq!(
            crate::platform::perms::file_mode(&old),
            Some(eukhe_types::platform::access::PRIVATE_FILE_MODE),
            "the rotated file holds the historical exception payloads"
        );
        assert_eq!(
            crate::platform::perms::file_mode(&path),
            Some(eukhe_types::platform::access::PRIVATE_FILE_MODE),
            "the fresh log is tightened despite a loose predecessor"
        );
        let _ = std::fs::remove_dir_all(&root);
    }
}
