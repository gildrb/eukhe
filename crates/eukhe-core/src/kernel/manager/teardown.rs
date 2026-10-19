//! Teardown: graceful shutdown, resource cleanup, and process killing.

use super::{
    json, live_kernels, lock, oneshot, orphan_journal, Arc, Duration, Inner, KernelShutdownOptions,
    KernelState, MemoSlot, OrphanReap, Signal, HOST_REQUEST_SHUTDOWN_TIMEOUT_MS,
    KERNEL_SHUTDOWN_TIMEOUT_MS,
};
use crate::kernel::shared::{KERNEL_KILL_VERIFY_MS, KERNEL_TERM_GRACE_MS};

// ---------------------------------------------------------------------------
// Teardown
// ---------------------------------------------------------------------------

impl Inner {
    /// Resolves `true` when this call performed the cleanup (false: a
    /// concurrent teardown won; a joiner's options are ignored — the first
    /// caller's policy wins). The memoization joins concurrent callers onto
    /// one in-flight shutdown.
    pub(crate) async fn shutdown_for_cleanup(
        self: &Arc<Self>,
        opts: KernelShutdownOptions,
    ) -> anyhow::Result<bool> {
        let existing = lock(&self.shutdown_memo).as_ref().cloned();
        if let Some(existing) = existing {
            let _ = existing.wait().await;
            return Ok(false);
        }
        let slot = {
            let mut memo = lock(&self.shutdown_memo);
            let slot = MemoSlot::new();
            *memo = Some(slot.clone());
            slot
        };
        lock(&self.guarded).teardown_in_flight += 1;
        self.supersede_protocol_repair();
        let performed = self.perform_shutdown(opts).await;
        lock(&self.guarded).teardown_in_flight -= 1;
        slot.finish(None);
        {
            let mut memo = lock(&self.shutdown_memo);
            if matches!(memo.as_ref(), Some(current) if Arc::ptr_eq(current, &slot)) {
                *memo = None;
            }
        }
        Ok(performed)
    }

    pub(crate) async fn perform_shutdown(self: &Arc<Self>, opts: KernelShutdownOptions) -> bool {
        if lock(&self.guarded).state == KernelState::Shutdown {
            live_kernels::remove(self);
            // Scoped read: re-locking inside the comparison self-deadlocks.
            let graceful_in_flight = {
                let g = lock(&self.guarded);
                g.graceful_shutdown_generation == Some(g.start_generation)
            };
            if graceful_in_flight {
                return false;
            }
            self.cleanup_resources(Signal::Term);
            return true;
        }
        // Captured before any await: teardowns and newer starts bump the counter.
        let generation = lock(&self.guarded).start_generation;
        if opts.snapshot {
            self.flush_snapshot_for_dispose().await;
            if self.start_stale(generation) {
                return false;
            }
        }
        // Protocol shutdown first: the runtime closes MCP servers and kills
        // live bash() process groups a bare hard-kill would leak.
        let protocol_shutdown_available = lock(&self.guarded).state == KernelState::Running;
        {
            let mut g = lock(&self.guarded);
            g.state = KernelState::Shutdown;
            g.graceful_shutdown_generation = Some(generation);
        }
        live_kernels::remove(self);

        let mut request_id: Option<String> = None;
        if opts.drain_host_requests {
            let in_flight = {
                let mut g = lock(&self.guarded);
                std::mem::take(&mut g.host_inflight)
            };
            if !in_flight.is_empty() {
                self.wait_for_host_requests_to_settle(in_flight, HOST_REQUEST_SHUTDOWN_TIMEOUT_MS)
                    .await;
            }
        }
        if protocol_shutdown_available
            && !self.start_stale(generation)
            && lock(&self.child).is_some()
        {
            let id = uuid::Uuid::new_v4().to_string();
            let (done_tx, done_rx) = oneshot::channel::<()>();
            lock(&self.guarded)
                .pending_done_waiters
                .insert(id.clone(), done_tx);
            request_id = Some(id.clone());
            let frame = json!({ "type": "shutdown", "id": id });
            let send_result = tokio::time::timeout(
                Duration::from_millis(KERNEL_SHUTDOWN_TIMEOUT_MS),
                self.write_line(&frame),
            )
            .await;
            let sent = match send_result {
                Ok(Ok(())) => true,
                Ok(Err(error)) => {
                    self.append_diagnostic(&format!("failed to send shutdown request: {error:#}"));
                    false
                }
                Err(_) => {
                    self.append_diagnostic("timed out sending shutdown request");
                    false
                }
            };
            if sent {
                let graceful_reply = async {
                    let _ = done_rx.await;
                };
                let deadline =
                    tokio::time::sleep(Duration::from_millis(KERNEL_SHUTDOWN_TIMEOUT_MS));
                let mut failed = false;
                tokio::select! {
                    () = graceful_reply => {}
                    () = self.wait_for_kernel_exit() => {}
                    () = deadline => {
                        failed = true;
                        self.append_diagnostic(&format!(
                            "graceful shutdown failed (killing instead): Kernel did not shut down within {KERNEL_SHUTDOWN_TIMEOUT_MS}ms"
                        ));
                    }
                }
                if !failed {
                    let deadline =
                        tokio::time::sleep(Duration::from_millis(KERNEL_SHUTDOWN_TIMEOUT_MS));
                    tokio::select! {
                        () = self.wait_for_kernel_exit() => {}
                        () = deadline => {}
                    }
                }
            }
        }
        if let Some(id) = request_id {
            lock(&self.guarded).pending_done_waiters.remove(&id);
        }
        {
            let mut g = lock(&self.guarded);
            if g.graceful_shutdown_generation == Some(generation) {
                g.graceful_shutdown_generation = None;
            }
        }
        if self.start_stale(generation) {
            return false;
        }
        // The graceful phases end the kernel in the normal case. A kernel
        // whose exit is not seen gets SIGTERM, then SIGKILL; each signal
        // goes to its whole process group.
        let unexited = lock(&self.child).as_ref().and_then(|child| {
            child
                .exit_rx
                .borrow()
                .is_none()
                .then(|| (child.pid, child.exit_rx.clone()))
        });
        let Some((pid, mut exit_rx)) = unexited else {
            self.cleanup_resources(Signal::Term);
            return true;
        };
        let _delivered = crate::platform::process::signal_process_group(pid, Signal::Term);
        let term_grace = Duration::from_millis(KERNEL_TERM_GRACE_MS);
        if tokio::time::timeout(term_grace, exit_rx.wait_for(Option::is_some))
            .await
            .is_ok()
        {
            self.cleanup_resources(Signal::Term);
            return true;
        }
        self.append_diagnostic(&format!(
            "kernel process group {pid} did not exit within {KERNEL_TERM_GRACE_MS}ms of SIGTERM; sending SIGKILL"
        ));
        self.cleanup_resources(Signal::Kill);
        let kill_verify = Duration::from_millis(KERNEL_KILL_VERIFY_MS);
        if tokio::time::timeout(kill_verify, exit_rx.wait_for(Option::is_some))
            .await
            .is_err()
        {
            self.append_diagnostic(&format!(
                "kernel process {pid} survived SIGKILL for {KERNEL_KILL_VERIFY_MS}ms"
            ));
        }
        true
    }

    /// Tear the child down: stop timers, fail pending work, close pipes, kill
    /// the process, and reap any `bash()` process groups it journaled.
    pub(crate) fn cleanup_resources(&self, kill_signal: Signal) {
        let had_background_work = {
            let mut g = lock(&self.guarded);
            // Any teardown invalidates in-flight starts.
            g.start_generation += 1;
            if let Some(timer) = lock(&self.snapshot_timer).take() {
                timer.abort();
            }
            g.late_handlers.clear();
            g.pending_done_waiters.clear();
            g.bash_activity_waiters.clear();
            g.factory_activity_waiters.clear();
            g.mcp_status_waiters.clear();
            let had_background_work = !g.background_bash_handles.is_empty();
            g.background_bash_handles.clear();
            // Stale pre-teardown background output must not surface after a restart.
            g.pending_background_output.clear();
            g.pending_background_output_chars = 0;
            g.pending_background_output_dropped = super::DroppedText::default();
            had_background_work
        };
        // Teardown kills the handles with the kernel, so owed continuations
        // waiting on them must hear the settlement once before it is lost.
        if had_background_work {
            self.notify_background_work_settled();
        }
        self.reject_active_execution("Kernel has been shut down");
        *lock(&self.stderr_log) = None;
        let child = lock(&self.child).take();
        lock(&self.guarded).ready_tx.take();
        if let Some(child) = child {
            // Dropping the write pipe signals EOF to the child's stdin reader;
            // closing stdin is equivalent to a shutdown request.
            if let Ok(mut stdin) = child.stdin.try_lock() {
                *stdin = None;
            }
            let pid = child.pid;
            // The kernel leads its own process group (see `do_start`). A
            // wrapped kernel's group is its wrapper's: the kill ends the
            // wrapper, the closed stdin ends the stub, and the stub kills
            // its own `bash()` groups on the way out.
            let _delivered = crate::platform::process::signal_process_group(pid, kill_signal);
            // A killed/crashed local kernel cannot run its own shutdown
            // hook, so the host reaps the bash() process groups it
            // journaled under this pid.
            match &child.orphan_reap {
                OrphanReap::Journal(journal) if pid > 0 => {
                    if let Err(error) = orphan_journal::reap_kernel_orphan_processes(journal, pid) {
                        self.append_diagnostic(&format!(
                            "orphan journal {}: {error}",
                            journal.display()
                        ));
                    }
                }
                OrphanReap::Journal(_) | OrphanReap::Stub => {}
            }
        }
        *lock(&self.start_memo) = None;
    }
}

#[cfg(test)]
mod tests {
    use crate::kernel::shared::{KernelManagerOptions, KernelShutdownOptions};
    use crate::kernel::{manager::KernelStartOptions, ReplKernelManager};

    /// A kernel that ignores SIGTERM and never answers the shutdown
    /// request is killed: the teardown ends with no kernel process alive.
    #[cfg(unix)]
    #[tokio::test]
    async fn teardown_kills_a_kernel_that_ignores_sigterm() {
        use std::os::unix::fs::PermissionsExt;

        let dir = tempfile::TempDir::new().expect("temp dir");
        let pid_file = dir.path().join("kernel.pid");
        let python = dir.path().join("ignores-sigterm");
        std::fs::write(
            &python,
            format!(
                "#!/usr/bin/env python3\nimport json, os, signal, time\nsignal.signal(signal.SIGTERM, signal.SIG_IGN)\nopen({:?}, 'w').write(str(os.getpid()))\nprint(json.dumps({{'event': 'ready', 'protocol': 3, 'python': '3.13.0'}}), flush=True)\ntime.sleep(60)\n",
                pid_file.display().to_string()
            ),
        )
        .expect("write fake kernel");
        std::fs::set_permissions(&python, std::fs::Permissions::from_mode(0o755))
            .expect("chmod fake kernel");
        let manager = ReplKernelManager::new(KernelManagerOptions {
            python: Some(python),
            ..Default::default()
        });
        manager
            .start(KernelStartOptions::default())
            .await
            .expect("ready handshake");
        let pid: u32 = std::fs::read_to_string(&pid_file)
            .expect("kernel pid")
            .parse()
            .expect("pid number");
        let performed = manager
            .shutdown(KernelShutdownOptions {
                snapshot: false,
                drain_host_requests: false,
            })
            .await
            .expect("shutdown");
        let alive = eukhe_types::platform::process::is_process_alive(pid).expect("liveness");
        assert_eq!((performed, alive), (true, false));
    }
}
