//! Request plumbing: enqueue/execute state machine, signal enum, and failure
//! description helpers.

use super::{
    anyhow, json, lock, merge_signals, oneshot, AbortSignal, ActiveExecution, Arc, AsyncWriteExt,
    Duration, ExecBuffers, ExecuteOptions, ExecuteResult, ExecuteStatus, Instant,
    InternalExecuteResult, KernelStartOptions, KernelState, Mutex, ReplKernelManager, Request,
    KERNEL_ABORT_GRACE_MS,
};

// ---------------------------------------------------------------------------
// Request plumbing
// ---------------------------------------------------------------------------

pub(crate) use crate::platform::process::Signal;

/// Append `text` up to `max_chars` Unicode scalars in all, keeping the
/// buffered count in sync and adding the characters past the cap to
/// `dropped`.
pub(crate) fn append_capped(
    buffer: &mut String,
    dropped: &mut usize,
    chars: &mut usize,
    text: &str,
    max_chars: usize,
) {
    let remaining = max_chars.saturating_sub(*chars);
    match text.char_indices().nth(remaining) {
        None => {
            buffer.push_str(text);
            *chars += text.chars().count();
        }
        Some((end, _)) => {
            buffer.push_str(&text[..end]);
            *chars = max_chars;
            *dropped += text[end..].chars().count();
        }
    }
}

pub(crate) fn describe_failure(result: &ExecuteResult) -> String {
    if let Some(error) = &result.error {
        if error.evalue.is_empty() {
            return error.ename.clone();
        }
        return format!("{}: {}", error.ename, error.evalue);
    }
    result.stderr.trim_end().to_string()
}

impl ReplKernelManager {
    /// Queue one protocol request (execute or state op) behind every other request.
    #[allow(clippy::too_many_lines)]
    pub(crate) async fn enqueue_request(
        &self,
        request: Request,
        code: &str,
        opts: ExecuteOptions,
        execution_timeout_ms: Option<u64>,
    ) -> anyhow::Result<InternalExecuteResult> {
        let started = Instant::now();
        if let Some(signal) = &opts.signal {
            if signal.is_aborted() {
                return Ok(InternalExecuteResult::aborted(started));
            }
        }
        self.start(KernelStartOptions {
            signal: opts.signal.clone(),
            on_bootstrap_progress: None,
        })
        .await?;
        if self.state() == KernelState::Shutdown {
            return Err(anyhow!("Kernel has been shut down"));
        }
        if lock(&self.inner.guarded).flushing_snapshot_for_dispose && !opts.internal {
            return Err(anyhow!("Kernel is shutting down"));
        }
        if !opts.protocol_repair {
            self.ensure_kernel_rebootstrapped(opts.signal.as_ref())
                .await?;
        }
        // Aborted while waiting on the re-bootstrap: settle now instead of
        // parking on the queue slot behind the still-running bootstrap.
        if let Some(signal) = &opts.signal {
            if signal.is_aborted() {
                return Ok(InternalExecuteResult::aborted(started));
            }
        }
        // Re-check: a final flush may have started while this request awaited
        // the lazy re-bootstrap; admitting it now would splice it between the
        // flush\'s captured queue and the final snapshot, unbounding the teardown.
        if lock(&self.inner.guarded).flushing_snapshot_for_dispose && !opts.internal {
            return Err(anyhow!("Kernel is shutting down"));
        }

        let queue_guard = self.inner.execution_queue.lock().await;

        // A repair started while this request was queued:
        // release the slot so the repair\'s own restore can run, then requeue
        // behind it.
        if lock(&self.inner.guarded).protocol_repair.is_some() && !opts.protocol_repair {
            drop(queue_guard);
            self.wait_for_protocol_repair(opts.signal.as_ref()).await?;
            return Box::pin(self.enqueue_request(request, code, opts, execution_timeout_ms)).await;
        }

        if self.state() == KernelState::Shutdown {
            return Err(anyhow!("Kernel has been shut down"));
        }

        // Bound the execution with an out-of-band abort (interrupt + grace).
        let timeout_signal = execution_timeout_ms.map(|ms| {
            let signal = AbortSignal::new();
            let timer_signal = signal.clone();
            tokio::spawn(async move {
                tokio::time::sleep(Duration::from_millis(ms)).await;
                timer_signal.abort();
            });
            signal
        });
        let merged = merge_signals(opts.signal.as_ref(), timeout_signal.clone());
        let mut opts = opts;
        opts.signal = merged;
        let result = self.execute_inner(request, code, opts, started).await;
        if let Some(signal) = &timeout_signal {
            signal.abort();
        }
        result
    }

    fn state(&self) -> KernelState {
        lock(&self.inner.guarded).state
    }

    #[allow(clippy::too_many_lines)]
    async fn execute_inner(
        &self,
        request: Request,
        code: &str,
        opts: ExecuteOptions,
        started: Instant,
    ) -> anyhow::Result<InternalExecuteResult> {
        let request_id = uuid::Uuid::new_v4().to_string();

        if let Some(signal) = &opts.signal {
            if signal.is_aborted() {
                return Ok(InternalExecuteResult::aborted(started));
            }
        }
        if lock(&self.inner.guarded).active_execution.is_some() {
            return Err(anyhow!("Kernel already has an active execution"));
        }

        let (result_tx, mut result_rx) =
            oneshot::channel::<anyhow::Result<InternalExecuteResult>>();
        let mut buffers = ExecBuffers {
            status: ExecuteStatus::Ok,
            ..ExecBuffers::default()
        };
        {
            let mut g = lock(&self.inner.guarded);
            buffers.background_output = std::mem::take(&mut g.pending_background_output);
            buffers.background_output_chars =
                std::mem::take(&mut g.pending_background_output_chars);
            buffers.background_output_dropped =
                std::mem::take(&mut g.pending_background_output_dropped);
            g.active_execution = None; // reset below with the execution in hand
        }
        let (namespace_code, restores_namespace) = match &request {
            Request::Execute { .. } => (true, false),
            Request::Restore { .. } => (false, true),
            _ => (false, false),
        };
        let execution = Arc::new(ActiveExecution {
            request_id: request_id.clone(),
            code: code.to_string(),
            started,
            namespace_code,
            restores_namespace,
            buffers: Mutex::new(buffers),
            result_tx: Mutex::new(Some(result_tx)),
            opts,
        });
        {
            let mut g = lock(&self.inner.guarded);
            g.active_execution = Some(execution.clone());
        }

        // Abort watcher: interrupts the kernel out-of-band, then kills it
        // after the grace window if the runtime did not settle the cell.
        if let Some(signal) = execution.opts.signal.clone() {
            // Weak on both sides: a never-fired signal leaves this watcher
            // pending forever, and a strong manager would pin the kernel
            // past the last manager's drop (the reader-retention class).
            let inner = Arc::downgrade(&self.inner);
            let weak_exec = Arc::downgrade(&execution);
            tokio::spawn(async move {
                signal.cancelled().await;
                let Some(execution) = weak_exec.upgrade() else {
                    return;
                };
                let Some(inner) = inner.upgrade() else {
                    return;
                };
                // A blocked request write holds the stdin mutex. Do not let an
                // interrupt queued behind it postpone the kill forever.
                // Dropping the interrupt at this deadline cannot tear its
                // frame: the ~60-byte frame is one write on a non-blocking
                // pipe, all-or-nothing below PIPE_BUF.
                let deadline =
                    tokio::time::Instant::now() + Duration::from_millis(KERNEL_ABORT_GRACE_MS);
                tokio::select! {
                    _ = inner.interrupt(Some(&execution.request_id)) => {},
                    () = tokio::time::sleep_until(deadline) => {}
                }
                tokio::time::sleep_until(deadline).await;
                inner.kill_after_abort_grace(&execution);
            });
        }

        if !execution.opts.internal {
            lock(&self.inner.guarded).last_cell_code = Some(code.to_string());
        }

        let mut frame = request.to_json();
        frame["id"] = json!(request_id);

        let mut send_task = {
            let writer = lock(&self.inner.child).as_ref().map(|c| c.stdin.clone());
            let Some(stdin) = writer else {
                {
                    let mut g = lock(&self.inner.guarded);
                    g.active_execution = None;
                }
                return Err(anyhow!("Kernel stdin is not connected"));
            };
            let mut line = frame.to_string();
            line.push('\n');
            tokio::spawn(async move {
                let mut guard = stdin.lock().await;
                let Some(stdin) = guard.as_mut() else {
                    return Err(anyhow!("Kernel stdin is not connected"));
                };
                stdin.write_all(line.as_bytes()).await?;
                stdin.flush().await?;
                Ok(())
            })
        };

        let mut settled_result: Option<anyhow::Result<InternalExecuteResult>> = None;
        let send_outcome: anyhow::Result<()> = {
            let send_promise = &mut send_task;
            tokio::select! {
                r = send_promise => r.unwrap_or_else(|e| Err(anyhow!("{e}"))),
                settled = &mut result_rx => {
                    // The cell settled before the write completed (fast runtime,
                    // or a kill). Only a killed request may skip waiting for the
                    // write; a failed write on a live cell must surface.
                    let settled: anyhow::Result<InternalExecuteResult> = match settled {
                        Ok(result) => result,
                        Err(_) => Err(anyhow!("Kernel has been shut down")),
                    };
                    // The killed kernel never reads the rest of the request.
                    let early_settle = matches!(&settled, Ok(result) if result.result.status == ExecuteStatus::Killed);
                    if early_settle {
                        // A blocked request writer would otherwise retain stdin's
                        // mutex after the caller returned.
                        send_task.abort();
                        settled_result = Some(settled);
                    } else {
                        // Surfacing a failed write outranks the settled cell.
                        if let Err(error) = (&mut send_task).await.unwrap_or_else(|e| Err(anyhow!("{e}"))) {
                            settled_result = Some(Err(error));
                        } else {
                            settled_result = Some(settled);
                        }
                    }
                    Ok(())
                }
            }
        };

        match settled_result.take() {
            Some(result) => result,
            None => match send_outcome {
                Err(error) => {
                    {
                        let mut g = lock(&self.inner.guarded);
                        if matches!(g.active_execution.as_ref(), Some(active) if Arc::ptr_eq(active, &execution))
                        {
                            g.active_execution = None;
                        }
                    }
                    Err(error)
                }
                Ok(()) => match result_rx.await {
                    Ok(result) => result,
                    Err(_) => Err(anyhow!("Kernel has been shut down")),
                },
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::append_capped;

    #[cfg(unix)]
    #[tokio::test]
    async fn bounded_execute_settles_when_kernel_stops_reading_stdin() {
        use super::*;
        use std::os::unix::fs::PermissionsExt;

        let dir = tempfile::TempDir::new().expect("temp dir");
        let python = dir.path().join("ready-but-not-reading");
        std::fs::write(
            &python,
            "#!/usr/bin/env python3\nimport json, time\nprint(json.dumps({'event': 'ready', 'protocol': 3, 'python': '3.13.0'}), flush=True)\ntime.sleep(30)\n",
        )
        .expect("write fake kernel");
        std::fs::set_permissions(&python, std::fs::Permissions::from_mode(0o755))
            .expect("chmod fake kernel");
        let manager = ReplKernelManager::new(crate::kernel::shared::KernelManagerOptions {
            python: Some(python),
            ..Default::default()
        });
        manager
            .start(KernelStartOptions::default())
            .await
            .expect("ready handshake");
        // Larger than the stdin pipe: the request writer holds its mutex while
        // waiting for this non-reader, so the interrupt write cannot acquire it.
        let code = "x".repeat(1024 * 1024);
        let result = tokio::time::timeout(
            Duration::from_secs(4),
            manager.execute_bounded(&code, ExecuteOptions::default(), Some(100)),
        )
        .await;
        let result = result
            .expect("timeout must settle even when the interrupt cannot write")
            .expect("bounded execute returns a result");
        assert_eq!(result.status, ExecuteStatus::Killed);
        assert!(
            manager.is_defunct(),
            "the unanswered abort kills the kernel"
        );
        manager.kill();
    }

    #[test]
    fn capped_append_keeps_whole_characters_and_counts_the_dropped_rest() {
        let frames = ["", "a", "é", "🍁", "xy", "é🍁abc", "", "tail"];
        let all: String = frames.concat();
        for cap in [0, 1, 2, 3, 4, 7, 65_536] {
            let mut actual = (String::new(), 0, 0);
            for text in frames {
                append_capped(&mut actual.0, &mut actual.1, &mut actual.2, text, cap);
            }
            let kept: String = all.chars().take(cap).collect();
            let total = all.chars().count();
            assert_eq!(
                actual,
                (
                    kept.clone(),
                    total - kept.chars().count(),
                    kept.chars().count()
                )
            );
        }
    }
}
