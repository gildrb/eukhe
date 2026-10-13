//! Execution bookkeeping: request writes, interrupts, the kill after an
//! unanswered abort, and
//! active-execution resolution plus late-sent agent message handlers.

use super::{
    anyhow, json, live_kernels, lock, parse_sent_agent_message, AbortSignal, ActiveExecution, Arc,
    AsyncWriteExt, BackgroundOutput, ExecuteResult, ExecuteStatus, Inner, InternalExecuteResult,
    KernelState, LateSentAgentMessageCallback, Signal, Value, AGENT_MESSAGE_DISPLAY_MIME,
    MAX_LATE_SENT_AGENT_MESSAGE_HANDLERS,
};

impl Inner {
    /// Write one JSON-lines request frame; completes when the OS accepted the bytes.
    pub(crate) async fn write_line(&self, frame: &Value) -> anyhow::Result<()> {
        let stdin = {
            let child = lock(&self.child);
            child
                .as_ref()
                .map(|c| c.stdin.clone())
                .ok_or_else(|| anyhow!("Kernel stdin is not connected"))?
        };
        let mut guard = stdin.lock().await;
        let Some(stdin) = guard.as_mut() else {
            return Err(anyhow!("Kernel stdin is not connected"));
        };
        let mut line = frame.to_string();
        line.push('\n');
        stdin.write_all(line.as_bytes()).await?;
        stdin.flush().await?;
        Ok(())
    }

    pub(crate) async fn interrupt(&self, id: Option<&str>) -> anyhow::Result<()> {
        let mut frame = json!({ "type": "interrupt" });
        if let Some(id) = id {
            frame["id"] = json!(id);
        }
        self.write_line(&frame).await
    }

    /// The abort's interrupt went unanswered past the grace: settle the
    /// request as killed with the output so far, then kill the kernel's
    /// process group. The manager turns defunct; the next start revives the
    /// last namespace snapshot.
    pub(crate) fn kill_after_abort_grace(&self, execution: &Arc<ActiveExecution>) {
        {
            let g = lock(&self.guarded);
            let is_active = matches!(g.active_execution.as_ref(), Some(active) if Arc::ptr_eq(active, execution));
            if !is_active {
                return;
            }
        }
        lock(&execution.buffers).status = ExecuteStatus::Killed;
        self.resolve_execution(execution);
        self.supersede_protocol_repair();
        lock(&self.guarded).state = KernelState::Shutdown;
        live_kernels::remove_inner(self);
        self.cleanup_resources(Signal::Kill);
    }

    pub(crate) fn reject_active_execution(&self, message: &str) {
        let execution = {
            let mut g = lock(&self.guarded);
            g.active_execution.take()
        };
        if let Some(execution) = execution {
            if let Some(tx) = lock(&execution.result_tx).take() {
                let _ = tx.send(Err(anyhow!("{message}")));
            }
        }
    }

    pub(crate) fn finish_active_execution(&self, execution: &Arc<ActiveExecution>) {
        let is_active = {
            let g = lock(&self.guarded);
            matches!(g.active_execution.as_ref(), Some(active) if Arc::ptr_eq(active, execution))
        };
        if !is_active {
            return;
        }
        self.resolve_execution(execution);
    }

    fn resolve_execution(&self, execution: &Arc<ActiveExecution>) {
        {
            let mut g = lock(&self.guarded);
            if matches!(g.active_execution.as_ref(), Some(active) if Arc::ptr_eq(active, execution))
            {
                g.active_execution = None;
            }
        }
        let mut buffers = lock(&execution.buffers);
        if !buffers.settled {
            buffers.settled = true;
            {
                let mut g = lock(&self.guarded);
                g.completed_executions += 1;
                if !execution.opts.internal {
                    g.user_executions += 1;
                }
                // The freshness memo describes the namespace as of its
                // commit. A settled request that runs user-namespace code
                // (an execute — the bootstrap class included, internal or
                // not) or replaces the namespace wholesale (a restore) ends
                // that description: the next capture must re-dump. The
                // state reads (the listing) and the captures themselves do
                // not clear it — the captures re-arm the memo at their own
                // commits.
                if execution.namespace_code || execution.restores_namespace {
                    g.capture_freshness = None;
                    g.freshness_epoch += 1;
                }
            }
            if let Some(callback) = execution.opts.on_late_sent_agent_message.clone() {
                self.register_late_sent_agent_message_handler(&execution.request_id, callback);
            }

            let stdout = std::mem::take(&mut buffers.stdout);
            let stderr = std::mem::take(&mut buffers.stderr);
            let result = buffers.result.take();
            let mut status = buffers.status;
            if status != ExecuteStatus::Killed
                && execution
                    .opts
                    .signal
                    .as_ref()
                    .is_some_and(AbortSignal::is_aborted)
            {
                status = ExecuteStatus::Aborted;
            }

            let background_output = std::mem::take(&mut buffers.background_output);
            buffers.background_output_chars = 0;
            let background_dropped = std::mem::take(&mut buffers.background_output_dropped);
            let done_fields = buffers.done_fields.take();
            let result = ExecuteResult {
                stdout,
                stderr,
                result,
                attachments: (!buffers.attachments.is_empty())
                    .then(|| std::mem::take(&mut buffers.attachments)),
                sent_agent_messages: (!buffers.sent_agent_messages.is_empty())
                    .then(|| std::mem::take(&mut buffers.sent_agent_messages)),
                bash_commands: buffers.bash_commands.take(),
                background_output: (!background_output.is_empty() || background_dropped.bytes > 0)
                    .then_some(BackgroundOutput {
                        text: background_output,
                        dropped_bytes: background_dropped.bytes,
                        dropped_newlines: background_dropped.newlines,
                    }),
                status,
                error: buffers.error.take(),
                duration_ms: execution.started.elapsed().as_millis() as u64,
            };
            drop(buffers);
            if let Some(tx) = lock(&execution.result_tx).take() {
                let _ = tx.send(Ok(InternalExecuteResult {
                    result,
                    done_fields,
                }));
            }
        }
    }

    fn register_late_sent_agent_message_handler(
        &self,
        request_id: &str,
        callback: LateSentAgentMessageCallback,
    ) {
        let mut g = lock(&self.guarded);
        g.late_handlers
            .retain(|(existing, _)| existing != request_id);
        g.late_handlers
            .push_back((request_id.to_string(), callback));
        while g.late_handlers.len() > MAX_LATE_SENT_AGENT_MESSAGE_HANDLERS {
            g.late_handlers.pop_front();
        }
    }

    pub(crate) fn dispatch_late_sent_agent_message(
        &self,
        request_id: Option<&str>,
        data: &Value,
    ) -> bool {
        let Some(request_id) = request_id else {
            return false;
        };
        let Some(payload) = data.get(AGENT_MESSAGE_DISPLAY_MIME) else {
            return false;
        };
        let Some(message) = parse_sent_agent_message(payload) else {
            return false;
        };
        let callback = {
            let mut g = lock(&self.guarded);
            let Some(position) = g.late_handlers.iter().position(|(id, _)| id == request_id) else {
                return false;
            };
            let callback = g
                .late_handlers
                .remove(position)
                .expect("position checked")
                .1;
            // Refresh recency, matching the TS map delete+set.
            g.late_handlers
                .push_back((request_id.to_string(), callback.clone()));
            callback
        };
        callback(message);
        true
    }
}
