//! Host request handling: execute-side requests answered by the host
//! (harness/goal/etc.) and their settle/exit waits.

use super::frames::Refusal;
use super::{anyhow, json, lock, Arc, Duration, HostRequestPayload, Inner, Value};
use crate::kernel::shared::{host_request_unavailable, CellJob, KernelHostRequest};
use crate::kernel::transport::KernelTransport;

/// The `version` of an `fs.*` rejection the kernel transport answers: a
/// sandbox path outside every shared mount.
const FS_TRANSPORT_VERSION: &str = "transport@1";

/// The cell source attached to a host request is capped at this many
/// characters (TS #2475: `MAX_CELL_SOURCE_CHARS`, repl-manager.ts:81-82):
/// the spawning cell's source rides on every host request it triggers, and
/// an uncapped multi-KB cell re-shipped per progress note (and persisted
/// per child as spawn code) dwarfs the request it tags.
const MAX_CELL_SOURCE_CHARS: usize = 2 * 1024;

/// Cap a cell source for host-request attachment: a source within the cap
/// passes verbatim; a longer one keeps the first `MAX_CELL_SOURCE_CHARS`
/// characters and carries the truncation marker so the consumer knows the
/// prefix is partial (TS repl-manager.ts:110-111's cap helper).
fn cap_cell_source(code: &str) -> String {
    if code.chars().count() <= MAX_CELL_SOURCE_CHARS {
        code.to_string()
    } else {
        let head: String = code.chars().take(MAX_CELL_SOURCE_CHARS).collect();
        format!("{head}\n[... cell source truncated at {MAX_CELL_SOURCE_CHARS} chars ...]")
    }
}

// ---------------------------------------------------------------------------
// Host requests
// ---------------------------------------------------------------------------

impl Inner {
    /// Run one host request the gate served (`frames.rs`) on its handler
    /// and send its one reply over the protocol.
    pub(crate) fn start_host_request(self: &Arc<Self>, request_id: String, data: Value) {
        let inner = Arc::clone(self);
        let task = tokio::spawn(async move {
            let result = inner
                .handle_host_request(&data)
                .await
                .map_err(|error| format!("{error:#}"));
            inner.send_host_reply(&request_id, result).await;
        });
        let mut g = lock(&self.guarded);
        // Completed task handles are dropped so the inflight set stays bounded.
        g.host_inflight.retain(|handle| !handle.is_finished());
        g.host_inflight.push(task);
    }

    /// Send the one reply to host request `request_id`: its handler's
    /// result, or the error of a failed request.
    #[tracing::instrument(level = "debug", skip(self, reply))]
    pub(crate) async fn send_host_reply(&self, request_id: &str, reply: Result<Value, String>) {
        let data = match reply {
            Ok(result) => json!({ "status": "ok", "result": result }),
            Err(error) => {
                self.append_diagnostic(&format!("host request failed for {request_id}: {error}"));
                json!({ "status": "error", "error": error })
            }
        };
        self.write_host_reply(request_id, data).await;
    }

    /// Send the one reply to a host request the gate refused
    /// ([`Refusal::reply`]).
    #[tracing::instrument(level = "debug", skip(self))]
    pub(crate) async fn send_host_refusal(&self, request_id: &str, refusal: &Refusal) {
        self.append_diagnostic(&format!("host request refused for {request_id}: {refusal}"));
        self.write_host_reply(request_id, refusal.reply()).await;
    }

    async fn write_host_reply(&self, request_id: &str, data: Value) {
        let frame = json!({ "type": "host_reply", "id": request_id, "data": data });
        if let Err(error) = self.write_line(&frame).await {
            self.append_diagnostic(&format!(
                "failed to send host request reply for {request_id}: {error:#}"
            ));
        }
    }

    async fn handle_host_request(&self, data: &Value) -> anyhow::Result<Value> {
        let Some(obj) = data.as_object() else {
            return Err(anyhow!("host request payload must be an object"));
        };
        let request_type = obj
            .get("type")
            .and_then(Value::as_str)
            .filter(|t| !t.is_empty())
            .ok_or_else(|| anyhow!("host request payload must have a string type"))?;
        // Tag the request with the cell that triggered it. A blocking call is
        // still the in-flight execution; detached spawns fire after the
        // scheduling cell goes idle, so fall back to that last cell's source.
        // The durable call context only rides an active execution whose call
        // has not settled: a settled call's API rejects every operation, and
        // a detached cell's call settled at the blocking budget.
        let (cell_source_code, call) = {
            let g = lock(&self.guarded);
            let active = g.active_execution.as_ref();
            (
                active
                    .map(|e| cap_cell_source(&e.code))
                    .or_else(|| g.last_cell_code.as_deref().map(cap_cell_source)),
                active
                    .filter(|e| !e.opts.job.as_ref().is_some_and(CellJob::is_detached))
                    .and_then(|e| e.opts.call.clone()),
            )
        };
        let mut payload = obj.clone();
        if let Some(code) = &cell_source_code {
            payload.insert("cellSourceCode".to_string(), Value::String(code.clone()));
        }
        // A wrapped kernel's `fs.*` paths are the sandbox's: they reach the
        // handler as the host's, through the shared mounts, and the reply's
        // paths go back as the sandbox's. A path outside every mount is
        // refused here as the fs functions' typed rejection (`FsError`
        // with reason `outside` in the kernel); no handler runs.
        let path_map = match &self.options.transport {
            KernelTransport::Wrapped(wrapper) if request_type.starts_with("fs.") => {
                Some(&wrapper.path_map)
            }
            KernelTransport::Wrapped(_) | KernelTransport::Local => None,
        };
        if let Some(path_map) = path_map {
            if let Err(error) = path_map.fs_request_to_host(request_type, &mut payload) {
                return Ok(json!({
                    "outcome": "rejected",
                    "version": FS_TRANSPORT_VERSION,
                    "reason": "outside",
                    "message": format!("{request_type}: {error}"),
                }));
            }
        }
        let mut result = if let Some(dispatch) = self.options.host_handlers.dispatch() {
            dispatch
                .dispatch(KernelHostRequest {
                    request_type: request_type.to_string(),
                    data: Value::Object(payload),
                    cell_source_code,
                    call,
                })
                .await?
        } else {
            let handler = self
                .options
                .host_handlers
                .get(request_type)
                .ok_or_else(|| host_request_unavailable(request_type))?
                .clone();
            handler(HostRequestPayload {
                data: Value::Object(payload),
                cell_source_code: None,
            })
            .await?
        };
        if let Some(path_map) = path_map {
            path_map.fs_reply_to_sandbox(&mut result);
        }
        Ok(result)
    }

    /// Wait (bounded) for the in-flight host request tasks to settle.
    pub(crate) async fn wait_for_host_requests_to_settle(
        &self,
        tasks: Vec<tokio::task::JoinHandle<()>>,
        timeout_ms: u64,
    ) {
        let all = async {
            for task in tasks {
                let _ = task.await;
            }
        };
        if tokio::time::timeout(Duration::from_millis(timeout_ms), all)
            .await
            .is_err()
        {
            self.append_diagnostic(&format!(
                "timed out waiting {timeout_ms}ms for host request task(s) during shutdown"
            ));
        }
    }

    pub(crate) async fn wait_for_kernel_exit(&self) {
        let exit_rx = match lock(&self.child).as_ref() {
            Some(child) => child.exit_rx.clone(),
            None => return,
        };
        let mut exit_rx = exit_rx;
        if exit_rx.borrow().is_some() {
            return;
        }
        loop {
            if exit_rx.borrow().is_some() {
                return;
            }
            if exit_rx.changed().await.is_err() {
                return;
            }
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;

    fn marker() -> String {
        format!("\n[... cell source truncated at {MAX_CELL_SOURCE_CHARS} chars ...]")
    }

    #[test]
    fn a_source_within_the_cap_attaches_verbatim() {
        let code = "x".repeat(MAX_CELL_SOURCE_CHARS);
        assert_eq!(cap_cell_source(&code), code);
    }

    #[test]
    fn an_oversized_source_keeps_the_prefix_and_carries_the_marker() {
        let code = "x".repeat(MAX_CELL_SOURCE_CHARS + 1);
        let capped = cap_cell_source(&code);
        let expected = format!("{}{}", "x".repeat(MAX_CELL_SOURCE_CHARS), marker());
        assert_eq!(capped, expected);
    }

    #[test]
    fn a_short_source_is_untouched() {
        let code = "print(1)";
        assert_eq!(cap_cell_source(code), code);
    }

    #[test]
    fn the_cap_lands_on_a_character_boundary() {
        // A multi-byte tail: the cap must slice by characters, never split one.
        let code = format!("{}{}", "é".repeat(MAX_CELL_SOURCE_CHARS), "é");
        let capped = cap_cell_source(&code);
        assert!(capped.starts_with(&"é".repeat(MAX_CELL_SOURCE_CHARS)));
        assert!(capped.ends_with(&marker()));
    }
}
