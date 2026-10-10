//! The stop sequences of the daemon-attached ACP session (TS
//! `stopSessionWork` and its callers): `session/cancel`, `session/close`,
//! and the EOF teardown. Each stop holds a session input pause while it
//! aborts the worker's work, and a failed stop fences the session (TS
//! `entry.stopFailure`).

use std::sync::Arc;

use eukhe_types::daemon::DaemonCommand;
use serde_json::{json, Map, Value};
use tokio::sync::Mutex;

use super::{
    clear_connection_servers, fetch_rlm_children, jsonrpc, producer, CancelOrder, CancelStop,
    DaemonAcpState, DaemonBinding, DaemonLink,
};

pub(super) async fn cancel_order(
    params: &Value,
    state: &Arc<Mutex<DaemonAcpState>>,
) -> CancelOrder {
    let Some(session_id) = params.get("sessionId").and_then(Value::as_str) else {
        return CancelOrder::None;
    };
    let mut guard = state.lock().await;
    if guard.session_close_done.is_some() {
        return CancelOrder::WaitForClose {
            session_id: session_id.to_string(),
        };
    }
    arm_cancel_locked(session_id, &mut guard)
}

pub(super) fn arm_cancel_locked(session_id: &str, guard: &mut DaemonAcpState) -> CancelOrder {
    let Some(hosted) = guard
        .session
        .as_mut()
        .filter(|hosted| hosted.acp_session_id == session_id)
    else {
        return CancelOrder::None;
    };
    if hosted.cancelling {
        return CancelOrder::None;
    }
    let admission_id = match hosted.turn.as_mut() {
        Some(turn) => {
            turn.cancelled = true;
            Some(turn.admission_id.clone())
        }
        None if hosted.stop_failure.is_none() => return CancelOrder::None,
        None => None,
    };
    let (done_tx, done_rx) = tokio::sync::watch::channel(false);
    hosted.cancel_task = Some(done_rx);
    hosted.cancelling = true;
    CancelOrder::Armed(CancelStop {
        acp_session_id: hosted.acp_session_id.clone(),
        daemon_session_id: hosted.daemon_active_session_id.clone(),
        admission_id,
        done: done_tx,
    })
}

pub(super) async fn wait_for_session_close(state: &Arc<Mutex<DaemonAcpState>>) {
    let close_done = { state.lock().await.session_close_done.clone() };
    if let Some(mut done) = close_done {
        let _ = done.wait_for(|finished| *finished).await;
    }
}

pub(super) async fn run_cancel_stop(
    stop: CancelStop,
    link: &Arc<DaemonLink>,
    state: &Arc<Mutex<DaemonAcpState>>,
) {
    let outcome = match acquire_stop_input_pause(link, state, &stop.acp_session_id).await {
        Ok(lease) => {
            match stop_session_work(link, &stop.daemon_session_id, stop.admission_id.as_deref())
                .await
            {
                Ok(()) => {
                    release_session_input_pause(link, &stop.daemon_session_id, &lease.pause_id)
                        .await
                        .map(|()| lease)
                }
                Err(error) => Err(error),
            }
        }
        Err(error) => Err(error),
    };
    {
        let mut guard = state.lock().await;
        let released_closed = matches!(
            &outcome,
            Ok(lease) if guard.closed_input_pause_id.as_deref() == Some(&lease.pause_id)
        );
        if let Some(hosted) = guard
            .session
            .as_mut()
            .filter(|hosted| hosted.acp_session_id == stop.acp_session_id)
        {
            hosted.cancelling = false;
            hosted.cancel_task = None;
            match &outcome {
                Ok(lease) => {
                    if hosted.input_pause_id.as_deref() == Some(&lease.pause_id) {
                        hosted.input_pause_id = None;
                    }
                    if hosted.input_pause_key.as_deref() == Some(&lease.lease_key) {
                        hosted.input_pause_key = None;
                    }
                    hosted.stop_failure = None;
                }
                Err(error) => hosted.stop_failure = Some(error.to_string()),
            }
        }
        if released_closed {
            guard.closed_input_pause_id = None;
            guard.closed_input_pause_key = None;
        }
    }
    let _ = stop.done.send(true);
}

/// TS `stopSessionWork`: abort the worker's running and queued work, stop
/// the owned admission (a prompt sent before the stop but committed after
/// the abort), wait the idle, then cancel the RLM children.
async fn stop_session_work(
    link: &Arc<DaemonLink>,
    daemon_session_id: &str,
    admission_id: Option<&str>,
) -> anyhow::Result<()> {
    link.request_ok(DaemonCommand::AbortAndClearQueue {
        id: None,
        active_session_id: daemon_session_id.to_string(),
        rest: Map::default(),
    })
    .await?;
    if let Some(admission_id) = admission_id {
        cancel_owned_admission(link, daemon_session_id, admission_id).await;
    }
    link.request_ok(DaemonCommand::WaitForIdle {
        id: None,
        active_session_id: daemon_session_id.to_string(),
        wait_for_rlm_quiescence: None,
        rest: Map::default(),
    })
    .await?;
    cancel_outstanding_rlm_children(link, daemon_session_id).await
}

/// TS `cancelOutstandingRlmChildren`: cancel every roster row, no status
/// filter — a row already settling keeps its own settle, and the cancels
/// run one after another (TS `Promise.allSettled` is the declared
/// divergence). A failed roster fetch or the first failed cancel fails the
/// stop; every row still gets its cancel.
async fn cancel_outstanding_rlm_children(
    link: &Arc<DaemonLink>,
    daemon_session_id: &str,
) -> anyhow::Result<()> {
    let children = fetch_rlm_children(link, daemon_session_id).await?;
    let mut failure = None;
    for child in children {
        let child_id = child
            .get("id")
            .and_then(Value::as_str)
            .unwrap_or_default()
            .to_string();
        if let Err(error) = link
            .request_ok(DaemonCommand::CancelRlmChild {
                id: None,
                active_session_id: daemon_session_id.to_string(),
                child_id,
                rest: Map::default(),
            })
            .await
        {
            failure.get_or_insert(error);
        }
    }
    failure.map_or(Ok(()), Err)
}

/// TS `cancel_prompt_admission` with `cancelOwned`: a committed prompt's
/// running turn aborts.
async fn cancel_owned_admission(
    link: &Arc<DaemonLink>,
    daemon_session_id: &str,
    admission_id: &str,
) {
    let _ = link
        .request(DaemonCommand::CancelPromptAdmission {
            id: None,
            active_session_id: daemon_session_id.to_string(),
            admission_id: admission_id.to_string(),
            cancel_owned: Some(true),
            rest: Map::default(),
        })
        .await;
}

struct InputPauseLease {
    pause_id: String,
    lease_key: String,
}

async fn acquire_stop_input_pause(
    link: &Arc<DaemonLink>,
    state: &Arc<Mutex<DaemonAcpState>>,
    acp_session_id: &str,
) -> anyhow::Result<InputPauseLease> {
    let (daemon_session_id, lease_key) = {
        let mut guard = state.lock().await;
        let Some(hosted) = guard
            .session
            .as_mut()
            .filter(|hosted| hosted.acp_session_id == acp_session_id)
        else {
            anyhow::bail!("Unknown ACP session: {acp_session_id}");
        };
        let lease_key = hosted
            .input_pause_key
            .clone()
            .unwrap_or_else(|| uuid::Uuid::new_v4().to_string());
        hosted.input_pause_key = Some(lease_key.clone());
        (hosted.daemon_active_session_id.clone(), lease_key)
    };
    let response = link
        .request(DaemonCommand::AcquireSessionInputPause {
            id: None,
            active_session_id: daemon_session_id.clone(),
            lease_key: lease_key.clone(),
            rest: Map::default(),
        })
        .await?;
    if !response.success {
        anyhow::bail!(response
            .error
            .unwrap_or_else(|| "unknown error".to_string()));
    }
    let pause_id = response
        .data
        .unwrap_or(Value::Null)
        .get("pauseId")
        .and_then(Value::as_str)
        .map(str::to_string)
        .ok_or_else(|| anyhow::anyhow!("the daemon returned no session input pause id"))?;
    {
        let mut guard = state.lock().await;
        if let Some(hosted) = guard
            .session
            .as_mut()
            .filter(|hosted| hosted.acp_session_id == acp_session_id)
        {
            hosted.input_pause_id = Some(pause_id.clone());
        }
    }
    Ok(InputPauseLease {
        pause_id,
        lease_key,
    })
}

pub(super) async fn release_session_input_pause(
    link: &Arc<DaemonLink>,
    daemon_session_id: &str,
    pause_id: &str,
) -> anyhow::Result<()> {
    link.request_ok(DaemonCommand::ReleaseSessionInputPause {
        id: None,
        active_session_id: daemon_session_id.to_string(),
        pause_id: pause_id.to_string(),
        rest: Map::default(),
    })
    .await
}

pub(super) async fn handle_session_close(
    id: Value,
    params: Value,
    link: &Arc<DaemonLink>,
    state: &Arc<Mutex<DaemonAcpState>>,
    tx: producer::FrameSink,
    close_done: tokio::sync::watch::Sender<bool>,
    owner_id: String,
) {
    let session_id = params
        .get("sessionId")
        .and_then(Value::as_str)
        .unwrap_or_default()
        .to_string();
    let cancel_task = {
        let guard = state.lock().await;
        guard
            .session
            .as_ref()
            .filter(|hosted| hosted.acp_session_id == session_id)
            .and_then(|hosted| hosted.cancel_task.clone())
    };
    if let Some(mut cancel_task) = cancel_task {
        let _ = cancel_task.changed().await;
    }
    let (acp_session_id, daemon_session_id, config, producer, admission_id) = {
        let mut guard = state.lock().await;
        let Some(hosted) = guard
            .session
            .as_mut()
            .filter(|hosted| hosted.acp_session_id == session_id)
        else {
            drop(guard);
            state.lock().await.session_close_done = None;
            let _ = close_done.send(true);
            return;
        };
        hosted.cancelling = true;
        if let Some(turn) = hosted.turn.as_mut() {
            turn.cancelled = true;
        }
        let admission_id = hosted.turn.as_ref().map(|turn| turn.admission_id.clone());
        (
            hosted.acp_session_id.clone(),
            hosted.daemon_active_session_id.clone(),
            Arc::clone(&hosted.config),
            Arc::clone(&hosted.producer),
            admission_id,
        )
    };
    let close_result = match acquire_stop_input_pause(link, state, &acp_session_id).await {
        Ok(lease) => {
            match stop_session_work(link, &daemon_session_id, admission_id.as_deref()).await {
                Ok(()) => {
                    // The serialized config work settles before the
                    // producer fences (TS `await configTask`).
                    let _ = config.queue.lock().await;
                    producer.close().await;
                    let _ =
                        clear_connection_servers(link, &daemon_session_id, &owner_id, state).await;
                    let mut guard = state.lock().await;
                    guard.closed_input_pause_id = Some(lease.pause_id.clone());
                    guard.closed_input_pause_key = Some(lease.lease_key.clone());
                    if let Some(hosted) = guard
                        .session
                        .as_mut()
                        .filter(|hosted| hosted.acp_session_id == session_id)
                    {
                        if hosted.input_pause_id.as_deref() == Some(&lease.pause_id) {
                            hosted.input_pause_id = None;
                        }
                        if hosted.input_pause_key.as_deref() == Some(&lease.lease_key) {
                            hosted.input_pause_key = None;
                        }
                        hosted.stop_failure = None;
                    }
                    guard
                        .session
                        .take_if(|hosted| hosted.acp_session_id == session_id);
                    Ok(())
                }
                Err(error) => Err(error),
            }
        }
        Err(error) => Err(error),
    };
    {
        let mut guard = state.lock().await;
        if let Some(hosted) = guard
            .session
            .as_mut()
            .filter(|hosted| hosted.acp_session_id == acp_session_id)
        {
            hosted.cancelling = false;
            if let Err(error) = &close_result {
                hosted.stop_failure = Some(error.to_string());
            }
        }
        guard.session_close_done = None;
    }
    let _ = close_done.send(true);
    match close_result {
        Ok(()) => {
            let _ = tx.send(jsonrpc::response(&id, &json!({})));
        }
        Err(error) => {
            let _ = tx.send(super::super::internal_error(&id, &error.to_string()));
        }
    }
}

/// Release the connection's hold after stdin closes (TS dispose): the
/// running prompt is cancelled (TS EOF abort → `cancel_prompt_admission`
/// with `cancelOwned`), the MCP servers go and the producer fences. A
/// client-owned session ends with the connection; a resident one stays
/// and is detached when the link drops.
pub(super) async fn teardown(
    link: &Arc<DaemonLink>,
    state: &Arc<Mutex<DaemonAcpState>>,
    binding: &DaemonBinding,
) {
    let hosted = state.lock().await.session.take();
    if let Some(hosted) = hosted.as_ref() {
        if let Some(turn) = hosted.turn.as_ref() {
            cancel_owned_admission(link, &binding.active_session_id, &turn.admission_id).await;
        }
        if let Some(pause_id) = hosted.input_pause_id.as_ref() {
            let _ = release_session_input_pause(link, &binding.active_session_id, pause_id).await;
        }
    }
    let closed_pause = {
        let mut guard = state.lock().await;
        guard.closed_input_pause_key = None;
        guard.closed_input_pause_id.take()
    };
    if let Some(pause_id) = closed_pause {
        let _ = release_session_input_pause(link, &binding.active_session_id, &pause_id).await;
    }
    let _ = clear_connection_servers(
        link,
        &binding.active_session_id,
        &binding.mcp_owner_id,
        state,
    )
    .await;
    // The owned worker stops before the config queue drains: a stalled
    // config operation holding the queue on a wire request fails fast.
    if binding.client_owned {
        let _ = link
            .request(DaemonCommand::CompleteOwnedSession {
                id: None,
                active_session_id: binding.active_session_id.clone(),
                rest: Map::default(),
            })
            .await;
    }
    if let Some(hosted) = hosted {
        let _ = hosted.config.queue.lock().await;
        hosted.producer.close().await;
    }
}
