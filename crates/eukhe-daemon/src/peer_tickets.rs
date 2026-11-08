//! Supervisor-issued direct-transport tickets (TS `daemon-supervisor.ts`
//! `get_direct_worker_transport` / `issuePeerTransport`).
//!
//! A client that wants to attach to a session asks the supervisor for a
//! ticket: the worker's socket path and filesystem identity, plus a
//! single-use grant (10s TTL). The grant is pushed into the worker's memory
//! (`worker_register_peer_transport`) before the ticket is returned, so by
//! the time the client presents it the worker can validate and burn it. The
//! supervisor is then out of the streaming path: the client attaches to the
//! session socket directly.
//!
//! TS refuses tickets for client-owned workers (`ownerClientId`); the Rust
//! supervisor has not ported that refusal yet (a disclosed divergence).

use std::sync::atomic::Ordering;
use std::sync::Arc;

use anyhow::{anyhow, Result};
use eukhe_types::daemon::{
    DaemonPeerTransportTicket, DaemonWorkerCommand, DaemonWorkerLifecycle, DaemonWorkerPeerGrant,
};

use crate::backpressure::RouteAdmission;
use crate::protocol::{response_failure, response_success, DaemonResponse};
use crate::registry::ResidentWorker;
use crate::supervisor::Supervisor;
use crate::util;
use serde_json::Map;

/// TS `PEER_TRANSPORT_GRANT_TTL_MS`: how long a minted grant stays valid.
pub(crate) const PEER_TRANSPORT_GRANT_TTL_MS: u64 = 10_000;
/// TS `issuePeerTransport` worker round-trip budget for the grant push.
const GRANT_REGISTRATION_TIMEOUT_MS: u64 = 3_000;

/// Who a minted grant admits on the target worker's socket.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PeerGrantPurpose {
    /// A session client attaching directly (TS `issuePeerTransport`).
    SessionClient,
    /// A peer worker delivering agent messages directly, bypassing the
    /// supervisor's route plane (thin-supervisor stage 3).
    Worker,
}

impl PeerGrantPurpose {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            PeerGrantPurpose::SessionClient => "session_client",
            PeerGrantPurpose::Worker => "worker",
        }
    }
}

impl Supervisor {
    /// `get_direct_worker_transport`: resolve the session, mint a grant,
    /// register it with the worker, and return the ticket.
    pub(crate) async fn handle_get_direct_worker_transport(
        self: &std::sync::Arc<Self>,
        command_id: &str,
        type_name: &str,
        selector: &str,
    ) -> DaemonResponse {
        match self.issue_direct_transport(selector).await {
            Ok(ticket) => response_success(
                Some(command_id),
                type_name,
                serde_json::to_value(&ticket).ok(),
            ),
            Err(error) => response_failure(Some(command_id), type_name, &error.to_string(), None),
        }
    }

    /// `get_worker_peer_transport` (a worker's supervisor-link request):
    /// mint a worker-to-worker peer ticket for direct delivery.
    pub(crate) async fn handle_get_worker_peer_transport(
        self: &std::sync::Arc<Self>,
        command_id: &str,
        type_name: &str,
        worker_token: &str,
        target_active_session_id: &str,
    ) -> DaemonResponse {
        match self
            .issue_worker_peer_transport(worker_token, target_active_session_id)
            .await
        {
            Ok(ticket) => response_success(
                Some(command_id),
                type_name,
                serde_json::to_value(&ticket).ok(),
            ),
            Err(error) => response_failure(Some(command_id), type_name, &error.to_string(), None),
        }
    }

    /// Port of `issuePeerTransport`. Errors carry the TS worker-state
    /// strings so clients see the same diagnosis.
    async fn issue_direct_transport(
        self: &std::sync::Arc<Self>,
        selector: &str,
    ) -> Result<DaemonPeerTransportTicket> {
        let resident = self.registry.resolve(selector).await?;
        self.mint_peer_transport_ticket(&resident, PeerGrantPurpose::SessionClient)
            .await
    }

    /// `get_worker_peer_transport`: a worker acting for its session asks
    /// for a single-use `worker`-purpose grant on a target worker's direct
    /// socket, so agent-message delivery bypasses the supervisor's route
    /// plane. The requester authenticates with its worker token (the TS
    /// `list_agent_peers` lookup), the target resolves through the roster
    /// with the same errors as the `send_message` arm, and the kin check
    /// ([`crate::kin_gate`]) admits only the requester's parent or child.
    async fn issue_worker_peer_transport(
        self: &std::sync::Arc<Self>,
        worker_token: &str,
        target_active_session_id: &str,
    ) -> Result<DaemonPeerTransportTicket> {
        let requester = self
            .registry
            .find_by_token(worker_token)
            .await
            .ok_or_else(|| anyhow!("Worker authentication failed"))?;
        let target = self.registry.resolve(target_active_session_id).await?;
        if Arc::ptr_eq(&requester, &target) {
            return Err(anyhow!("Agent messaging cannot target the sending session"));
        }
        self.admit_kin_resident(&requester, &target, target_active_session_id)
            .await
            .map_err(|refusal| anyhow!(refusal))?;
        self.mint_peer_transport_ticket(&target, PeerGrantPurpose::Worker)
            .await
    }

    /// The shared mint path (TS `issuePeerTransport` body): availability,
    /// exact process identity, grant push into worker memory, then the
    /// ticket. The supervisor is out of the streaming path once the ticket
    /// returns.
    async fn mint_peer_transport_ticket(
        self: &std::sync::Arc<Self>,
        resident: &std::sync::Arc<ResidentWorker>,
        purpose: PeerGrantPurpose,
    ) -> Result<DaemonPeerTransportTicket> {
        if self.is_stopping(resident) {
            return Err(anyhow!("Supervisor is shutting down"));
        }
        if !resident.peer_transport_capable.load(Ordering::SeqCst) {
            return Err(anyhow!(
                "Session worker does not support direct peer transport"
            ));
        }
        self.require_available_worker_client(resident).await?;
        let (worker_instance_id, socket_path, pid) = {
            let descriptor = resident.descriptor.lock().await;
            let worker_instance_id = descriptor
                .worker_instance_id
                .clone()
                .filter(|id| !id.is_empty())
                .ok_or_else(|| {
                    anyhow!("Direct transport requires an exact worker process identity")
                })?;
            (
                worker_instance_id,
                descriptor.socket_path.clone(),
                descriptor.pid,
            )
        };
        // The TS supervisor additionally pins the worker's process-start
        // id; this supervisor never populated it, so the live-pid check is
        // the process-identity guarantee here.
        if !matches!(crate::lease::is_process_alive(pid as u32), Ok(true)) {
            return Err(anyhow!(
                "Direct transport worker process identity is not current"
            ));
        }
        let socket_identity = eukhe_types::platform::socket_identity(std::path::Path::new(
            &socket_path,
        ))
        .ok_or_else(|| anyhow!("Direct transport requires an exact worker socket identity"))?;
        let grant = mint_grant(&worker_instance_id, &resident.worker_id, purpose);
        let registration = DaemonWorkerCommand::WorkerRegisterPeerTransport {
            id: None,
            grant: grant.clone(),
            rest: Map::default(),
        };
        let payload = serde_json::to_value(&registration)?;
        let response = self
            .route_command_typed(
                resident,
                "worker_register_peer_transport",
                payload,
                GRANT_REGISTRATION_TIMEOUT_MS,
                RouteAdmission::SupervisorInternal,
            )
            .await?;
        if !response.success {
            return Err(anyhow!(
                "{}",
                response
                    .error
                    .unwrap_or_else(|| "Peer transport grant is invalid".to_string())
            ));
        }
        Ok(DaemonPeerTransportTicket {
            purpose: grant.purpose.clone(),
            socket_path,
            socket_identity,
            worker_instance_id: grant.worker_instance_id.clone(),
            active_session_id: grant.active_session_id.clone(),
            grant_id: grant.grant_id.clone(),
            token: grant.token.clone(),
            expires_at: grant.expires_at.clone(),
        })
    }

    /// TS `requireAvailableWorkerClient`: the worker must be connected and
    /// ready, and not stopping. Ready includes the session-create boundary
    /// (a fresh create, or a replacement's create replay): a worker that
    /// registered but has not finished opening its session refuses every
    /// command, and a peer grant burns on first use, so the ticket waits
    /// for the boundary like the supervisor's routed commands do (the
    /// refusal sends the caller down that routed path).
    async fn require_available_worker_client(
        &self,
        resident: &std::sync::Arc<ResidentWorker>,
    ) -> Result<()> {
        let connected = resident.cmd_tx.lock().await.is_some();
        let lifecycle = resident.descriptor.lock().await.lifecycle;
        let available =
            connected && lifecycle == DaemonWorkerLifecycle::Ready && !self.is_stopping(resident);
        if !available {
            return Err(anyhow!(
                "Session worker is {}",
                effective_worker_state(connected, lifecycle, self.is_stopping(resident))
            ));
        }
        if !resident.route_state().session_ready {
            return Err(anyhow!("Session worker is starting"));
        }
        Ok(())
    }
}

/// TS `effectiveWorkerState` (shared with the create-reuse seam's typed
/// `worker is {state}` answers).
pub(crate) fn effective_worker_state(
    connected: bool,
    lifecycle: DaemonWorkerLifecycle,
    stopping: bool,
) -> &'static str {
    if stopping {
        "stopping"
    } else if lifecycle == DaemonWorkerLifecycle::Failed {
        "failed"
    } else if lifecycle == DaemonWorkerLifecycle::Ready && !connected {
        "recovering"
    } else {
        match lifecycle {
            DaemonWorkerLifecycle::Starting => "starting",
            DaemonWorkerLifecycle::Ready => "ready",
            DaemonWorkerLifecycle::Recovering => "recovering",
            DaemonWorkerLifecycle::Stopping => "stopping",
            DaemonWorkerLifecycle::Failed => "failed",
        }
    }
}

/// Mint one single-use grant for a worker instance and session, valid for
/// [`PEER_TRANSPORT_GRANT_TTL_MS`].
fn mint_grant(
    worker_instance_id: &str,
    active_session_id: &str,
    purpose: PeerGrantPurpose,
) -> DaemonWorkerPeerGrant {
    DaemonWorkerPeerGrant {
        grant_id: uuid::Uuid::new_v4().to_string(),
        token: uuid::Uuid::new_v4().simple().to_string(),
        expires_at: util::iso_from_unix_ms(util::now_ms() + PEER_TRANSPORT_GRANT_TTL_MS),
        purpose: purpose.as_str().to_string(),
        worker_instance_id: worker_instance_id.to_string(),
        active_session_id: active_session_id.to_string(),
        issuer_generation: format!("sup:{}", std::process::id()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn minted_grants_expire_in_ten_seconds_and_are_unique() {
        let first = mint_grant("inst-1", "abc123", PeerGrantPurpose::SessionClient);
        let second = mint_grant("inst-1", "abc123", PeerGrantPurpose::Worker);
        assert_ne!(first.grant_id, second.grant_id);
        assert_ne!(first.token, second.token);
        assert_eq!(first.purpose, "session_client");
        assert_eq!(second.purpose, "worker");
        assert_eq!(first.worker_instance_id, "inst-1");
        assert_eq!(first.active_session_id, "abc123");
        let expires = crate::util::iso_to_unix_ms(&first.expires_at).expect("iso expiry");
        let now = crate::util::now_ms();
        assert!(
            expires > now && expires <= now + PEER_TRANSPORT_GRANT_TTL_MS,
            "expiry inside the 10s TTL window: {expires} vs {now}"
        );
    }

    /// A supervisor over a fresh agent dir (kept alive by the returned
    /// dir) whose spawn ledger records `bbb222` and `ccc333` as children
    /// of `aaa111`; `ddd444` is another root. Each worker's session file
    /// is `<sessions>/<worker id>.jsonl`.
    async fn worker_ticket_supervisor() -> (tempfile::TempDir, Arc<Supervisor>) {
        let dir = tempfile::TempDir::new().unwrap();
        let agent_dir = dir.path().join("agent");
        let sessions_dir = agent_dir.join("sessions");
        std::fs::create_dir_all(&sessions_dir).unwrap();
        let supervisor = Arc::new(
            Supervisor::new(crate::supervisor::SupervisorOptions {
                socket_path: dir.path().join("s.sock"),
                agent_dir,
            })
            .unwrap(),
        );
        for id in ["aaa111", "bbb222", "ccc333", "ddd444"] {
            std::fs::write(
                sessions_dir.join(format!("{id}.jsonl")),
                format!("{{\"type\":\"session\",\"id\":\"{id}\"}}\n"),
            )
            .unwrap();
        }
        let ledger = supervisor.rlm_spawn_ledger_for(None).await.unwrap();
        for child in ["bbb222", "ccc333"] {
            ledger
                .append_spawn(&crate::rlm_ledger::RlmSpawnInput {
                    child_id: format!("sub-{child}"),
                    parent: sessions_dir
                        .join("aaa111.jsonl")
                        .to_string_lossy()
                        .into_owned(),
                    child: sessions_dir
                        .join(format!("{child}.jsonl"))
                        .to_string_lossy()
                        .into_owned(),
                    depth: 1,
                    name: child.to_string(),
                })
                .unwrap();
        }
        (dir, supervisor)
    }

    /// The worker-peer ticket arm authenticates by worker token, refuses
    /// self-targeting with the TS `send_message` string, and mints only
    /// for the requester's parent or children (the kin check).
    #[tokio::test]
    async fn worker_peer_ticket_auth_and_self_target() {
        use crate::registry::ResidentWorker;
        use eukhe_types::daemon::{
            DaemonWorkerDescriptor, DaemonWorkerLifecycle, DurableDaemonCreateCommand,
        };

        let (dir, supervisor) = worker_ticket_supervisor().await;
        let sessions_dir = dir.path().join("agent").join("sessions");
        let tokenized = |worker_id: &str, token: &str| {
            ResidentWorker::new(
                worker_id.to_string(),
                DaemonWorkerDescriptor {
                    version: 2,
                    worker_id: worker_id.to_string(),
                    pid: 1,
                    process_start_id: None,
                    socket_path: "/w.sock".to_string(),
                    recovery_journal_path: "/w.jsonl".to_string(),
                    orphan_process_journal_path: None,
                    supervisor_socket_path: "/s.sock".to_string(),
                    authentication_token: token.to_string(),
                    worker_instance_id: None,
                    root_active_session_id: worker_id.to_string(),
                    owner_client_id: None,
                    root_session_id: None,
                    session_file: Some(
                        sessions_dir
                            .join(format!("{worker_id}.jsonl"))
                            .to_string_lossy()
                            .into_owned(),
                    ),
                    session_dir: None,
                    created_at: "t".to_string(),
                    updated_at: "t".to_string(),
                    lifecycle: DaemonWorkerLifecycle::Ready,
                    create_command: DurableDaemonCreateCommand {
                        session_path: None,
                        no_session: None,
                        rest: Map::default(),
                    },
                    consecutive_failures: 0,
                    stop_requested_at: None,
                    archive_on_stop: None,
                    last_failure_at: None,
                    last_error: None,
                    rest: Map::default(),
                },
                std::path::PathBuf::from("/d.json"),
            )
        };
        // An unknown token answers with the TS auth error.
        let rejected = supervisor
            .handle_get_worker_peer_transport("t1", "get_worker_peer_transport", "nope", "aaa111")
            .await;
        assert!(!rejected.success, "{rejected:?}");
        assert_eq!(
            rejected.error.as_deref(),
            Some("Worker authentication failed")
        );
        // A known requester targeting itself answers with the TS
        // self-target string.
        supervisor
            .registry
            .insert(tokenized("aaa111", "tok-a"))
            .await;
        let self_target = supervisor
            .handle_get_worker_peer_transport("t2", "get_worker_peer_transport", "tok-a", "aaa111")
            .await;
        assert!(!self_target.success, "{self_target:?}");
        assert_eq!(
            self_target.error.as_deref(),
            Some("Agent messaging cannot target the sending session")
        );
        // A known requester with an unknown target answers with the TS
        // unknown-session error.
        let unknown = supervisor
            .handle_get_worker_peer_transport(
                "t3",
                "get_worker_peer_transport",
                "tok-a",
                "no-such-session",
            )
            .await;
        assert!(!unknown.success, "{unknown:?}");
        assert_eq!(
            unknown.error.as_deref(),
            Some("Unknown active session: no-such-session")
        );
        // A different resident without a live worker connection reaches
        // the mint path and answers with the not-connected state.
        let target = tokenized("bbb222", "tok-b");
        target
            .peer_transport_capable
            .store(true, std::sync::atomic::Ordering::SeqCst);
        supervisor.registry.insert(target).await;
        let reachable = supervisor
            .handle_get_worker_peer_transport("t4", "get_worker_peer_transport", "tok-a", "bbb222")
            .await;
        assert!(!reachable.success, "{reachable:?}");
        assert_eq!(
            reachable.error.as_deref(),
            Some("Session worker is recovering")
        );
        // A connected, registered worker whose session create has not
        // finished refuses the ticket: the grant would burn on a worker
        // that refuses every command until its session opens.
        let starting = tokenized("ccc333", "tok-c");
        starting
            .peer_transport_capable
            .store(true, std::sync::atomic::Ordering::SeqCst);
        let (cmd_tx, _cmd_rx) = tokio::sync::mpsc::channel(1);
        *starting.cmd_tx.lock().await = Some(cmd_tx);
        supervisor.registry.insert(starting).await;
        let starting = supervisor
            .handle_get_worker_peer_transport("t5", "get_worker_peer_transport", "tok-a", "ccc333")
            .await;
        assert!(!starting.success, "{starting:?}");
        assert_eq!(
            starting.error.as_deref(),
            Some("Session worker is starting")
        );
        // Another root is no kin of the requester: refused before any mint.
        supervisor
            .registry
            .insert(tokenized("ddd444", "tok-d"))
            .await;
        let stranger = supervisor
            .handle_get_worker_peer_transport("t6", "get_worker_peer_transport", "tok-a", "ddd444")
            .await;
        assert!(!stranger.success, "{stranger:?}");
        assert_eq!(
            stranger.error.as_deref(),
            Some("Cannot message ddd444: agents message only their parent and their own children")
        );
    }

    #[test]
    fn worker_states_match_ts_names() {
        use DaemonWorkerLifecycle as L;
        assert_eq!(effective_worker_state(true, L::Ready, true), "stopping");
        assert_eq!(effective_worker_state(true, L::Failed, false), "failed");
        assert_eq!(effective_worker_state(false, L::Ready, false), "recovering");
        assert_eq!(effective_worker_state(true, L::Ready, false), "ready");
        assert_eq!(effective_worker_state(true, L::Starting, false), "starting");
        assert_eq!(
            effective_worker_state(false, L::Recovering, false),
            "recovering"
        );
    }
}
