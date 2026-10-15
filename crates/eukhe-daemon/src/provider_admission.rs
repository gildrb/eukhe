//! Provider admission across a daemon's workers. Every session runs in its
//! own worker process, so the supervisor owns the one
//! [`AdmissionRegistry`] of the daemon (`providerMaxInFlight` /
//! `providerMaxQueued`, omp2 `AdmissionController` semantics) and workers
//! ask it over their supervisor link ([`LinkAdmission`]). The chat
//! memory's compactor asks the same registry for background slots: in
//! this process when the supervisor owns the chat ([`SupervisorAdmission`]
//! is an admission authority itself), over the link when a worker does.
//!
//! A slot is bound to the connection that took it: the worker opens one
//! connection per model request, the supervisor answers once the slot is
//! taken (sending a `provider_admission_queued` frame first when the
//! request has to wait), and the slot stays taken until that connection
//! closes. A finished, failed, or aborted request closes it by dropping
//! its permit; a dead worker's sockets close with its process, so the
//! supervisor reclaims its slots (and its place in the queue) without any
//! liveness bookkeeping. A background slot an interactive request preempts
//! is free at once; its connection gets a `provider_admission_preempted`
//! frame, and the worker stops the request.
//!
//! The limits are the global settings' (`<agent-dir>/settings.json`),
//! re-read when that file changes (one `stat` per request): a new limit
//! applies to the next request without a restart.

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::{Arc, Mutex, PoisonError};
use std::time::{Duration, SystemTime};

use eukhe_core::admission::{
    Admission, AdmissionError, AdmissionLimits, AdmissionRegistry, AdmissionRejected,
    AdmissionRequest, ModelPermit, ProviderAdmission, ProviderPermit,
};
use eukhe_types::daemon::AdmissionPriority;
use serde_json::{json, Value};
use tokio_util::sync::CancellationToken;

use crate::protocol::{response_failure, response_success, DaemonResponse};
use crate::supervisor::{Outbound, Supervisor};
use crate::supervisor_link::SupervisorLink;

/// The frame a waiting acquire receives before its answer.
pub(crate) const QUEUED_FRAME: &str = "provider_admission_queued";

/// The frame a background slot's connection receives when an interactive
/// request preempted it (possibly before the acquire's answer).
pub(crate) const PREEMPTED_FRAME: &str = "provider_admission_preempted";

/// How long a worker waits for the supervisor connection itself (the slot
/// wait has no deadline).
const CONNECT_TIMEOUT: Duration = Duration::from_secs(10);

/// What the global settings file looked like at the last limits read.
#[derive(Clone, Copy, PartialEq, Eq)]
struct FileStamp {
    modified: Option<SystemTime>,
    len: u64,
}

fn stamp(path: &std::path::Path) -> Option<FileStamp> {
    let metadata = std::fs::metadata(path).ok()?;
    Some(FileStamp {
        modified: metadata.modified().ok(),
        len: metadata.len(),
    })
}

/// The global settings file as the registry's limits last read it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum LimitsSource {
    /// No read yet.
    Unread,
    /// Read when the file had this stamp (`None`: the file was absent).
    Read(Option<FileStamp>),
}

/// The slots one supervisor connection holds, and the token that ends its
/// waits when it closes.
struct ConnectionSlots {
    closed: CancellationToken,
    permits: Vec<ProviderPermit>,
}

/// The supervisor's admission state.
pub(crate) struct SupervisorAdmission {
    agent_dir: PathBuf,
    registry: AdmissionRegistry,
    /// The settings stamp the registry's limits were read at.
    loaded: Mutex<LimitsSource>,
    connections: Mutex<HashMap<String, ConnectionSlots>>,
}

impl SupervisorAdmission {
    pub(crate) fn new(agent_dir: PathBuf) -> Self {
        Self {
            agent_dir,
            registry: AdmissionRegistry::default(),
            loaded: Mutex::new(LimitsSource::Unread),
            connections: Mutex::new(HashMap::new()),
        }
    }

    /// Re-read the limits when the global settings file changed.
    fn refresh_limits(&self) {
        let path = self.agent_dir.join("settings.json");
        let current = stamp(&path);
        {
            let mut loaded = self.loaded.lock().unwrap_or_else(PoisonError::into_inner);
            if *loaded == LimitsSource::Read(current) {
                return;
            }
            *loaded = LimitsSource::Read(current);
        }
        let limits: AdmissionLimits =
            eukhe_core::settings::SettingsManager::create(&self.agent_dir, &self.agent_dir)
                .get_admission_limits();
        self.registry.apply_limits(&limits);
    }

    /// Register `connection_id` as holding admission state; `None` when the
    /// connection already closed (`open` reports whether it is live). The
    /// check runs under the table lock, and [`Self::close_connection`]
    /// runs after the connection left the live set, so a closed connection
    /// can never be registered after its cleanup.
    fn open(&self, connection_id: &str, open: impl FnOnce() -> bool) -> Option<CancellationToken> {
        let mut connections = self
            .connections
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        if let Some(slots) = connections.get(connection_id) {
            return Some(slots.closed.clone());
        }
        if !open() {
            return None;
        }
        let closed = CancellationToken::new();
        connections.insert(
            connection_id.to_owned(),
            ConnectionSlots {
                closed: closed.clone(),
                permits: Vec::new(),
            },
        );
        Some(closed)
    }

    /// Hand `permit` to its connection; `false` (the permit drops, the slot
    /// frees) when the connection closed meanwhile.
    fn keep(&self, connection_id: &str, permit: ProviderPermit) -> bool {
        let mut connections = self
            .connections
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        let Some(slots) = connections.get_mut(connection_id) else {
            return false;
        };
        slots.permits.push(permit);
        true
    }

    /// A connection closed: its slots free and its waits end.
    pub(crate) fn close_connection(&self, connection_id: &str) {
        let removed = self
            .connections
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .remove(connection_id);
        if let Some(slots) = removed {
            slots.closed.cancel();
            drop(slots.permits);
        }
    }

    /// The counters of `provider_id`.
    #[cfg(test)]
    pub(crate) fn snapshot(&self, provider_id: &str) -> eukhe_core::admission::AdmissionSnapshot {
        self.registry.controller(provider_id).snapshot()
    }
}

impl ProviderAdmission for SupervisorAdmission {
    /// The supervisor's own requests (its chat memory's compactor) take
    /// their slots in this process.
    #[tracing::instrument(level = "debug", skip_all, fields(provider = %request.provider_id))]
    async fn acquire(&self, request: AdmissionRequest) -> Result<ModelPermit, AdmissionError> {
        self.refresh_limits();
        self.registry.acquire(request).await
    }
}

/// The acquire command's inputs.
pub(crate) struct AcquireCommand<'a> {
    pub(crate) command_id: &'a str,
    pub(crate) type_name: &'a str,
    pub(crate) worker_token: &'a str,
    pub(crate) provider_id: &'a str,
    pub(crate) priority: AdmissionPriority,
    pub(crate) connection_id: &'a str,
}

impl Supervisor {
    /// `provider_admission_acquire`: take a slot of the provider in the
    /// request's class for the requesting connection, waiting in the
    /// provider's queue when it has to (the queued frame goes out first),
    /// or fail at once when the queue is full (`data.queueLimit` names the
    /// limit). A preempted background slot gets the preempted frame.
    pub(crate) async fn handle_provider_admission_acquire(
        self: &Arc<Self>,
        acquire: AcquireCommand<'_>,
        stream: &tokio::sync::mpsc::Sender<(Vec<Outbound>, bool)>,
    ) -> DaemonResponse {
        let AcquireCommand {
            command_id,
            type_name,
            worker_token,
            provider_id,
            priority,
            connection_id,
        } = acquire;
        let failure = |error: &str| response_failure(Some(command_id), type_name, error, None);
        if self.registry.find_by_token(worker_token).await.is_none() {
            return failure("Worker authentication failed");
        }
        let admission = &self.provider_admission;
        admission.refresh_limits();
        let Some(closed) = admission.open(connection_id, || {
            self.client_connections
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .contains_key(connection_id)
        }) else {
            return failure("the admission connection closed");
        };
        let permit = match admission.registry.controller(provider_id).admit(priority) {
            Err(rejected) => {
                return DaemonResponse {
                    data: Some(json!({ "queueLimit": rejected.queue_limit })),
                    ..failure(&rejected.to_string())
                };
            }
            Ok(Admission::Granted(permit)) => permit,
            Ok(Admission::Queued(waiting)) => {
                let frame = json!({
                    "type": QUEUED_FRAME,
                    "commandId": command_id,
                    "providerId": provider_id,
                });
                // A closed connection fails the send; the wait below ends
                // on the same close.
                let _ = stream.send((vec![Outbound::Line(frame)], false)).await;
                tokio::select! {
                    permit = waiting => permit,
                    () = closed.cancelled() => {
                        return failure("the admission connection closed");
                    }
                }
            }
        };
        let preempted = permit.preemption();
        if !admission.keep(connection_id, permit) {
            return failure("the admission connection closed");
        }
        match priority {
            AdmissionPriority::Interactive => {}
            AdmissionPriority::Background => {
                // The frame may beat the answer, which the worker allows
                // for; a closed connection holds no slot to preempt.
                let frame = json!({
                    "type": PREEMPTED_FRAME,
                    "commandId": command_id,
                    "providerId": provider_id,
                });
                let stream = stream.clone();
                tokio::spawn(async move {
                    tokio::select! {
                        () = preempted.cancelled() => {
                            // A connection closing meanwhile fails the
                            // send: its worker is gone with the slot.
                            let _ = stream.send((vec![Outbound::Line(frame)], false)).await;
                        }
                        () = closed.cancelled() => {}
                    }
                });
            }
        }
        response_success(
            Some(command_id),
            type_name,
            Some(json!({ "providerId": provider_id })),
        )
    }
}

/// A worker's admission authority: the supervisor, over a dedicated link
/// connection per request that stays open while the request holds its slot.
pub(crate) struct LinkAdmission {
    link: SupervisorLink,
    worker_token: String,
}

impl LinkAdmission {
    pub(crate) fn new(supervisor_socket_path: PathBuf, worker_token: String) -> Self {
        Self {
            link: SupervisorLink::new(supervisor_socket_path),
            worker_token,
        }
    }
}

/// Keeps a background slot's connection, watched for a preemption, until
/// its permit drops: the watch ends then, and the connection closes with
/// it.
struct Watching(tokio::task::JoinHandle<()>);

impl Drop for Watching {
    fn drop(&mut self) {
        self.0.abort();
    }
}

impl ProviderAdmission for LinkAdmission {
    #[tracing::instrument(
        level = "debug",
        skip_all,
        fields(provider = %request.provider_id, priority = ?request.priority)
    )]
    async fn acquire(&self, request: AdmissionRequest) -> Result<ModelPermit, AdmissionError> {
        let AdmissionRequest {
            provider_id,
            priority,
            on_queued,
        } = request;
        let mut on_queued = Some(on_queued);
        // Set by a preemption, which may come before the answer.
        let preempted = CancellationToken::new();
        let preempted_early = preempted.clone();
        let command = json!({
            "type": "provider_admission_acquire",
            "workerToken": self.worker_token,
            "providerId": provider_id,
            "priority": priority,
        });
        let held = self
            .link
            .hold(command, CONNECT_TIMEOUT, |frame| {
                let kind = frame.get("type").and_then(Value::as_str);
                if kind == Some(QUEUED_FRAME) {
                    if let Some(notice) = on_queued.take() {
                        notice.notify();
                    }
                } else if kind == Some(PREEMPTED_FRAME) {
                    preempted_early.cancel();
                }
            })
            .await;
        let (response, mut connection) = match held {
            Ok(held) => held,
            Err(error) => {
                return Err(AdmissionError::Unavailable {
                    provider_id,
                    reason: format!("{error:#}"),
                })
            }
        };
        if response.success {
            return Ok(match priority {
                AdmissionPriority::Interactive => ModelPermit::holding(connection),
                AdmissionPriority::Background => {
                    // A connection that ends takes the slot with it: a
                    // preemption as well.
                    let watched = preempted.clone();
                    let watch = tokio::spawn(async move {
                        if let Err(error) = connection.until_frame(PREEMPTED_FRAME).await {
                            tracing::warn!("the background admission connection failed: {error:#}");
                        }
                        watched.cancel();
                    });
                    ModelPermit::preemptible(Watching(watch), preempted)
                }
            });
        }
        let queue_limit = response
            .data
            .as_ref()
            .and_then(|data| data.get("queueLimit"))
            .and_then(Value::as_u64);
        match queue_limit {
            Some(queue_limit) => Err(AdmissionError::QueueFull(AdmissionRejected {
                provider_id,
                queue_limit: u32::try_from(queue_limit).unwrap_or(u32::MAX),
            })),
            None => Err(AdmissionError::Unavailable {
                provider_id,
                reason: response
                    .error
                    .unwrap_or_else(|| "request failed".to_owned()),
            }),
        }
    }
}

#[cfg(test)]
mod tests;
