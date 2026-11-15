//! The prompt-admission surface (protocol breadth wave b9): the
//! supervisor's cancellation registry for `prompt` / `prompt_and_wait`
//! (TS `SupervisorPromptAdmission` + the `cancel_prompt_admission`
//! supervisor arm) and the worker-side admission bookkeeping the
//! forwarded cancellations read (TS daemon-mode `promptAdmissions`).
//!
//! The lifecycle: a prompt carrying `admissionId` registers at dispatch
//! (the TS parse-time registration; duplicates and empty ids answer the
//! TS parse errors), the route rewrites the admission id to a
//! supervisor-scoped one (`supervisor-admission:<uuid>`) and records the
//! worker, a successful prompt commits the admission (`owned`), and the
//! admission clears once the route settles. `cancel_prompt_admission`
//! answers the TS status ladder - `unknown` for an unregistered id,
//! `cancelled` for a waiting admission (aborting the in-flight prompt
//! with the TS `Prompt admission was cancelled.` failure), `owned` for a
//! committed one, and the worker's status for a cancellation racing a
//! live route.

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use serde_json::{json, Value};

use crate::backpressure::RouteAdmission;
use crate::protocol::{response_failure, response_line, response_success, DaemonResponse};
use crate::supervisor::{
    client_command_payload, client_route_admission, client_route_timeout, Supervisor,
    ROUTE_TIMEOUT_MS,
};
use crate::worker::Worker;

/// The admission status vocabulary (TS `SupervisorPromptAdmission.status`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AdmissionStatus {
    Waiting,
    Owned,
    Cancelled,
}

/// The TS admission key: session + public admission id.
fn prompt_admission_key(active_session_id: &str, admission_id: &str) -> String {
    format!("{active_session_id}\u{0}{admission_id}")
}

/// Why a prompt admission id was not registered (the TS parse-time
/// errors).
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub(crate) enum AdmissionRegisterError {
    #[error("admissionId must not be empty")]
    EmptyAdmissionId,
    #[error("admissionId must not contain NUL")]
    NulInAdmissionId,
    #[error("Prompt admission requires string activeSessionId and admissionId")]
    MissingSession,
    #[error("activeSessionId must not contain NUL")]
    NulInSessionId,
    #[error("Prompt admission id is already in use: {admission_id}")]
    InUse { admission_id: String },
}

/// One registered admission (the TS supervisor record).
struct PromptAdmission {
    worker_admission_id: String,
    status: AdmissionStatus,
    worker_id: Option<String>,
    worker_active_session_id: Option<String>,
}

/// The per-connection admission registry.
#[derive(Default)]
pub(crate) struct PromptAdmissionTable {
    admissions: Mutex<HashMap<String, PromptAdmission>>,
}

impl PromptAdmissionTable {
    /// The TS parse-time registration: a `prompt/prompt_and_wait` carrying
    /// an `admissionId` reserves it (duplicates answer the TS error).
    pub(crate) fn register(
        &self,
        active_session_id: &str,
        admission_id: &str,
    ) -> Result<(), AdmissionRegisterError> {
        // The TS checks in order: the empty admission id answers its own
        // error, then a missing session selector answers the generic one.
        if admission_id.is_empty() {
            return Err(AdmissionRegisterError::EmptyAdmissionId);
        }
        // The registry key joins its halves with NUL, so a NUL in either
        // half makes the separator ambiguous: an admission id carrying NUL
        // forges the stale-id cancel's NUL-prefixed suffix match, and a
        // session id carrying NUL forges a different half-split of the
        // same exact key. Registered halves stay NUL-free, so every key
        // carries exactly one NUL and both lookups are unambiguous.
        if admission_id.contains('\0') {
            return Err(AdmissionRegisterError::NulInAdmissionId);
        }
        if active_session_id.is_empty() {
            return Err(AdmissionRegisterError::MissingSession);
        }
        if active_session_id.contains('\0') {
            return Err(AdmissionRegisterError::NulInSessionId);
        }
        let key = prompt_admission_key(active_session_id, admission_id);
        let mut admissions = self
            .admissions
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if admissions.contains_key(&key) {
            return Err(AdmissionRegisterError::InUse {
                admission_id: admission_id.to_owned(),
            });
        }
        admissions.insert(
            key,
            PromptAdmission {
                worker_admission_id: format!("supervisor-admission:{}", uuid::Uuid::new_v4()),
                status: AdmissionStatus::Waiting,
                worker_id: None,
                worker_active_session_id: None,
            },
        );
        Ok(())
    }

    fn with<R>(&self, key: &str, f: impl FnOnce(&PromptAdmission) -> R) -> Option<R> {
        let admissions = self
            .admissions
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        admissions.get(key).map(f)
    }

    fn update<R>(&self, key: &str, f: impl FnOnce(&mut PromptAdmission) -> R) -> Option<R> {
        let mut admissions = self
            .admissions
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        admissions.get_mut(key).map(f)
    }

    /// Move one admission under a new key (the stale-active-id rebind: a
    /// cancellation addresses the admission by the session id the client
    /// currently holds). Returns whether the admission now lives at `to`:
    /// a missing source is a settled admission and an occupied
    /// destination stays intact (overwriting would lose a concurrent
    /// prompt's record), so on `false` the caller keeps addressing the
    /// entry where it is.
    fn rekey(&self, from: &str, to: &str) -> bool {
        if from == to {
            return true;
        }
        let mut admissions = self
            .admissions
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if admissions.contains_key(to) {
            return false;
        }
        match admissions.remove(from) {
            Some(admission) => {
                admissions.insert(to.to_string(), admission);
                true
            }
            None => false,
        }
    }

    /// The single admission whose key carries this admission id, when
    /// exactly one does (the stale-id cancel's last resort: after repeated
    /// replacements the session half of the key is unknowable, but a
    /// connection's admission id is its own idempotency key).
    fn sole_key_for_admission_id(&self, admission_id: &str) -> Option<String> {
        if admission_id.is_empty() {
            return None;
        }
        let suffix = format!("\u{0}{admission_id}");
        let admissions = self
            .admissions
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let mut keys = admissions.keys().filter(|key| key.ends_with(&suffix));
        let first = keys.next()?.clone();
        keys.next().is_none().then_some(first)
    }

    fn remove(&self, key: &str) {
        self.admissions
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .remove(key);
    }

    /// The disconnect cleanup (TS `cancelWaitingPromptAdmissionsForClient`):
    /// every waiting admission cancels so its in-flight prompt fails.
    pub(crate) fn cancel_all_waiting(&self) {
        let mut admissions = self
            .admissions
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        for admission in admissions.values_mut() {
            if admission.status == AdmissionStatus::Waiting {
                admission.status = AdmissionStatus::Cancelled;
            }
        }
    }
}

/// The admission id a prompt-family command carries (the registration
/// and route hooks match the same pair). The wire field is the TS
/// `admissionId`: it rides the command's lossless `rest` map (the
/// eukhe-types `PromptInput` predates the camelCase wire spelling).
pub(crate) fn input_admission_id(command: &eukhe_types::daemon::DaemonCommand) -> Option<&str> {
    use eukhe_types::daemon::DaemonCommand;
    match command {
        DaemonCommand::Prompt { input, rest, .. }
        | DaemonCommand::PromptAndWait { input, rest, .. } => input
            .admission_id
            .as_deref()
            .or_else(|| rest.get("admissionId").and_then(Value::as_str)),
        _ => None,
    }
}

impl Supervisor {
    /// Route one admitted prompt (the TS `forward()` closure in
    /// `routeClientCommand`): the cancellation checks around the worker
    /// round trip, the admission-id rewrite, and the owned commit.
    #[allow(clippy::too_many_arguments)]
    pub(crate) async fn route_prompt_with_admission(
        self: &Arc<Self>,
        connection: &Arc<crate::input_pause_lease::ClientConnectionState>,
        command: &eukhe_types::daemon::DaemonCommand,
        client_id: &str,
        attached: &Arc<crate::supervisor::subscribers::ClientSubscriptions>,
        command_id: String,
        type_name: String,
        active_session_id: &str,
    ) -> (Vec<Value>, bool) {
        let mut key = prompt_admission_key(
            active_session_id,
            input_admission_id(command).unwrap_or_default(),
        );
        let cancelled = connection
            .prompt_admissions
            .with(&key, |admission| {
                admission.status == AdmissionStatus::Cancelled
            })
            .unwrap_or(false);
        if cancelled {
            return Self::admission_failure(
                &command_id,
                &type_name,
                "Prompt admission was cancelled.",
            );
        }
        let Some(worker_admission_id) = connection
            .prompt_admissions
            .with(&key, |admission| admission.worker_admission_id.clone())
        else {
            // An admission that vanished before the route: the prompt
            // routes through the generic path (TS `admission undefined`).
            return self
                .route_client_command(command, client_id, attached, command_id, type_name, None)
                .await;
        };
        let timeout = client_route_timeout(command);
        // Resolve the session (the generic route's wake-aware resolution).
        let mut rebound_to: Option<String> = None;
        let resident = match self.registry.resolve(active_session_id).await {
            Ok(resident) => resident,
            Err(_) => {
                // The stale-active-id rebind (the generic route's
                // seam): the admission id stays the client's
                // idempotency key across the rebind - the prompt
                // failed before it reached any worker, so routing it
                // once to the session's current resident delivers
                // it exactly once.
                if let Some(resident) = self.binding_target(active_session_id).await {
                    let current = self
                        .rebind_connection(active_session_id, &resident, attached)
                        .await;
                    // The admission follows the rebind: a
                    // cancellation by the advertised current id
                    // must find the in-flight admission.
                    let rekeyed = prompt_admission_key(
                        &current,
                        input_admission_id(command).unwrap_or_default(),
                    );
                    if connection.prompt_admissions.rekey(&key, &rekeyed) {
                        key = rekeyed;
                    }
                    rebound_to = Some(current);
                    resident
                } else {
                    let message = format!("Unknown active session: {active_session_id}");
                    return Self::admission_failure(&command_id, &type_name, &message);
                }
            }
        };
        // A cancellation that landed during the resolution fails the
        // prompt before it reaches the worker.
        let cancelled = connection
            .prompt_admissions
            .with(&key, |admission| {
                admission.status == AdmissionStatus::Cancelled
            })
            .unwrap_or(false);
        if cancelled {
            return Self::admission_failure(
                &command_id,
                &type_name,
                "Prompt admission was cancelled.",
            );
        }
        connection.prompt_admissions.update(&key, |admission| {
            admission.worker_id = Some(resident.worker_id.clone());
            admission.worker_active_session_id = Some(resident.worker_id.clone());
        });
        let (command_type, mut payload) = match client_command_payload(command, client_id) {
            Ok(payload) => payload,
            Err(error) => {
                return Self::admission_failure(&command_id, &type_name, &error.to_string())
            }
        };
        payload["admissionId"] = json!(worker_admission_id);
        // A rebind retargets the routed frame to the session's current id.
        if let Some(current) = &rebound_to {
            payload["activeSessionId"] = json!(current);
        }
        // The replacement-aware route: a prompt aimed at a worker being
        // replaced waits out the replay inside its own budget instead of
        // bouncing off the worker's require-created gate, and a send that
        // provably never left the supervisor retries on the next
        // connection - the admission id stays the idempotency key, so the
        // prompt still lands exactly once (the generic client route's
        // contract). A `prompt_and_wait` is a watch: no in-flight permit,
        // and it ends with its requester.
        let admission = client_route_admission(command);
        let routed =
            self.route_command_ready_typed(&resident, command_type, payload, timeout, admission);
        let Some(response) = attached.unless_requester_gone(routed, admission).await else {
            connection.prompt_admissions.remove(&key);
            return (Vec::new(), false);
        };
        let mut response = match response {
            Ok(response) => response,
            Err(error) => {
                // The route failed: the admission clears with it (TS
                // deletes in the finally).
                connection.prompt_admissions.remove(&key);
                return Self::admission_failure(&command_id, &type_name, &error.to_string());
            }
        };
        if response.success {
            connection
                .prompt_admissions
                .update(&key, |admission| admission.status = AdmissionStatus::Owned);
        }
        // The prompt settled: the admission clears (TS `finally`);
        // a cancel that raced it already recorded its own outcome.
        connection.prompt_admissions.remove(&key);
        response.id = Some(command_id);
        (vec![response_line(&response)], false)
    }

    /// `cancel_prompt_admission` (the TS supervisor arm): the status
    /// ladder, with the worker forward for a cancellation racing a live
    /// prompt route.
    pub(crate) async fn handle_cancel_prompt_admission(
        self: &Arc<Self>,
        connection: &Arc<crate::input_pause_lease::ClientConnectionState>,
        command: &eukhe_types::daemon::DaemonCommand,
        command_id: &str,
        type_name: &str,
    ) -> (Vec<Value>, bool) {
        let eukhe_types::daemon::DaemonCommand::CancelPromptAdmission {
            active_session_id,
            admission_id,
            cancel_owned,
            ..
        } = command
        else {
            return Self::admission_failure(command_id, type_name, "invalid command");
        };
        let mut key = prompt_admission_key(active_session_id, admission_id);
        if connection.prompt_admissions.with(&key, |_| ()).is_none() {
            // The stale-active-id rebind: a rebound prompt's admission
            // moved under the session's current resident id (the same
            // source the rebind seam re-keyed with), so a cancel still
            // addressed by the superseded id follows it there. A resident
            // replaced again mid-flight leaves no resolvable session half;
            // the admission id alone settles it when it is unambiguous.
            let mut rebound = None;
            if let Some(resident) = self.binding_target(active_session_id).await {
                let candidate = prompt_admission_key(&resident.worker_id, admission_id);
                if connection
                    .prompt_admissions
                    .with(&candidate, |_| ())
                    .is_some()
                {
                    rebound = Some(candidate);
                }
            }
            if rebound.is_none() {
                rebound = connection
                    .prompt_admissions
                    .sole_key_for_admission_id(admission_id);
            }
            if let Some(rebound) = rebound {
                key = rebound;
            }
        }
        // A waiting admission with no worker yet cancels outright (the TS
        // `handleLine` pre-check: the prompt route fails with the TS
        // cancellation error at its next check).
        connection.prompt_admissions.update(&key, |admission| {
            if admission.status == AdmissionStatus::Waiting && admission.worker_id.is_none() {
                admission.status = AdmissionStatus::Cancelled;
            }
        });
        let Some(status) = connection
            .prompt_admissions
            .with(&key, |admission| admission.status)
        else {
            return Self::admission_status(command_id, type_name, "unknown");
        };
        match status {
            AdmissionStatus::Cancelled => {
                Self::admission_status(command_id, type_name, "cancelled")
            }
            AdmissionStatus::Owned => Self::admission_status(command_id, type_name, "owned"),
            AdmissionStatus::Waiting => {
                // The route is in flight: forward the cancellation to the
                // worker with the rewritten ids and map its status.
                let fields = connection.prompt_admissions.with(&key, |admission| {
                    (
                        admission.worker_admission_id.clone(),
                        admission.worker_active_session_id.clone(),
                        admission.worker_id.clone(),
                    )
                });
                let Some((worker_admission_id, worker_active, worker_id)) = fields else {
                    return Self::admission_status(command_id, type_name, "cancelled");
                };
                let Some(worker_active) = worker_active else {
                    return Self::admission_status(command_id, type_name, "cancelled");
                };
                let Some(worker_id) = worker_id else {
                    return Self::admission_status(command_id, type_name, "cancelled");
                };
                let Some(resident) = self.registry.get(&worker_id).await else {
                    return Self::admission_status(command_id, type_name, "cancelled");
                };
                let mut payload = json!({
                    "activeSessionId": worker_active,
                    "admissionId": worker_admission_id,
                });
                if *cancel_owned == Some(true) {
                    payload["cancelOwned"] = json!(true);
                }
                let mut response = match self
                    .route_command_typed(
                        &resident,
                        "cancel_prompt_admission",
                        payload,
                        ROUTE_TIMEOUT_MS,
                        RouteAdmission::SupervisorInternal,
                    )
                    .await
                {
                    Ok(response) => response,
                    Err(error) => {
                        return Self::admission_failure(command_id, type_name, &error.to_string())
                    }
                };
                // The mapped status updates the supervisor record (TS
                // re-reads and downgrades only through waiting).
                let status = response
                    .data
                    .as_ref()
                    .and_then(|data| data.get("status"))
                    .and_then(Value::as_str)
                    .unwrap_or("unknown")
                    .to_string();
                connection
                    .prompt_admissions
                    .update(&key, |admission| match status.as_str() {
                        "owned" => admission.status = AdmissionStatus::Owned,
                        "cancelled" => admission.status = AdmissionStatus::Cancelled,
                        _ => {
                            if admission.status != AdmissionStatus::Cancelled {
                                admission.status = AdmissionStatus::Waiting;
                            }
                        }
                    });
                response.id = Some(command_id.to_string());
                (vec![response_line(&response)], false)
            }
        }
    }

    fn admission_failure(command_id: &str, type_name: &str, error: &str) -> (Vec<Value>, bool) {
        (
            vec![response_line(&response_failure(
                Some(command_id),
                type_name,
                error,
                None,
            ))],
            false,
        )
    }

    fn admission_status(command_id: &str, type_name: &str, status: &str) -> (Vec<Value>, bool) {
        (
            vec![response_line(&response_success(
                Some(command_id),
                type_name,
                Some(json!({ "status": status })),
            ))],
            false,
        )
    }
}

// ---------------------------------------------------------------------------
// Worker side
// ---------------------------------------------------------------------------

/// One prompt admission on the worker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum WorkerAdmission {
    /// Registered; the prompt has not committed.
    Waiting,
    /// A cancel came first: the prompt never runs.
    Cancelled,
    /// Committed: the prompt is on its way to its submission.
    Committing,
    /// Committed and queued as this durable submission (its request id is
    /// the admission id).
    Admitted(eukhe_durable::types::SubmissionId),
    /// Committed as no submission (a session command or a held input).
    Started,
}

/// The worker's admission registry: admission id -> admission (the TS
/// daemon-mode `promptAdmissions` map). `changed` wakes the cancels that
/// wait for a committing admission's outcome.
#[derive(Default, Clone)]
pub(crate) struct WorkerAdmissions {
    admissions: Arc<Mutex<HashMap<String, WorkerAdmission>>>,
    changed: Arc<tokio::sync::Notify>,
}

impl WorkerAdmissions {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    fn register(&self, admission_id: &str) {
        self.admissions
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .insert(admission_id.to_string(), WorkerAdmission::Waiting);
    }

    /// Admission at prompt enqueue: a waiting id commits, and the prompt
    /// carries the commit to its submission. A cancelled or removed id
    /// refuses delivery, including cancellation before enqueue.
    pub(crate) fn commit(
        &self,
        admission_id: &str,
    ) -> Result<CommittedAdmission, AdmissionCancelled> {
        let mut admissions = self
            .admissions
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        match admissions.get_mut(admission_id) {
            Some(admission @ WorkerAdmission::Waiting) => {
                *admission = WorkerAdmission::Committing;
                Ok(self.committed(admission_id))
            }
            Some(
                WorkerAdmission::Committing
                | WorkerAdmission::Admitted(_)
                | WorkerAdmission::Started,
            ) => Ok(self.committed(admission_id)),
            Some(WorkerAdmission::Cancelled) | None => Err(AdmissionCancelled),
        }
    }

    fn committed(&self, admission_id: &str) -> CommittedAdmission {
        CommittedAdmission {
            admissions: self.clone(),
            admission_id: admission_id.to_string(),
        }
    }

    /// Move a committing admission on to `next`; an admission in any other
    /// state stays as it is.
    fn settle_commit(&self, admission_id: &str, next: Option<WorkerAdmission>) {
        let mut admissions = self
            .admissions
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if admissions.get(admission_id) == Some(&WorkerAdmission::Committing) {
            match next {
                Some(next) => admissions.insert(admission_id.to_string(), next),
                None => admissions.remove(admission_id),
            };
        }
        self.changed.notify_waiters();
    }

    /// The prompt settled: its admission clears (TS `clearAdmission`).
    pub(crate) fn clear(&self, admission_id: &str) {
        self.admissions
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .remove(admission_id);
        self.changed.notify_waiters();
    }

    /// Cancel one admission: a waiting one marks cancelled (its queued
    /// prompt never runs), any other admission reports as-is, an unknown id
    /// answers `None` (the wire `unknown`).
    fn cancel(&self, admission_id: &str) -> Option<WorkerAdmission> {
        let mut admissions = self
            .admissions
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let admission = admissions.get_mut(admission_id)?;
        if *admission == WorkerAdmission::Waiting {
            *admission = WorkerAdmission::Cancelled;
        }
        Some(*admission)
    }

    /// [`Self::cancel`] for a `cancelOwned` cancel: a committing admission
    /// has no submission to withdraw yet, so the cancel waits until the
    /// prompt has queued it (or ended without one).
    async fn cancel_owned(&self, admission_id: &str) -> Option<WorkerAdmission> {
        loop {
            // Registered before the read, so a change between the read and
            // the wait is not missed.
            let changed = self.changed.notified();
            match self.cancel(admission_id) {
                Some(WorkerAdmission::Committing) => changed.await,
                admission => return admission,
            }
        }
    }
}

/// A prompt's admission was cancelled before it committed: the prompt
/// never runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[error("Prompt admission was cancelled.")]
pub(crate) struct AdmissionCancelled;

/// A committed admission on its way to its submission. Dropped before it
/// records one (the prompt failed first), it clears the admission, so a
/// cancel waiting on it answers.
pub(crate) struct CommittedAdmission {
    admissions: WorkerAdmissions,
    admission_id: String,
}

impl CommittedAdmission {
    /// The prompt queued as durable submission `submission`.
    pub(crate) fn admitted(self, submission: eukhe_durable::types::SubmissionId) {
        self.admissions.settle_commit(
            &self.admission_id,
            Some(WorkerAdmission::Admitted(submission)),
        );
    }

    /// The prompt runs as no submission (a session command or a held input).
    pub(crate) fn started(self) {
        self.admissions
            .settle_commit(&self.admission_id, Some(WorkerAdmission::Started));
    }
}

impl Drop for CommittedAdmission {
    fn drop(&mut self) {
        self.admissions.settle_commit(&self.admission_id, None);
    }
}

impl Worker {
    /// Register a prompt's admission (the worker-side bookkeeping the
    /// forwarded cancellations read).
    pub(crate) fn register_prompt_admission(&self, admission_id: &str) {
        self.prompt_admissions.register(admission_id);
    }

    /// `cancel_prompt_admission` (the worker arm the supervisor forwards
    /// to): the TS status ladder over the worker's registry. An owned
    /// admission with `cancelOwned` withdraws its queued submission, or
    /// aborts the run that placed it; one still on its way to its
    /// submission is waited for first, so the `owned` answer never leaves
    /// a committed prompt running.
    pub(crate) async fn handle_cancel_prompt_admission(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "cancel_prompt_admission";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let admission_id = payload
            .get("admissionId")
            .and_then(Value::as_str)
            .unwrap_or_default();
        let cancel_owned = payload.get("cancelOwned").and_then(Value::as_bool) == Some(true);
        let admission = if cancel_owned {
            self.prompt_admissions.cancel_owned(admission_id).await
        } else {
            self.prompt_admissions.cancel(admission_id)
        };
        if admission == Some(WorkerAdmission::Cancelled) {
            self.prompt_admissions.clear(admission_id);
        }
        if let (true, Some(WorkerAdmission::Admitted(submission))) = (cancel_owned, admission) {
            let cx = eukhe_chord::context::BACKGROUND_CONTEXT.clone();
            let main = hosted.main();
            match hosted
                .harness()
                .abort_submission(
                    submission,
                    main.as_ref()
                        .ok()
                        .map(eukhe_durable::harness::Conversation::id),
                    &cx,
                )
                .await
            {
                Ok(eukhe_durable::harness::AbortSubmissionResult::AlreadyPlaced) => {
                    if let Ok(main) = main {
                        let _ = main
                            .abort(
                                eukhe_durable::harness::types::ConversationAbortOptions::default(),
                                &cx,
                            )
                            .await;
                    }
                }
                Ok(_) => self.prompt_admissions.clear(admission_id),
                Err(error) => {
                    return response_failure(None, COMMAND, &error.to_string(), None);
                }
            }
        }
        let status = match admission {
            None => "unknown",
            Some(
                WorkerAdmission::Committing
                | WorkerAdmission::Admitted(_)
                | WorkerAdmission::Started,
            ) => "owned",
            Some(WorkerAdmission::Waiting | WorkerAdmission::Cancelled) => "cancelled",
        };
        response_success(None, COMMAND, Some(json!({ "status": status })))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rekey_moves_a_live_admission_under_the_new_session_id() {
        let table = PromptAdmissionTable::default();
        table
            .register("stale-id", "adm-1")
            .expect("register admission");
        let old_key = prompt_admission_key("stale-id", "adm-1");
        let new_key = prompt_admission_key("current-id", "adm-1");
        assert!(table.rekey(&old_key, &new_key));
        assert!(table.with(&old_key, |_| ()).is_none());
        assert!(table.with(&new_key, |_| ()).is_some());
        // A settled (already-removed) admission stays absent.
        table.remove(&new_key);
        assert!(!table.rekey(&new_key, &old_key));
        assert!(table.with(&old_key, |_| ()).is_none());
    }

    #[test]
    fn rekey_never_overwrites_an_occupied_destination() {
        let table = PromptAdmissionTable::default();
        table.register("stale-id", "adm-1").expect("register");
        table.register("current-id", "adm-1").expect("register");
        let from = prompt_admission_key("stale-id", "adm-1");
        let to = prompt_admission_key("current-id", "adm-1");
        // The refusal is reported: the caller keeps addressing the
        // admission under `from` (the route's cancel/remove stay keyed
        // there instead of hitting the concurrent prompt's record).
        assert!(!table.rekey(&from, &to));
        assert!(table.with(&from, |_| ()).is_some());
        assert!(table.with(&to, |_| ()).is_some());
    }

    #[test]
    fn sole_admission_id_match_resolves_but_ambiguity_stays_unknown() {
        let table = PromptAdmissionTable::default();
        table.register("sess-a", "adm-1").expect("register");
        assert_eq!(
            table.sole_key_for_admission_id("adm-1"),
            Some(prompt_admission_key("sess-a", "adm-1"))
        );
        // The same admission id under a second session is ambiguous: no
        // last-resort match.
        table.register("sess-b", "adm-1").expect("register");
        assert_eq!(table.sole_key_for_admission_id("adm-1"), None);
        assert_eq!(table.sole_key_for_admission_id(""), None);
    }

    #[test]
    fn a_nul_in_either_key_half_is_refused_at_registration() {
        let table = PromptAdmissionTable::default();
        // A NUL in the admission id forges the stale-id cancel's
        // NUL-prefixed suffix match ("prefix<NUL>target" ends with
        // "<NUL>target").
        assert_eq!(
            table
                .register("sess-a", "prefix\0target")
                .map_err(|error| error.to_string()),
            Err("admissionId must not contain NUL".to_string())
        );
        // A NUL in the session id forges a different half-split of the
        // same exact key (session "s<NUL>t" + admission "u" builds the
        // key that session "s" + admission "t<NUL>u" addresses).
        assert_eq!(
            table
                .register("s\0t", "u")
                .map_err(|error| error.to_string()),
            Err("activeSessionId must not contain NUL".to_string())
        );
        // Both refusals left nothing registered, so neither forged key
        // exists under any half-split.
        assert!(table.sole_key_for_admission_id("target").is_none());
        assert!(table.sole_key_for_admission_id("t\0u").is_none());
    }

    /// A `cancelOwned` cancel of a committing admission answers what the
    /// prompt became: started as no submission, or cleared when the prompt
    /// failed before queueing (its commit dropped). A plain cancel before
    /// the commit refuses the prompt.
    #[tokio::test]
    async fn a_cancel_owned_answers_what_a_committing_admission_became() {
        let admissions = WorkerAdmissions::new();
        admissions.register("failed");
        let committed = admissions
            .commit("failed")
            .expect("a waiting admission commits");
        let cancel = admissions.cancel_owned("failed");
        tokio::pin!(cancel);
        assert!(futures::poll!(&mut cancel).is_pending());
        drop(committed);
        assert_eq!(cancel.await, None);

        admissions.register("command");
        let committed = admissions
            .commit("command")
            .expect("a waiting admission commits");
        let cancel = admissions.cancel_owned("command");
        tokio::pin!(cancel);
        assert!(futures::poll!(&mut cancel).is_pending());
        committed.started();
        assert_eq!(cancel.await, Some(WorkerAdmission::Started));

        admissions.register("early");
        assert_eq!(admissions.cancel("early"), Some(WorkerAdmission::Cancelled));
        assert_eq!(admissions.commit("early").err(), Some(AdmissionCancelled));
    }

    /// A `cancelOwned` that lands after the worker committed a prompt's
    /// admission but before it recorded the prompt's submission stops the
    /// prompt: the scripted answer never lands. A quiesced run gate holds
    /// the prompt inside that window (it commits, then waits at the gate
    /// to queue its input), and the prompt's turn holds at a faux gate
    /// released only once the cancel has answered.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn a_cancel_owned_inside_the_commit_window_stops_the_prompt() {
        let gates = tempfile::tempdir().expect("gate dir");
        let gate = gates.path().join("hold.sock");
        let listener = tokio::net::UnixListener::bind(&gate).expect("bind the hold gate");
        let (answered, cancel_answered) = tokio::sync::oneshot::channel::<()>();
        let held = tokio::spawn(async move {
            let (connection, _) = listener.accept().await.expect("the turn reaches the gate");
            let _ = cancel_answered.await;
            drop(connection);
        });
        let (_dir, worker) = crate::durable_test_support::created_worker_with(
            "cancel-window",
            json!([{ "text": "ran", "holdUntilReleased": gate }]),
            json!({ "noSession": true }),
        )
        .await;
        assert!(worker.dispatch("worker_quiesce", &json!({})).await.success);

        let prompt_payload = json!({ "message": "withdraw me", "admissionId": "adm-1" });
        let prompt = worker.dispatch("prompt_and_wait", &prompt_payload);
        tokio::pin!(prompt);
        // Drive the prompt until it commits its admission (it may wait on
        // the session's own writes first); the closed gate then holds it
        // before it queues, and it is not polled again until the cancel
        // has run once.
        while worker
            .prompt_admissions
            .admissions
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .get("adm-1")
            != Some(&WorkerAdmission::Committing)
        {
            assert!(futures::poll!(&mut prompt).is_pending());
            tokio::task::yield_now().await;
        }

        let cancel_payload = json!({ "admissionId": "adm-1", "cancelOwned": true });
        let cancel = async {
            let response = worker
                .dispatch("cancel_prompt_admission", &cancel_payload)
                .await;
            let _ = answered.send(());
            response
        };
        tokio::pin!(cancel);
        let early = futures::poll!(&mut cancel);
        assert!(worker.dispatch("worker_release", &json!({})).await.success);
        let (cancelled, prompted) = match early {
            std::task::Poll::Ready(cancelled) => (cancelled, prompt.await),
            std::task::Poll::Pending => tokio::join!(cancel, prompt),
        };
        held.abort();

        assert_eq!(
            cancelled.data,
            Some(json!({ "status": "owned" })),
            "{cancelled:?}"
        );
        let answers = crate::durable_test_support::worker_rows(&worker, "pi.assistant").await;
        assert!(
            !answers
                .iter()
                .any(|row| row.to_string().contains("\"ran\"")),
            "the cancelled prompt ran: {answers:?}"
        );
        assert!(
            !prompted.success,
            "the cancelled prompt answered: {prompted:?}"
        );
    }
}
