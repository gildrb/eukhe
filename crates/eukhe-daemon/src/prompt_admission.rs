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
//! live route. A `cancelOwned` cancel answers only what it did (see
//! [`Worker::handle_cancel_prompt_admission`]): it never answers `owned`
//! unless it withdrew the prompt or aborted its run, and it never waits
//! behind a closed run gate.

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
                .route_client_command(command, client_id, attached, &command_id, &type_name, None)
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
    /// Committed; the prompt has not started on what it becomes (it may
    /// wait at a closed run gate). A `cancelOwned` cancel withdraws it here.
    Committed,
    /// Starting as its submission or its held input; a `cancelOwned` cancel
    /// waits for which.
    Starting,
    /// Queued as this durable submission (its request id is the admission
    /// id).
    Admitted(eukhe_durable::types::SubmissionId),
    /// Parked in the held inputs by an input-pause lease (its request id is
    /// the admission id).
    Held,
    /// Running as a typed session command or a `/budget` toggle.
    Command,
}

/// What a `cancelOwned` cancel found: nothing, a prompt it stopped before
/// it started, or a started one it may still withdraw.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OwnedCancel {
    Unknown,
    Cancelled,
    Admitted(eukhe_durable::types::SubmissionId),
    Held,
    Command,
}

/// The worker's admission registry: admission id -> admission (the TS
/// daemon-mode `promptAdmissions` map). `changed` wakes the cancels that
/// wait for a starting admission's outcome.
#[derive(Default, Clone)]
pub(crate) struct WorkerAdmissions {
    admissions: Arc<Mutex<HashMap<String, WorkerAdmission>>>,
    changed: Arc<tokio::sync::Notify>,
}

impl WorkerAdmissions {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, HashMap<String, WorkerAdmission>> {
        self.admissions
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    fn register(&self, admission_id: &str) {
        self.lock()
            .insert(admission_id.to_string(), WorkerAdmission::Waiting);
    }

    /// Admission at prompt enqueue: a waiting id commits, and the prompt
    /// carries the commit until it starts. A cancelled, removed or already
    /// committed id refuses delivery, including cancellation before enqueue.
    pub(crate) fn commit(
        &self,
        admission_id: &str,
    ) -> Result<CommittedAdmission, AdmissionCancelled> {
        let mut admissions = self.lock();
        match admissions.get_mut(admission_id) {
            Some(admission @ WorkerAdmission::Waiting) => {
                *admission = WorkerAdmission::Committed;
                Ok(CommittedAdmission {
                    admissions: self.clone(),
                    admission_id: admission_id.to_string(),
                })
            }
            _ => Err(AdmissionCancelled),
        }
    }

    /// Move the admission from `from` to `next` (`None` removes it); an
    /// admission in any other state stays as it is. Answers whether it
    /// moved.
    fn advance(
        &self,
        admission_id: &str,
        from: &[WorkerAdmission],
        next: Option<WorkerAdmission>,
    ) -> bool {
        let moved = {
            let mut admissions = self.lock();
            let moved = admissions
                .get(admission_id)
                .is_some_and(|admission| from.contains(admission));
            if moved {
                match next {
                    Some(next) => admissions.insert(admission_id.to_string(), next),
                    None => admissions.remove(admission_id),
                };
            }
            moved
        };
        self.changed.notify_waiters();
        moved
    }

    /// The prompt settled: its admission clears (TS `clearAdmission`).
    pub(crate) fn clear(&self, admission_id: &str) {
        self.lock().remove(admission_id);
        self.changed.notify_waiters();
    }

    /// Cancel one admission: a waiting one marks cancelled (its prompt
    /// never runs), any other admission reports as-is, an unknown id
    /// answers `None` (the wire `unknown`).
    fn cancel(&self, admission_id: &str) -> Option<WorkerAdmission> {
        let mut admissions = self.lock();
        let admission = admissions.get_mut(admission_id)?;
        if *admission == WorkerAdmission::Waiting {
            *admission = WorkerAdmission::Cancelled;
        }
        Some(*admission)
    }

    /// [`Self::cancel`] for a `cancelOwned` cancel: a committed admission
    /// that has not started is withdrawn too (the prompt finds it cancelled
    /// when it starts, so a closed run gate does not delay the answer), and
    /// a starting one is waited for until it is queued, held or gone.
    async fn cancel_owned(&self, admission_id: &str) -> OwnedCancel {
        loop {
            // Registered before the read, so a change between the read and
            // the wait is not missed.
            let changed = self.changed.notified();
            {
                let mut admissions = self.lock();
                let Some(admission) = admissions.get_mut(admission_id) else {
                    return OwnedCancel::Unknown;
                };
                match *admission {
                    WorkerAdmission::Waiting
                    | WorkerAdmission::Committed
                    | WorkerAdmission::Cancelled => {
                        *admission = WorkerAdmission::Cancelled;
                        return OwnedCancel::Cancelled;
                    }
                    WorkerAdmission::Admitted(submission) => {
                        return OwnedCancel::Admitted(submission)
                    }
                    WorkerAdmission::Held => return OwnedCancel::Held,
                    WorkerAdmission::Command => return OwnedCancel::Command,
                    WorkerAdmission::Starting => {}
                }
            }
            changed.await;
        }
    }
}

/// A prompt's admission was cancelled before the prompt started: the
/// prompt never runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[error("Prompt admission was cancelled.")]
pub(crate) struct AdmissionCancelled;

/// A committed admission the prompt carries until it starts. Dropped
/// before the prompt is queued or held (it failed first), or once its
/// command ended, it clears the admission, so a cancel waiting on it
/// answers.
pub(crate) struct CommittedAdmission {
    admissions: WorkerAdmissions,
    admission_id: String,
}

impl CommittedAdmission {
    /// The prompt starts on what it becomes (past the run gate, or into
    /// the held inputs); refused when a `cancelOwned` cancel withdrew it
    /// first, and then it must not run.
    pub(crate) fn start(&mut self) -> Result<(), AdmissionCancelled> {
        self.advance_from_committed(WorkerAdmission::Starting)
    }

    /// The prompt starts as a typed session command or a `/budget` toggle;
    /// refused when a `cancelOwned` cancel withdrew it first. Keep the
    /// admission until the command ends.
    pub(crate) fn command(&mut self) -> Result<(), AdmissionCancelled> {
        self.advance_from_committed(WorkerAdmission::Command)
    }

    fn advance_from_committed(&self, next: WorkerAdmission) -> Result<(), AdmissionCancelled> {
        self.admissions
            .advance(
                &self.admission_id,
                &[WorkerAdmission::Committed],
                Some(next),
            )
            .then_some(())
            .ok_or(AdmissionCancelled)
    }

    /// The started prompt queued as durable submission `submission`.
    pub(crate) fn admitted(self, submission: eukhe_durable::types::SubmissionId) {
        self.admissions.advance(
            &self.admission_id,
            &[WorkerAdmission::Starting],
            Some(WorkerAdmission::Admitted(submission)),
        );
    }

    /// The started prompt parked in the held inputs.
    pub(crate) fn held(self) {
        self.admissions.advance(
            &self.admission_id,
            &[WorkerAdmission::Starting],
            Some(WorkerAdmission::Held),
        );
    }
}

impl Drop for CommittedAdmission {
    fn drop(&mut self) {
        self.admissions.advance(
            &self.admission_id,
            &[
                WorkerAdmission::Committed,
                WorkerAdmission::Starting,
                WorkerAdmission::Command,
            ],
            None,
        );
    }
}

impl Worker {
    /// Register a prompt's admission (the worker-side bookkeeping the
    /// forwarded cancellations read).
    pub(crate) fn register_prompt_admission(&self, admission_id: &str) {
        self.prompt_admissions.register(admission_id);
    }

    /// `cancel_prompt_admission` (the worker arm the supervisor forwards
    /// to): the TS status ladder over the worker's registry. A plain cancel
    /// stops a waiting admission (`cancelled`) and answers `owned` for a
    /// committed one. A `cancelOwned` cancel answers what it did:
    /// `cancelled` when the prompt never runs (it had not started),
    /// `owned` when it withdrew the queued submission or the held input,
    /// or aborted the run that placed it, `ran` when the prompt already ran
    /// (or runs) as a command or a settled submission, and `notWithdrawn`
    /// when the prompt left where the cancel could reach it (a held input
    /// a release delivered or a clear dropped).
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
        let status = if payload.get("cancelOwned").and_then(Value::as_bool) == Some(true) {
            let found = self.prompt_admissions.cancel_owned(admission_id).await;
            match self.withdraw_owned(&hosted, admission_id, found).await {
                Ok(status) => status,
                Err(error) => return response_failure(None, COMMAND, &error, None),
            }
        } else {
            match self.prompt_admissions.cancel(admission_id) {
                None => "unknown",
                Some(WorkerAdmission::Waiting | WorkerAdmission::Cancelled) => {
                    self.prompt_admissions.clear(admission_id);
                    "cancelled"
                }
                Some(_) => "owned",
            }
        };
        response_success(None, COMMAND, Some(json!({ "status": status })))
    }

    /// Withdraw what a `cancelOwned` cancel found; answers the wire status.
    async fn withdraw_owned(
        &self,
        hosted: &crate::worker::HostedSession,
        admission_id: &str,
        found: OwnedCancel,
    ) -> Result<&'static str, String> {
        let cx = eukhe_chord::context::BACKGROUND_CONTEXT.clone();
        match found {
            OwnedCancel::Unknown => Ok("unknown"),
            OwnedCancel::Cancelled => {
                self.prompt_admissions.clear(admission_id);
                Ok("cancelled")
            }
            OwnedCancel::Command => Ok("ran"),
            OwnedCancel::Held => {
                let removed = crate::worker::mutate_withdrawn(
                    hosted,
                    &self.core,
                    &self.events,
                    |mut state| {
                        let before = state.held.len();
                        state
                            .held
                            .retain(|input| input.request.as_deref() != Some(admission_id));
                        let removed = state.held.len() != before;
                        (state, removed)
                    },
                )
                .await
                .map_err(|error| error.to_string())?;
                self.prompt_admissions.clear(admission_id);
                Ok(if removed { "owned" } else { "notWithdrawn" })
            }
            OwnedCancel::Admitted(submission) => {
                let main = hosted.main().map_err(|error| error.to_string())?;
                let aborted = hosted
                    .harness()
                    .abort_submission(submission, Some(main.id()), &cx)
                    .await
                    .map_err(|error| error.to_string())?;
                match aborted {
                    eukhe_durable::harness::AbortSubmissionResult::AlreadyPlaced => {
                        main.abort(
                            eukhe_durable::harness::types::ConversationAbortOptions::default(),
                            &cx,
                        )
                        .await
                        .map_err(|error| error.to_string())?;
                        Ok("owned")
                    }
                    eukhe_durable::harness::AbortSubmissionResult::Aborted => {
                        self.prompt_admissions.clear(admission_id);
                        Ok("owned")
                    }
                    eukhe_durable::harness::AbortSubmissionResult::Settled => {
                        self.prompt_admissions.clear(admission_id);
                        Ok("ran")
                    }
                    eukhe_durable::harness::AbortSubmissionResult::NotFound => {
                        self.prompt_admissions.clear(admission_id);
                        Ok("notWithdrawn")
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::future::Future;

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

    /// A `cancelOwned` cancel answers what the admission became: one that
    /// has not started (its prompt waits at the run gate) is withdrawn at
    /// once and never starts; a starting one is waited for until it is
    /// queued, held or gone; a running command answers itself and clears
    /// when it ends. A plain cancel before the commit refuses the prompt.
    #[tokio::test]
    async fn a_cancel_owned_answers_what_the_admission_became() {
        let admissions = WorkerAdmissions::new();
        admissions.register("at-gate");
        let mut at_gate = admissions
            .commit("at-gate")
            .expect("a waiting admission commits");
        assert_eq!(
            admissions.cancel_owned("at-gate").await,
            OwnedCancel::Cancelled
        );
        assert_eq!(at_gate.start(), Err(AdmissionCancelled));

        let starting = |admission_id: &str| {
            admissions.register(admission_id);
            let mut committed = admissions
                .commit(admission_id)
                .expect("a waiting admission commits");
            assert_eq!(committed.start(), Ok(()));
            committed
        };
        let failed = starting("failed");
        let cancel = admissions.cancel_owned("failed");
        tokio::pin!(cancel);
        assert!(futures::poll!(&mut cancel).is_pending());
        drop(failed);
        assert_eq!(cancel.await, OwnedCancel::Unknown);

        let submission = eukhe_durable::types::SubmissionId::from_number(7);
        let queued = starting("queued");
        let cancel = admissions.cancel_owned("queued");
        tokio::pin!(cancel);
        assert!(futures::poll!(&mut cancel).is_pending());
        queued.admitted(submission);
        assert_eq!(cancel.await, OwnedCancel::Admitted(submission));

        let held = starting("held");
        let cancel = admissions.cancel_owned("held");
        tokio::pin!(cancel);
        assert!(futures::poll!(&mut cancel).is_pending());
        held.held();
        assert_eq!(cancel.await, OwnedCancel::Held);

        admissions.register("command");
        let mut command = admissions
            .commit("command")
            .expect("a waiting admission commits");
        assert_eq!(command.command(), Ok(()));
        assert_eq!(
            admissions.cancel_owned("command").await,
            OwnedCancel::Command
        );
        drop(command);
        assert_eq!(
            admissions.cancel_owned("command").await,
            OwnedCancel::Unknown
        );

        admissions.register("early");
        assert_eq!(admissions.cancel("early"), Some(WorkerAdmission::Cancelled));
        assert_eq!(admissions.commit("early").err(), Some(AdmissionCancelled));
    }

    async fn cancel_owned(worker: &Worker, admission_id: &str) -> Option<Value> {
        worker
            .dispatch(
                "cancel_prompt_admission",
                &json!({ "admissionId": admission_id, "cancelOwned": true }),
            )
            .await
            .data
    }

    fn status(status: &str) -> Option<Value> {
        Some(json!({ "status": status }))
    }

    /// Drive `prompt` until its admission commits (it may wait on the
    /// session's own writes first).
    async fn until_committed<F: Future>(
        worker: &Worker,
        mut prompt: std::pin::Pin<&mut F>,
        admission_id: &str,
    ) {
        while worker.prompt_admissions.lock().get(admission_id) != Some(&WorkerAdmission::Committed)
        {
            assert!(futures::poll!(prompt.as_mut()).is_pending());
            tokio::task::yield_now().await;
        }
    }

    /// A `cancelOwned` cancel that arrives while a restart decision holds
    /// the run gate closed answers at once, and the prompts waiting at the
    /// gate (a typed prompt and a `/compact`) never run: the cancels finish
    /// before the gate opens.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn a_cancel_owned_behind_a_closed_run_gate_answers_at_once() {
        let (_dir, worker) = crate::durable_test_support::created_worker_with(
            "cancel-gate",
            json!(["ran"]),
            json!({ "noSession": true }),
        )
        .await;
        assert!(worker.dispatch("worker_quiesce", &json!({})).await.success);
        let typed_payload = json!({ "message": "withdraw me", "admissionId": "adm-typed" });
        let typed = worker.dispatch("prompt_and_wait", &typed_payload);
        tokio::pin!(typed);
        let compact_payload = json!({ "message": "/compact", "admissionId": "adm-compact" });
        let compact = worker.dispatch("prompt_and_wait", &compact_payload);
        tokio::pin!(compact);
        // Each prompt commits its admission, then waits at the closed gate.
        until_committed(&worker, typed.as_mut(), "adm-typed").await;
        until_committed(&worker, compact.as_mut(), "adm-compact").await;

        assert_eq!(
            cancel_owned(&worker, "adm-typed").await,
            status("cancelled")
        );
        assert_eq!(
            cancel_owned(&worker, "adm-compact").await,
            status("cancelled")
        );
        assert!(worker.dispatch("worker_release", &json!({})).await.success);
        for answered in [typed.await, compact.await] {
            assert_eq!(
                answered.error.as_deref(),
                Some("Prompt admission was cancelled."),
                "{answered:?}"
            );
        }
        let answers = crate::durable_test_support::worker_rows(&worker, "pi.assistant").await;
        assert!(answers.is_empty(), "a cancelled prompt ran: {answers:?}");
    }

    /// A `cancelOwned` cancel of a prompt an input-pause lease parked
    /// withdraws it from the held inputs, and answers `notWithdrawn` for
    /// one a queue clear already dropped: never `owned` with nothing
    /// withdrawn. Neither runs once the lease is released.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn a_cancel_owned_withdraws_a_held_prompt() {
        let (_dir, worker) = crate::durable_test_support::created_worker_with(
            "cancel-held",
            json!(["next answer"]),
            json!({ "noSession": true }),
        )
        .await;
        let pause = worker
            .dispatch(
                "acquire_session_input_pause",
                &json!({ "leaseKey": "stop", "clientId": "acp" }),
            )
            .await;
        let pause_id = pause.data.expect("a pause id")["pauseId"].clone();
        for admission_id in ["adm-held", "adm-cleared"] {
            let parked = worker
                .dispatch(
                    "prompt",
                    &json!({ "message": admission_id, "admissionId": admission_id }),
                )
                .await;
            assert!(parked.success, "{parked:?}");
        }
        let held = || -> Vec<String> {
            worker
                .core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .held
                .iter()
                .map(|input| input.text.clone())
                .collect()
        };
        assert_eq!(held(), ["adm-held", "adm-cleared"]);

        assert_eq!(cancel_owned(&worker, "adm-held").await, status("owned"));
        assert_eq!(held(), ["adm-cleared"]);
        assert!(
            worker
                .dispatch("abort_and_clear_queue", &json!({}))
                .await
                .success
        );
        assert_eq!(
            cancel_owned(&worker, "adm-cleared").await,
            status("notWithdrawn")
        );

        let released = worker
            .dispatch(
                "release_session_input_pause",
                &json!({ "pauseId": pause_id, "clientId": "acp" }),
            )
            .await;
        assert!(released.success, "{released:?}");
        // Nothing withdrawn is delivered: the next prompt is the only one
        // the session placed.
        let next = worker
            .dispatch("prompt_and_wait", &json!({ "message": "next" }))
            .await;
        assert!(next.success, "{next:?}");
        let users = crate::durable_test_support::worker_rows(&worker, "pi.user").await;
        assert_eq!(users.len(), 1, "{users:?}");
        assert!(users[0].to_string().contains("next"), "{users:?}");
    }

    /// A prompt that runs as a typed session command or a `/budget` toggle
    /// answers `ran` to a `cancelOwned` cancel while it runs (there is
    /// nothing to withdraw), and its admission clears once it ends.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn a_cancel_owned_of_a_session_command_answers_that_it_ran() {
        let (_dir, worker) = crate::durable_test_support::created_worker_with(
            "cancel-command",
            json!([]),
            json!({ "noSession": true }),
        )
        .await;
        // The admission as a command prompt holds it while the command runs.
        worker.register_prompt_admission("adm-running");
        let mut running = worker
            .prompt_admissions
            .commit("adm-running")
            .expect("a waiting admission commits");
        assert_eq!(running.command(), Ok(()));
        assert_eq!(cancel_owned(&worker, "adm-running").await, status("ran"));
        drop(running);
        assert_eq!(
            cancel_owned(&worker, "adm-running").await,
            status("unknown")
        );

        for (message, admission_id) in [("/accept", "adm-accept"), ("/budget off", "adm-budget")] {
            let _ = worker
                .dispatch(
                    "prompt_and_wait",
                    &json!({ "message": message, "admissionId": admission_id }),
                )
                .await;
            assert_eq!(
                cancel_owned(&worker, admission_id).await,
                status("unknown"),
                "{message}"
            );
        }
    }
}
