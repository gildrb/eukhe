//! Supervisor-side parent-death cleanup for RLM children: the seam that
//! closes a hard-killed parent worker's resident children (the #246
//! adjacent gap).
//!
//! TS ground truth (`modes/daemon/daemon-mode.ts`): RLM children are hosted
//! in the parent's process, so they die with it - any death of the parent,
//! including SIGKILL, takes its children down, and the durable spawn ledger
//! keeps their roster rows as passive family rows. The Rust redesign hosts
//! each child as its own supervisor-owned worker process, and the #246
//! close runs inside the parent worker (the replacement/kill/shutdown
//! teardowns), so a SIGKILL bypasses every close path and the children
//! would survive their parent as orphaned workers. The supervisor's
//! worker-death monitoring is the only component that observes the death,
//! so the close ports there: on an unexpected exit, every resident worker
//! whose durable create names the dead worker as its parent (the runtime
//! metadata's `parentActiveSessionId`, the same join TS
//! `getChildActiveSessionStates` runs) stops with its parent - the same
//! wire action the #246 `SupervisorChildSessions::close_children` issues
//! per child (a `kill` with no `rlmLedgerDelete` marker: a plain stop, so
//! the spawn edge and the passive roster row survive, and the child
//! worker's own kill handler closes the child's children first - the
//! grandchild cascade is the kill route's recursion, TS
//! `closeSessionOnce`'s cascade).

use std::sync::Arc;
use std::time::Duration;

use serde_json::{json, Value};

use crate::backpressure::RouteAdmission;
use crate::registry::ResidentWorker;
use crate::supervisor::Supervisor;
use crate::timeouts;
use eukhe_types::daemon::{DaemonWorkerDescriptor, StopOutcome};

/// Retries for a child the death close left open: one that refused the
/// close (a child worker may still be starting: the supervisor registers
/// a resident before its worker process connects, so the kill route can
/// arrive before the session exists), or whose stop failed to persist.
const CHILD_CLOSE_RETRY_ATTEMPTS: u32 = 3;
/// Space between the close retries: long enough for a starting child to
/// finish connecting, short enough to bound the orphan window.
const CHILD_CLOSE_RETRY_DELAY_MS: u64 = 5_000;

/// Where one child's parent-death close stands.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ChildClose {
    /// The child closed through its own kill handler, which closed its
    /// children first.
    Closed,
    /// The child was stopped by signal (or its stop is carried to the
    /// next boot): its own resident children are orphaned in turn.
    Signaled,
    /// The child is still resident: a later retry owns it.
    Open,
}

impl Supervisor {
    /// Close the resident RLM children of a worker whose process died
    /// without a teardown (the SIGKILL class: none of the #246 worker-side
    /// close paths ran). Runs once per unexpected exit, before the crash
    /// recovery, so a relaunched parent never resumes beside an orphaned
    /// child worker; a hung child holds the restart for one stop grace
    /// plus its escalation. Best-effort, like the TS daemon kill handler's
    /// swallowed close error: a child still open is handed to a bounded
    /// retry walk (never a fresh join - the respawned parent keeps the
    /// dead worker's active session id, so only the residents captured
    /// here belong to the dead instance).
    pub(crate) async fn close_children_of_dead_parent(
        self: &Arc<Self>,
        parent: &Arc<ResidentWorker>,
    ) {
        let children = self.resident_children_of_worker(parent).await;
        self.close_orphaned_children(
            &format!("session worker {} died", parent.worker_id),
            children,
        )
        .await;
    }

    /// Close the resident RLM children of the headless parent session
    /// `parent_id` whose registration ended
    /// ([`crate::headless_parent`]): its connection closed, so the client
    /// process that hosted it exited, normally, on an error or killed.
    /// The same close as a dead parent worker's: the parent is gone and
    /// nothing will collect the children.
    pub(crate) async fn close_children_of_headless_parent(self: &Arc<Self>, parent_id: &str) {
        let children = self.resident_children_of(parent_id).await;
        self.close_orphaned_children(&format!("headless parent {parent_id} left"), children)
            .await;
    }

    /// Close `children`, whose parent is gone (`why` says how, for the
    /// log), all at once, so one hung child holds the close for one stop
    /// grace at most. A child stopped by signal orphans its own children
    /// in turn: they close in the next round. The ones still open go to
    /// the bounded retry walk.
    async fn close_orphaned_children(
        self: &Arc<Self>,
        why: &str,
        children: Vec<Arc<ResidentWorker>>,
    ) {
        if children.is_empty() {
            return;
        }
        self.log_line(&format!(
            "{why} with {} resident RLM child(ren); closing them with the parent",
            children.len()
        ));
        let mut round = children;
        let mut unclosed = Vec::new();
        while !round.is_empty() {
            let closes =
                futures::future::join_all(round.iter().map(|child| self.close_dead_child(child)))
                    .await;
            let mut orphaned = Vec::new();
            for (child, close) in round.into_iter().zip(closes) {
                match close {
                    ChildClose::Closed => {}
                    ChildClose::Signaled => {
                        orphaned.extend(self.resident_children_of_worker(&child).await);
                    }
                    ChildClose::Open => unclosed.push(child),
                }
            }
            round = orphaned;
        }
        if !unclosed.is_empty() {
            let supervisor = Arc::clone(self);
            tokio::spawn(async move {
                supervisor.retry_close_children(unclosed).await;
            });
        }
    }

    /// Bounded retries for children the death close left open: the
    /// same per-child close, never a fresh registry join (the respawned
    /// parent shares the dead worker's active session id, so a re-join
    /// could catch its legitimately spawned children); a child stopped by
    /// signal adds its own children to the walk. A child whose process is
    /// gone, or that left the registry, leaves the walk. Gives up loudly
    /// when a child stays open - its durable parent link keeps it joinable
    /// for an explicit kill.
    async fn retry_close_children(self: Arc<Self>, children: Vec<Arc<ResidentWorker>>) {
        let mut unclosed = children;
        for _ in 0..CHILD_CLOSE_RETRY_ATTEMPTS {
            tokio::time::sleep(Duration::from_millis(CHILD_CLOSE_RETRY_DELAY_MS)).await;
            if self.is_shutting_down() {
                return;
            }
            let mut still_open = Vec::new();
            for child in unclosed {
                if self.child_is_gone(&child).await {
                    self.log_line(&format!(
                        "RLM child worker {} is gone; its parent-death close ends",
                        child.worker_id
                    ));
                    continue;
                }
                match self.close_dead_child(&child).await {
                    ChildClose::Closed => {}
                    ChildClose::Signaled => {
                        still_open.extend(self.resident_children_of_worker(&child).await);
                    }
                    ChildClose::Open => still_open.push(child),
                }
            }
            unclosed = still_open;
            if unclosed.is_empty() {
                return;
            }
        }
        for child in &unclosed {
            self.log_line(&format!(
                "RLM child worker {} outlived its dead parent and could not be closed",
                child.worker_id
            ));
        }
    }

    /// Whether a child of the retry walk is gone: another path took it
    /// out of the registry, or its process exited.
    async fn child_is_gone(&self, child: &Arc<ResidentWorker>) -> bool {
        let resident = self
            .registry
            .get(&child.worker_id)
            .await
            .is_some_and(|current| Arc::ptr_eq(&current, child));
        let pid = child.descriptor.lock().await.pid;
        let exited = u32::try_from(pid)
            .ok()
            .filter(|pid| *pid != 0)
            .is_some_and(|pid| matches!(crate::lease::is_process_alive(pid), Ok(false)));
        !resident || exited
    }

    /// Close one child of a dead parent: the same kill route the #246
    /// `close_children` drives per child (a plain stop - the child
    /// worker's kill handler aborts its in-flight turn and closes its own
    /// children first, so the cascade to grandchildren rides the
    /// recursion) plus the supervisor-side completion of a kill (the
    /// steps the client kill route runs after the worker answers): drop
    /// the worker from the registry and the live roster, then reseed the
    /// ledger so the closed child's passive row appears. The kill gets the
    /// stop grace; a child that leaves it unanswered (hung, or never
    /// connected) is stopped by signal ([`Self::stop_unanswered_child`]).
    ///
    /// The close carries the `shutdown` reason marker: the parent died,
    /// the child did not (TS's in-process child dies with the parent
    /// worker without a close; the Rust worker must be told). The child
    /// keeps its resume entry — no job cancel, no `archived` state — so
    /// its passive row and its scheduled jobs survive the orphaning,
    /// exactly like TS (the wake model owns reviving it later).
    async fn close_dead_child(self: &Arc<Self>, child: &Arc<ResidentWorker>) -> ChildClose {
        match self
            .route_command_typed(
                child,
                "kill",
                json!({ "rlmCloseReason": "shutdown" }),
                timeouts::derived().stop_grace_ms,
                RouteAdmission::Control,
            )
            .await
        {
            Ok(response) if response.success => {
                // The kill is already routed, so the child dies regardless
                // of the tombstone's durability: its exit must read as
                // intentional BEFORE the cleanup path runs, or a failed
                // tombstone persist would leave the exit classified as a
                // crash - the monitor would relaunch the orphan.
                child
                    .intentional_stop
                    .store(true, std::sync::atomic::Ordering::SeqCst);
                if let Err(error) = self.stop_worker(child).await {
                    self.log_line(&format!(
                        "parent-death stop of RLM child worker {} failed: {error:#}; the routed kill owns the rest",
                        child.worker_id
                    ));
                }
                ChildClose::Closed
            }
            Ok(response) => {
                self.log_line(&format!(
                    "parent-death close of RLM child worker {} failed: {}",
                    child.worker_id,
                    response
                        .error
                        .unwrap_or_else(|| "worker refused the close".to_string())
                ));
                ChildClose::Open
            }
            Err(error) => {
                self.log_line(&format!(
                    "parent-death close of RLM child worker {} failed: {error:#}; stopping its process",
                    child.worker_id
                ));
                self.stop_unanswered_child(child).await
            }
        }
    }

    /// Stop a child that left its parent-death close unanswered: SIGTERM,
    /// then the process group's SIGKILL. Its session stays as after a
    /// crash (no archive, its run declared interrupted). Its own children
    /// lost their parent with it ([`ChildClose::Signaled`]): its kill
    /// handler, which closes them on a cooperative stop, never ran.
    async fn stop_unanswered_child(self: &Arc<Self>, child: &Arc<ResidentWorker>) -> ChildClose {
        match self.stop_unanswering_worker(child).await {
            Ok(outcome) => {
                match outcome {
                    StopOutcome::Settled | StopOutcome::ForcedEffectsUnknown => {}
                    StopOutcome::Survived => self.log_line(&format!(
                        "RLM child worker {} survived its parent-death stop; its tombstoned descriptor carries the stop to the next boot",
                        child.worker_id
                    )),
                }
                ChildClose::Signaled
            }
            Err(error) => {
                self.log_line(&format!(
                    "parent-death stop of RLM child worker {} failed: {error:#}",
                    child.worker_id
                ));
                ChildClose::Open
            }
        }
    }

    /// The resident RLM children of `parent`'s worker (never `parent`
    /// itself).
    async fn resident_children_of_worker(
        &self,
        parent: &Arc<ResidentWorker>,
    ) -> Vec<Arc<ResidentWorker>> {
        let parent_id = parent
            .descriptor
            .lock()
            .await
            .root_active_session_id
            .clone();
        let mut children = self.resident_children_of(&parent_id).await;
        children.retain(|child| child.worker_id != parent.worker_id);
        children
    }

    /// The resident workers whose durable create names `parent_id` as
    /// their RLM parent. The join is the runtime metadata's
    /// `parentActiveSessionId` alone (TS
    /// `getChildActiveSessionStates`): a top-level session carries no
    /// parent link and never matches, and a resumed or
    /// forked copy of the parent's session file under another worker
    /// must never adopt another worker's children.
    async fn resident_children_of(&self, parent_id: &str) -> Vec<Arc<ResidentWorker>> {
        let mut children = Vec::new();
        for resident in self.registry.list().await {
            let descriptor = resident.descriptor.lock().await;
            if child_names_parent(&descriptor, parent_id) {
                drop(descriptor);
                children.push(resident);
            }
        }
        children
    }
}

/// Whether one resident's durable create names `parent_id` as its RLM
/// parent: the supervisor-side copy of the TS create `runtimeMetadata`
/// (`parentActiveSessionId`, the field `getChildActiveSessionStates`
/// joins on). A top-level session carries no `parentActiveSessionId` and
/// never matches.
fn child_names_parent(descriptor: &DaemonWorkerDescriptor, parent_id: &str) -> bool {
    descriptor
        .create_command
        .rest
        .get("runtimeMetadata")
        .and_then(|metadata| metadata.get("parentActiveSessionId"))
        .and_then(Value::as_str)
        .is_some_and(|candidate| candidate == parent_id)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// One durable descriptor from a JSON literal (the same fields the
    /// supervisor persists at launch).
    fn descriptor(runtime_metadata: Option<Value>) -> DaemonWorkerDescriptor {
        // The durable create command flattens its `rest` map, so the
        // runtime metadata sits directly under `createCommand` - the same
        // shape the supervisor persists at launch.
        let mut create_command = json!({
            "sessionPath": "/tmp/child.jsonl",
            "noSession": false,
            "cwd": "/work",
        });
        if let Some(metadata) = runtime_metadata {
            create_command["runtimeMetadata"] = metadata;
        }
        serde_json::from_value(json!({
            "version": 2,
            "workerId": "w-child",
            "pid": 42,
            "socketPath": "/tmp/w.sock",
            "recoveryJournalPath": "/tmp/w.recovery.jsonl",
            "supervisorSocketPath": "/tmp/s.sock",
            "authenticationToken": "token",
            "rootActiveSessionId": "child-root",
            "createdAt": "t",
            "updatedAt": "t",
            "lifecycle": "starting",
            "consecutiveFailures": 0,
            "createCommand": create_command,
        }))
        .expect("descriptor json")
    }

    #[test]
    fn a_subagent_names_its_parent_by_active_session_id() {
        let metadata = json!({
            "kind": "subagent",
            "rlmChildId": "sub-1",
            "parentActiveSessionId": "parent-root",
            "rlmDepth": 1,
        });
        let child = descriptor(Some(metadata));
        assert!(child_names_parent(&child, "parent-root"));
        assert!(!child_names_parent(&child, "another-root"));
    }

    #[test]
    fn a_top_level_session_never_matches_a_parent() {
        // No runtime metadata: a plain top-level session create.
        assert!(!child_names_parent(&descriptor(None), "parent-root"));
        // Runtime metadata without a parent link never matches either.
        let root = descriptor(Some(json!({ "kind": "root" })));
        assert!(!child_names_parent(&root, "parent-root"));
    }
}
