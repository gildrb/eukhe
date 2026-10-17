//! The jobs in the session state tree. Each job is one session-scope
//! `eukhe.job` document, keyed by the job id: its start creates it and its
//! end retires it, so the state tree holds one node (under the root) per
//! running job, and the node of a job started after a rewind target is not
//! in the tree at the target. The output of a job is never committed.
//!
//! A writer task (a session service) commits the records of the table in
//! order, a batch per commit, off every caller's path. A job that starts
//! and ends within one batch commits nothing. At open the writer retires
//! the nodes the history left (the jobs of an earlier process, which ended
//! with it).

use std::sync::{Arc, Weak};

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_durable::documents::{DocFamilyDefinition, SessionDocFamily};
use eukhe_durable::harness::define::section;
use eukhe_durable::harness::types::{PromptInput, PromptSection};
use eukhe_durable::harness::Harness;
use eukhe_durable::session::{CommitListener, SessionResult};
use eukhe_durable::tree::{SessionTree, StateKind, StateNode};
use eukhe_durable::types::EntryId;
use eukhe_types::job::JobId;
use futures::FutureExt;
use serde::{Deserialize, Serialize};
use tokio::sync::mpsc;

use super::{JobEnd, JobKind, Wait};
use crate::durable::main_conversation::main_conversation_id;
use crate::durable::rlm::{submit_notice, CustomNotice};
use crate::durable::{EukheSession, HostDeps, OpenedSession, ServiceStop};

/// The document kind of a job node.
pub const JOB_DOC_KIND: &str = "eukhe.job";

/// Records a writer batch takes at most.
const BATCH: usize = 64;

/// The `eukhe.job` document value.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(super) struct JobDocState {
    /// [`JobKind::name`].
    kind: String,
    label: String,
}

/// One `eukhe.job` document per job, keyed by the job id (version 1); the
/// seed is the value.
pub(super) static JOB_DOC: SessionDocFamily<JobDocState, JobDocState> =
    match SessionDocFamily::define(DocFamilyDefinition {
        kind: JOB_DOC_KIND,
        version: 1,
        initial: |seed| seed,
        migrate: None,
        checkpoint_when: None,
    }) {
        Ok(token) => token,
        Err(_) => panic!("eukhe.job has a valid version"),
    };

/// What the writer commits.
#[derive(Clone)]
pub(super) enum JobRecord {
    Start {
        id: JobId,
        kind: JobKind,
        label: String,
    },
    /// The job's one end (a node of an earlier process: killed).
    End { id: JobId, end: JobEnd },
}

impl JobRecord {
    fn id(&self) -> &JobId {
        match self {
            Self::Start { id, .. } | Self::End { id, .. } => id,
        }
    }
}

/// The custom type of the notice of a job record the writer could not
/// commit.
pub const JOB_RECORD_FAILED_CUSTOM_TYPE: &str = "job_record_failed";

/// The ids of the job nodes of `tree`, in start order.
fn job_ids(tree: &SessionTree<StateNode>) -> Vec<String> {
    tree.iter()
        .filter(|(_, node)| {
            node.value.kind == StateKind::Document && node.value.value["kind"] == JOB_DOC_KIND
        })
        .filter_map(|(_, node)| node.value.value["key"].as_str().map(str::to_owned))
        .collect()
}

/// Start the session's job writer when the session opens (one service),
/// and let the job table see the order of the session's entries.
pub fn install(deps: &Arc<HostDeps>) {
    deps.add_service(Box::new(|opened: OpenedSession| {
        async move {
            let Some(queue) = opened.deps.jobs.take_queue() else {
                return Ok(None);
            };
            let table = Arc::downgrade(&opened.deps);
            let listener: CommitListener = Arc::new(move |publication, _| {
                if let Some(deps) = table.upgrade() {
                    deps.jobs.observe(publication);
                }
            });
            let entries = opened.harness.subscribe_commits(listener)?;
            let writer = tokio::spawn(write_records(opened.harness.clone(), queue));
            let sweep = tokio::spawn(retire_stale(Arc::downgrade(&opened.deps)));
            let stop: ServiceStop = Box::new(move || {
                async move {
                    entries.unsubscribe();
                    sweep.abort();
                    writer.abort();
                }
                .boxed()
            });
            SessionResult::Ok(Some(stop))
        }
        .boxed()
    }));
}

/// Commit `records` in one commit.
#[tracing::instrument(skip_all, fields(records = records.len()))]
async fn commit_records(harness: &Harness, records: Vec<JobRecord>) -> SessionResult<()> {
    harness
        .commit(
            move |tx| async move {
                for record in records {
                    match record {
                        JobRecord::Start { id, kind, label } => {
                            let seed = JobDocState {
                                kind: kind.name().to_owned(),
                                label,
                            };
                            tx.doc_member(&JOB_DOC, id.as_str(), &seed).await?;
                        }
                        // The retirement of an absent node retires nothing.
                        JobRecord::End { id, end } => {
                            tracing::debug!(job = %id, ?end, "retiring the node of an ended job");
                            tx.retire_doc(&JOB_DOC, id.as_str()).await?;
                        }
                    }
                }
                Ok(())
            },
            &BACKGROUND_CONTEXT,
        )
        .await
}

/// Commit the records of the table, a batch per commit, until the session
/// closes. When a batch fails, commit its records one at a time, so one
/// bad record loses no other; a record that fails alone goes to the main
/// conversation as a notice.
#[tracing::instrument(skip_all)]
pub(super) async fn write_records(harness: Harness, mut queue: mpsc::UnboundedReceiver<JobRecord>) {
    let mut batch = Vec::new();
    while queue.recv_many(&mut batch, BATCH).await > 0 {
        let ended: Vec<JobId> = batch
            .iter()
            .filter_map(|record| match record {
                JobRecord::End { id, .. } => Some(id.clone()),
                JobRecord::Start { .. } => None,
            })
            .collect();
        let started: Vec<JobId> = batch
            .iter()
            .filter_map(|record| match record {
                JobRecord::Start { id, .. } => Some(id.clone()),
                JobRecord::End { .. } => None,
            })
            .collect();
        // A job that starts and ends within the batch leaves no node.
        let records: Vec<JobRecord> = batch
            .drain(..)
            .filter(|record| !(started.contains(record.id()) && ended.contains(record.id())))
            .collect();
        if records.is_empty() {
            continue;
        }
        let Err(error) = commit_records(&harness, records.clone()).await else {
            continue;
        };
        tracing::warn!(%error, "a batch of job records failed; committing them one at a time");
        for record in records {
            let (id, what) = match &record {
                JobRecord::Start { id, .. } => (id.clone(), "start"),
                JobRecord::End { id, .. } => (id.clone(), "end"),
            };
            let Err(error) = commit_records(&harness, vec![record]).await else {
                continue;
            };
            tracing::error!(job = %id, %error, "committing a job record failed");
            let notice = CustomNotice::new(
                JOB_RECORD_FAILED_CUSTOM_TYPE,
                format!(
                    "[job-record-failed]\n\nThe session could not record the {what} of the job {id}: {error}\nThe running-jobs section can be wrong about this job until the session opens again."
                ),
                true,
                None,
            );
            let delivered = match main_conversation_id(&harness, &BACKGROUND_CONTEXT).await {
                Ok(main) => submit_notice(&harness, main, &notice, &BACKGROUND_CONTEXT).await,
                Err(error) => Err(error.into()),
            };
            if let Err(error) = delivered {
                tracing::error!(job = %id, %error, "the notice of a failed job record failed");
            }
        }
    }
}

/// Retire the job nodes the history left: no job of this process holds
/// them.
#[tracing::instrument(skip_all)]
async fn retire_stale(deps: Weak<HostDeps>) {
    let Some(tree) = deps
        .upgrade()
        .and_then(|deps| deps.state_tree.get().and_then(Weak::upgrade))
    else {
        return;
    };
    let Some(held) = tree.read(|state| job_ids(state.tree())).await else {
        return;
    };
    let Some(deps) = deps.upgrade() else {
        return;
    };
    for id in held {
        if deps.jobs.get(&id).is_some() {
            continue;
        }
        match JobId::new(id) {
            Ok(id) => {
                // It ended with the process that ran it.
                let _ = deps.jobs.records.send(JobRecord::End {
                    id,
                    end: JobEnd::Killed,
                });
            }
            Err(error) => tracing::warn!(%error, "a job node with an invalid id"),
        }
    }
}

/// The orphan jobs a rewind sent the kill to.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Orphans {
    /// The jobs whose end came within the wait.
    pub stopped: Vec<JobId>,
    /// The jobs that had not ended when the wait passed: their kill was
    /// sent, and their end comes later.
    pub stopping: Vec<JobId>,
}

/// Stop the orphan jobs of a rewind of `session` to the state tree just
/// after `target` was added (`None`: the empty tree): send the kill to
/// every running job that started after that entry
/// ([`JobTable::rewind_to`](super::JobTable::rewind_to)), then wait for
/// their ends, at most the session's blocking budget. A kill only sends
/// the signal, so a job can end after the wait: it is `stopping`.
#[tracing::instrument(skip_all)]
pub async fn stop_orphans(session: &EukheSession, target: Option<EntryId>) -> Orphans {
    let deps = session.deps();
    let killed = deps.jobs.rewind_to(target);
    let deadline = tokio::time::Instant::now() + deps.blocking_budget();
    let waits = killed
        .iter()
        .map(|job| super::wait_until(deadline, job.ended()));
    let mut orphans = Orphans::default();
    for (job, waited) in killed.iter().zip(futures::future::join_all(waits).await) {
        match waited {
            Wait::Settled(_) => orphans.stopped.push(job.id().clone()),
            Wait::Detached => orphans.stopping.push(job.id().clone()),
        }
    }
    if !killed.is_empty() {
        tracing::info!(?orphans, "a rewind stopped its orphan jobs");
    }
    orphans
}

/// The `running-jobs` system prompt section: the running jobs of the
/// session state tree, their count and ids; absent while none runs.
pub fn running_jobs_section(deps: &Arc<HostDeps>) -> Arc<PromptSection> {
    let deps = Arc::downgrade(deps);
    section(
        "running-jobs",
        move |_input: &PromptInput, _cx| {
            let tree = deps
                .upgrade()
                .and_then(|deps| deps.state_tree.get().and_then(Weak::upgrade));
            async move {
                let Some(tree) = tree else {
                    return Ok(None);
                };
                let ids = tree
                    .read(|state| job_ids(state.tree()))
                    .await
                    .unwrap_or_default();
                let count = ids.len();
                let noun = if count == 1 { "job runs" } else { "jobs run" };
                Ok((count > 0).then(|| format!("{count} background {noun}: {}.", ids.join(", "))))
            }
            .boxed()
        },
        None,
    )
}
