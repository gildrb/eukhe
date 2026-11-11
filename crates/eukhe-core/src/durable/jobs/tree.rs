//! The jobs in the session state tree. Each job is one session-scope
//! `eukhe.job` document, keyed by the job id: its start creates it and its
//! end retires it, so the state tree holds one node (under the root) per
//! running job, and the node of a job started after a rewind target is not
//! in the tree at the target. The output of a job is never committed.
//!
//! The node is the job's journal (exactly-once effects,
//! `eukhe_bend::rules::once`): its commit is the record `Intended` and
//! `Started` together, awaited before the job starts
//! ([`JobTable::record_start`](super::JobTable::record_start)), so no job
//! runs, and no detach is reported, without a durable start. A writer task
//! (a session service) commits the ends of the table in order, a batch per
//! commit, off every caller's path: an end always commits after its start.
//!
//! At open the nodes the history left are the jobs of an earlier process,
//! whose processes died with the worker that ran them. Each one the
//! compiled core settles unknown is reported interrupted to the main
//! conversation (a `job_settled` notice under the request id
//! `job-interrupted:<job id>`), then its node is retired and the effect
//! noted in the conversation's `eukhe.effects` ledger in one commit. A
//! crash between the two leaves the node: the next open admits the same
//! request id again, which the harness drops, and then retires it, so a
//! job is reported once and never run again.

use std::sync::{Arc, Weak};

use eukhe_bend::rules::once::{self, Mode, Policy, Record, Seen, Verdict};
use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_chord::json::{from_json, JsonValue};
use eukhe_durable::documents::{DocFamilyDefinition, SessionDocFamily};
use eukhe_durable::harness::define::section;
use eukhe_durable::harness::effects::{note_unknown, EffectKind, UnknownEffect};
use eukhe_durable::harness::types::{InputSubmissionDraft, PromptInput, PromptSection, WhenBusy};
use eukhe_durable::harness::{Conversation, Harness};
use eukhe_durable::session::{CommitListener, SessionError, SessionResult};
use eukhe_durable::tree::{SessionTree, StateKind, StateNode};
use eukhe_durable::types::EntryId;
use eukhe_types::input_origin::{InputOrigin, Report};
use eukhe_types::job::{CellStatus, JobId};
use eukhe_types::pi_ai::UserContent;
use eukhe_types::platform::kill_point::kill_point;
use futures::FutureExt;
use serde::{Deserialize, Serialize};
use tokio::sync::mpsc;

use super::{JobEnd, JobKind, Wait};
use crate::durable::deps::SessionClosing;
use crate::durable::entries::input_entry;
use crate::durable::main_conversation::main_conversation_id;
use crate::durable::messages::JOB_SETTLED_CUSTOM_TYPE;
use crate::durable::rlm::{now_millis, submit_notice, CustomNotice};
use crate::durable::{EukheSession, HostDeps, OpenedSession, ServiceStop, StoredWork};

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

/// The one end of a job, which the writer commits as the retirement of
/// its node.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct JobEnded {
    pub(super) id: JobId,
    pub(super) end: JobEnd,
}

/// The custom type of the notice of a job end the writer could not
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

/// Start the session's job writer and its sweep of the jobs of an earlier
/// process when the session opens (one service), and let the job table
/// see the order of the session's entries.
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
            let mode = match opened.stored_work {
                StoredWork::Resume => Mode::Resume,
                StoredWork::Stop => Mode::Stop,
            };
            let sweep = tokio::spawn(interrupt_stale(
                Arc::downgrade(&opened.deps),
                opened.harness.clone(),
                opened.main.clone(),
                mode,
            ));
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

/// Commit the node of the job `id`: its start record.
#[tracing::instrument(skip_all, fields(job = %id))]
pub(super) async fn commit_start(
    harness: &Harness,
    id: &JobId,
    kind: JobKind,
    label: &str,
) -> SessionResult<()> {
    let id = id.clone();
    let seed = JobDocState {
        kind: kind.name().to_owned(),
        label: label.to_owned(),
    };
    harness
        .commit(
            move |tx| async move {
                tx.doc_member(&JOB_DOC, id.as_str(), &seed).await?;
                Ok(())
            },
            &BACKGROUND_CONTEXT,
        )
        .await
}

/// Retire the nodes of the jobs of `ends` in one commit.
#[tracing::instrument(skip_all, fields(ends = ends.len()))]
async fn commit_ends(harness: &Harness, ends: Vec<JobEnded>) -> SessionResult<()> {
    harness
        .commit(
            move |tx| async move {
                for JobEnded { id, end } in ends {
                    // The retirement of an absent node retires nothing.
                    tracing::debug!(job = %id, ?end, "retiring the node of an ended job");
                    tx.retire_doc(&JOB_DOC, id.as_str()).await?;
                }
                Ok(())
            },
            &BACKGROUND_CONTEXT,
        )
        .await
}

/// Commit the ends of the table, a batch per commit, until the session
/// closes. When a batch fails, commit its ends one at a time, so one bad
/// end loses no other; an end that fails alone goes to the main
/// conversation as a notice.
#[tracing::instrument(skip_all)]
pub(super) async fn write_records(harness: Harness, mut queue: mpsc::UnboundedReceiver<JobEnded>) {
    let mut batch = Vec::new();
    while queue.recv_many(&mut batch, BATCH).await > 0 {
        let ends = std::mem::take(&mut batch);
        let Err(error) = commit_ends(&harness, ends.clone()).await else {
            kill_point("job", "finished");
            continue;
        };
        tracing::warn!(%error, "a batch of job ends failed; committing them one at a time");
        for ended in ends {
            let id = ended.id.clone();
            let Err(error) = commit_ends(&harness, vec![ended]).await else {
                kill_point("job", "finished");
                continue;
            };
            tracing::error!(job = %id, %error, "committing a job end failed");
            let notice = CustomNotice::new(
                JOB_RECORD_FAILED_CUSTOM_TYPE,
                format!(
                    "[job-record-failed]\n\nThe session could not record the end of the job {id}: {error}\nThe running-jobs section can be wrong about this job until the session opens again."
                ),
                true,
                None,
            );
            let delivered = match main_conversation_id(&harness, &BACKGROUND_CONTEXT).await {
                Ok(main) => submit_notice(&harness, main, &notice, &BACKGROUND_CONTEXT).await,
                Err(error) => Err(error.into()),
            };
            if let Err(error) = delivered {
                tracing::error!(job = %id, %error, "the notice of a failed job end failed");
            }
        }
    }
}

/// Settle the job nodes the history left (the jobs of an earlier process;
/// a job this process recorded is never one): each is reported to `main`
/// and retired ([`settle_stale`]). The run comes back as `mode`.
#[tracing::instrument(skip_all)]
async fn interrupt_stale(deps: Weak<HostDeps>, harness: Harness, main: Conversation, mode: Mode) {
    let Some(tree) = deps
        .upgrade()
        .and_then(|deps| deps.state_tree.get().and_then(Weak::upgrade))
    else {
        return;
    };
    let Some(held) = tree.read(|state| job_ids(state.tree())).await else {
        return;
    };
    drop(tree);
    let Some(deps) = deps.upgrade() else {
        return;
    };
    for id in held {
        let id = match JobId::new(id) {
            Ok(id) => id,
            Err(error) => {
                tracing::warn!(%error, "a job node with an invalid id");
                continue;
            }
        };
        if deps.jobs.recorded(&id) {
            continue;
        }
        if let Err(error) = settle_stale(&harness, &main, &deps.closing, &id, mode).await {
            tracing::error!(job = %id, %error, "settling a job of an earlier process failed");
        }
    }
}

/// Settle the node of `id`, a job of an earlier process, as the compiled
/// core says (`once::restart` of its journal, `Intended` then `Started`):
/// its process died with the worker that ran it (the supervisor reaps a
/// dead worker's process groups), and nothing tells whether it ran, so
/// the world is dark and a job is never launched twice. An interrupted job
/// is reported to `main` (the `job_settled` row of status `interrupted`,
/// a steer, request id `job-interrupted:<id>`), then its node is retired
/// and the effect noted unknown in `main`'s ledger in one commit. A
/// closing session admits no notice: the node stays for the next open.
#[tracing::instrument(skip_all, fields(job = %id))]
pub(super) async fn settle_stale(
    harness: &Harness,
    main: &Conversation,
    closing: &SessionClosing,
    id: &JobId,
    mode: Mode,
) -> SessionResult<()> {
    let cx = &BACKGROUND_CONTEXT;
    let Some(value) = harness.snapshot(&JOB_DOC, id.as_str(), cx).await? else {
        return Ok(());
    };
    let job: JobDocState = from_json(&JsonValue::Object(value)).map_err(SessionError::other)?;
    let (_, verdict) = once::restart(
        [Record::Intended, Record::Started],
        mode,
        Policy::Never,
        Seen::Dark,
    );
    let effect = match verdict {
        // A job is never launched again: its process belongs to the worker
        // that ran it, and a started journal of a job no repeat drops never
        // answers a launch (`once_never_launches_twice`).
        Verdict::Interrupt | Verdict::Launch => {
            let JobDocState { kind, label } = &job;
            let report = Report::JobSettled {
                job: id.clone(),
                status: CellStatus::Interrupted,
            };
            let text = report.render(&format!(
                "The background {kind} job {id} ({label:?}) was interrupted by a restart: it may have partially run, and its output is lost. It was not run again; check the state it changes before you run it again."
            ));
            let entry = input_entry(
                JOB_SETTLED_CUSTOM_TYPE,
                UserContent::Text(text.clone()),
                true,
                Some(serde_json::json!({
                    "job": id.as_str(),
                    "status": CellStatus::Interrupted.label(),
                })),
                InputOrigin::Report {
                    report: report.clone(),
                },
            )
            .map_err(SessionError::other)?;
            let draft = InputSubmissionDraft {
                request_id: Some(format!("job-interrupted:{id}")),
                content: UserContent::Text(text),
                when_busy: Some(WhenBusy::Steer),
                origin: InputOrigin::Report { report },
                entry: Some(entry),
            };
            let Some(admitted) = closing.admit(|| main.submit(draft, cx)).await else {
                return Ok(());
            };
            admitted.map(drop)?;
            #[expect(
                clippy::cast_precision_loss,
                reason = "epoch milliseconds stay below 2^53"
            )]
            let at = now_millis() as f64;
            Some(UnknownEffect {
                id: format!("job:{id}"),
                kind: EffectKind::Job,
                what: job.label,
                at,
                resolution: None,
            })
        }
        // A started journal is never absent, ended, or unstarted: nothing
        // to report; the node only goes.
        Verdict::Skip | Verdict::Adopt | Verdict::Abandon | Verdict::Settled => None,
    };
    let (conversation, id) = (main.id(), id.clone());
    harness
        .commit(
            move |tx| async move {
                tx.retire_doc(&JOB_DOC, id.as_str()).await?;
                if let Some(effect) = effect {
                    note_unknown(&tx, conversation, &effect).await?;
                }
                Ok(())
            },
            cx,
        )
        .await
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
