//! The `eukhe.workflow.runs` conversation document: one record per
//! `workflow` tool call (keyed by its task id), with the run's meta, its
//! limits, its agent rows by ordinal, its phases, and its log tail. The
//! `/workflows` view reads it through [`snapshots`].

use std::collections::BTreeMap;
use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_chord::json::{from_json, to_json, JsonObject, JsonValue};
use eukhe_durable::documents::{ConversationDoc, DocDefinition};
use eukhe_durable::session::{SessionResult, Tx};
use eukhe_durable::types::{ConversationId, DocumentReader, DocumentReaderExt, LatestFork};
use eukhe_types::pi_ai::IndexMap;
use eukhe_types::workflow::{
    WorkflowAgent, WorkflowAgentStatus, WorkflowPhase, WorkflowPhaseState, WorkflowRunSnapshot,
    WorkflowRunState, WorkflowSize, WORKFLOW_LOG_TAIL,
};
use serde::{Deserialize, Serialize};

use super::meta::WorkflowMeta;

/// Runs of one conversation, keyed by the `workflow` call's task id.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub(crate) struct WorkflowRuns {
    pub(crate) runs: IndexMap<String, RunRecord>,
}

/// One agent of a run.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct AgentRow {
    pub(crate) ordinal: u32,
    pub(crate) label: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) phase: Option<String>,
    pub(crate) status: WorkflowAgentStatus,
    /// The resume key: the hash of the prompt and options, and the
    /// occurrence of that pair in the run.
    pub(crate) key: String,
    /// The child's session name (`wf<run>-<ordinal>`); `None` for a cached
    /// agent.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) child_name: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) child_session_id: Option<String>,
    /// What the agent returned to the script (a string, an object, or
    /// `null`), once it ended.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) result: Option<serde_json::Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) note: Option<String>,
    /// Whether the agent counts against the run's `max_agents`.
    pub(crate) counted: bool,
}

/// One run.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct RunRecord {
    pub(crate) meta: WorkflowMeta,
    pub(crate) size: WorkflowSize,
    pub(crate) concurrency: u32,
    pub(crate) max_agents: u32,
    pub(crate) state: WorkflowRunState,
    /// Wall clock at the run's start (ms).
    pub(crate) started_at: f64,
    /// The earlier run whose finished agents this run reuses.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) resume_from: Option<String>,
    /// The phase the script entered last.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) active_phase: Option<String>,
    /// Agents by ordinal.
    pub(crate) agents: BTreeMap<u32, AgentRow>,
    pub(crate) logs: Vec<String>,
}

impl RunRecord {
    /// A new running record.
    pub(crate) fn start(
        meta: WorkflowMeta,
        size: WorkflowSize,
        limits: eukhe_types::workflow::WorkflowLimits,
        started_at: f64,
        resume_from: Option<String>,
    ) -> Self {
        Self {
            meta,
            size,
            concurrency: limits.concurrency,
            max_agents: limits.max_agents,
            state: WorkflowRunState::Running,
            started_at,
            resume_from,
            active_phase: None,
            agents: BTreeMap::new(),
            logs: Vec::new(),
        }
    }

    /// Agents that count against `max_agents`.
    pub(crate) fn spawned(&self) -> u32 {
        let counted = self.agents.values().filter(|agent| agent.counted).count();
        u32::try_from(counted).unwrap_or(u32::MAX)
    }

    /// Keep the last [`WORKFLOW_LOG_TAIL`] lines with `line` appended.
    pub(crate) fn push_log(&mut self, line: String) {
        self.logs.push(line);
        let excess = self.logs.len().saturating_sub(WORKFLOW_LOG_TAIL);
        self.logs.drain(..excess);
    }

    /// The view of the run.
    pub(crate) fn snapshot(&self, run_id: &str, session_id: &str) -> WorkflowRunSnapshot {
        let active = self.active_phase.as_deref();
        let active_index = active.and_then(|title| {
            self.meta
                .phases
                .iter()
                .position(|phase| phase.as_str() == title)
        });
        let phases = self
            .meta
            .phases
            .iter()
            .enumerate()
            .map(|(index, title)| WorkflowPhase {
                title: title.clone(),
                state: match (active_index, self.state.is_terminal()) {
                    (_, true) => {
                        if active_index.is_some_and(|active| index > active) {
                            WorkflowPhaseState::Pending
                        } else {
                            WorkflowPhaseState::Done
                        }
                    }
                    (Some(active), false) if index < active => WorkflowPhaseState::Done,
                    (Some(active), false) if index == active => WorkflowPhaseState::Active,
                    (Some(_) | None, false) => WorkflowPhaseState::Pending,
                },
            })
            .collect();
        let count = |status: &[WorkflowAgentStatus]| {
            let matched = self
                .agents
                .values()
                .filter(|agent| status.contains(&agent.status))
                .count();
            u32::try_from(matched).unwrap_or(u32::MAX)
        };
        WorkflowRunSnapshot {
            run_id: run_id.to_owned(),
            session_id: session_id.to_owned(),
            name: self.meta.name.clone(),
            description: self.meta.description.clone(),
            size: self.size,
            state: self.state.clone(),
            phases,
            agents: self
                .agents
                .values()
                .map(|agent| WorkflowAgent {
                    ordinal: agent.ordinal,
                    label: agent.label.clone(),
                    phase: agent.phase.clone(),
                    status: agent.status,
                    child_session_id: agent.child_session_id.clone(),
                    note: agent.note.clone(),
                })
                .collect(),
            spawned: self.spawned(),
            done: count(&[WorkflowAgentStatus::Done, WorkflowAgentStatus::Cached]),
            failed: count(&[WorkflowAgentStatus::Failed, WorkflowAgentStatus::Cancelled]),
            max_agents: self.max_agents,
            concurrency: self.concurrency,
            logs: self.logs.clone(),
        }
    }
}

pub(crate) static WORKFLOW_RUNS_DOC: ConversationDoc<WorkflowRuns> = match ConversationDoc::define(
    DocDefinition {
        kind: "eukhe.workflow.runs",
        version: 1,
        initial: WorkflowRuns::default,
        migrate: None,
        checkpoint_when: None,
    },
    // Runs belong to the conversation that ran them; a fork starts without
    // any.
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("eukhe.workflow.runs has a valid version"),
};

fn decode(value: Option<Arc<JsonObject>>) -> SessionResult<WorkflowRuns> {
    match value {
        None => Ok(WorkflowRuns::default()),
        Some(value) => Ok(from_json(&JsonValue::Object(value))?),
    }
}

/// The committed runs of `conversation_id`.
///
/// # Errors
///
/// Document read failures.
pub(crate) async fn read_runs(
    reader: &(impl DocumentReader + ?Sized),
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<WorkflowRuns> {
    decode(
        reader
            .snapshot(&WORKFLOW_RUNS_DOC, conversation_id, cx)
            .await?,
    )
}

/// The record of `run_id` inside a commit.
pub(crate) async fn tx_run(
    tx: &Tx,
    conversation_id: ConversationId,
    run_id: &str,
) -> SessionResult<Option<RunRecord>> {
    let runs = tx
        .doc(&WORKFLOW_RUNS_DOC, conversation_id)
        .await?
        .child("runs")?;
    match runs.get(run_id)? {
        None => Ok(None),
        Some(item) => Ok(Some(from_json(&item.to_value()?)?)),
    }
}

/// Write `record` as `run_id` inside a commit.
pub(crate) async fn tx_put_run(
    tx: &Tx,
    conversation_id: ConversationId,
    run_id: &str,
    record: &RunRecord,
) -> SessionResult<()> {
    let runs = tx
        .doc(&WORKFLOW_RUNS_DOC, conversation_id)
        .await?
        .child("runs")?;
    runs.set(run_id.to_owned(), to_json(record)?)?;
    Ok(())
}

/// The runs of `conversation_id` of session `session_id`, newest first.
///
/// # Errors
///
/// Document read failures.
pub async fn snapshots(
    reader: &(impl DocumentReader + ?Sized),
    conversation_id: ConversationId,
    session_id: &str,
    cx: &Context,
) -> SessionResult<Vec<WorkflowRunSnapshot>> {
    let runs = read_runs(reader, conversation_id, cx).await?;
    let mut records: Vec<(&String, &RunRecord)> = runs.runs.iter().collect();
    records.sort_by(|(_, a), (_, b)| b.started_at.total_cmp(&a.started_at));
    Ok(records
        .into_iter()
        .map(|(run_id, record)| record.snapshot(run_id, session_id))
        .collect())
}
