//! `factory.report`: the kernel's factory executor (`rlm/factory.py`)
//! reports every milestone that takes a run out of `running` (done,
//! failed, stopped, or paused by an `escalate` failure) to the agent that
//! started it. The report is a `[job-settled job:factory-<run_id>
//! status:S]` input of that agent's conversation: an idle agent wakes into
//! a turn, a busy one takes it when its turn ends. The run's ledger seq
//! keys the request id, so a repeated report is admitted once.

use std::sync::{Arc, Weak};

use eukhe_durable::harness::types::{InputSubmissionDraft, WhenBusy};
use eukhe_types::input_origin::{InputOrigin, Report};
use eukhe_types::job::{CellStatus, JobId};
use eukhe_types::pi_ai::UserContent;
use futures::FutureExt;
use serde::Deserialize;
use serde_json::{json, Value};

use super::super::{HostCall, HostCallHandler};
use super::{background, RlmRuntime};
use crate::durable::entries::input_entry;
use crate::durable::main_conversation::main_conversation_id;
use crate::durable::messages::JOB_SETTLED_CUSTOM_TYPE;

/// How a run left `running`, as the executor reports it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
enum RunEnd {
    /// Every state settled without an error.
    Done,
    /// A state errored (its failure policy ended the run, or the run
    /// finished with errored states).
    Failed,
    /// A limit, or a stop from the factory view, ended the run.
    Stopped,
    /// An `escalate` failure paused the run: the agent resumes or stops it.
    Paused,
}

impl RunEnd {
    /// The report header's status: a paused run reports the failure that
    /// paused it.
    fn status(self) -> CellStatus {
        match self {
            Self::Done => CellStatus::Ok,
            Self::Failed | Self::Paused => CellStatus::Error,
            Self::Stopped => CellStatus::Aborted,
        }
    }
}

/// One `factory.report` payload.
#[derive(Debug, Deserialize)]
struct FactoryReport {
    run_id: String,
    /// The milestone's ledger seq within the run.
    seq: u64,
    state: RunEnd,
    /// The report body: the run's outcome and its states by status.
    report: String,
}

pub(super) fn register(runtime: &Arc<RlmRuntime>) {
    let weak: Weak<RlmRuntime> = Arc::downgrade(runtime);
    let handler: HostCallHandler = Arc::new(move |call: HostCall| {
        let weak = Weak::clone(&weak);
        async move {
            let runtime = weak.upgrade().ok_or_else(|| {
                anyhow::anyhow!("the session ended before the report could be delivered")
            })?;
            deliver(&runtime, &call).await
        }
        .boxed()
    });
    runtime
        .deps
        .host_requests
        .register("factory.report", handler);
}

/// Admit the report into the conversation of the cell that sent it, else
/// the session's main conversation (a run's control loop outlives the cell
/// that started it). A closing session admits none.
async fn deliver(runtime: &RlmRuntime, call: &HostCall) -> anyhow::Result<Value> {
    let report: FactoryReport = serde_json::from_value(call.data.clone())
        .map_err(|error| anyhow::anyhow!("factory.report: {error}"))?;
    let job = JobId::new(format!("factory-{}", report.run_id))?;
    let cx = background();
    let harness = runtime.deps.harness.require()?;
    let conversation_id = match &call.call {
        Some(api) => api.conversation_id(),
        None => main_conversation_id(&harness, &cx).await?,
    };
    let conversation = harness
        .conversation(conversation_id, &cx)
        .await?
        .ok_or_else(|| anyhow::anyhow!("conversation {conversation_id} does not exist"))?;
    let status = report.state.status();
    let header = Report::JobSettled {
        job: job.clone(),
        status,
    };
    let text = header.render(&report.report);
    let entry = input_entry(
        JOB_SETTLED_CUSTOM_TYPE,
        UserContent::Text(text.clone()),
        true,
        Some(json!({ "job": job.as_str(), "status": status.label() })),
        InputOrigin::Report {
            report: header.clone(),
        },
    )?;
    let draft = InputSubmissionDraft {
        request_id: Some(format!("factory-report:{}:{}", report.run_id, report.seq)),
        content: UserContent::Text(text),
        when_busy: Some(WhenBusy::FollowUp),
        origin: InputOrigin::Report { report: header },
        entry: Some(entry),
    };
    let admitted = runtime
        .deps
        .closing
        .admit(|| conversation.submit(draft, &cx))
        .await;
    match admitted {
        Some(submitted) => {
            submitted?;
            Ok(json!({ "admitted": true }))
        }
        None => Ok(json!({ "admitted": false })),
    }
}
