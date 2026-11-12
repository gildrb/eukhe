//! The loop's conversation document `eukhe.loop`: the state the compiled
//! core steps (`bend/loop.bend` `St`), and what Rust keeps beside it to
//! carry out the core's answers exactly once across a crash.

use eukhe_durable::documents::{ConversationDoc, DocDefinition};
use eukhe_durable::types::{LatestFork, TaskId};
use eukhe_types::loop_mode::{LoopLimit, LoopState};
use serde::{Deserialize, Serialize};

/// The loop of one conversation; a fork starts with no loop.
pub static LOOP_MODE_DOC: ConversationDoc<LoopDoc> = match ConversationDoc::define(
    DocDefinition {
        kind: LOOP_DOC_KIND,
        version: 1,
        initial: LoopDoc::default,
        migrate: None,
        checkpoint_when: Some(|_, _, _| true),
    },
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("eukhe.loop has a valid version"),
};

/// The document kind of [`LOOP_MODE_DOC`].
pub(crate) const LOOP_DOC_KIND: &str = "eukhe.loop";

/// `eukhe.loop`.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct LoopDoc {
    /// The state the compiled core answered last.
    pub state: LoopState,
    /// The id of this `/loop` (its start clock, in hex): the submissions
    /// of its iterations carry `loop:<id>:<iteration>` as request id, so
    /// none is queued twice.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub loop_id: Option<String>,
    /// The bound given at `/loop`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub limit: Option<LoopLimit>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub started_at_ms: Option<u64>,
    /// The last line the loop reported.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub message: Option<String>,
    /// The iteration a final answer continued into, keyed by the answering
    /// generation task: a rerun of that task after a crash repeats the
    /// continuation instead of deciding again.
    #[serde(rename = "yield", skip_serializing_if = "Option::is_none")]
    pub yield_record: Option<LoopYield>,
    /// The iteration whose prompt is known to be in the transcript because
    /// the user sent it (an adopted prompt carries no loop marker).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub adopted: Option<u64>,
    /// When the loop was armed or paused: only a prompt the user sends
    /// after it becomes the loop's prompt.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub waiting_since_ms: Option<u64>,
    /// A manual compaction cut the turn in flight: its abort is no user
    /// interrupt, and the turn is sent again once the compaction ended.
    pub held: bool,
    /// How many times a cut turn was sent again (keeps their request ids
    /// apart).
    pub resends: u64,
    /// The first output line of the last condition command that broke.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub check_output: Option<String>,
}

/// One continuation a final answer made.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LoopYield {
    pub task_id: TaskId,
    pub iteration: u64,
}
