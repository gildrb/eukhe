//! The code mode call's documents (pi-durable `codemode.ts`
//! `CodemodeRunDoc`, `CodemodeJournalDoc`, `CodemodeStoreDoc`): its start
//! data and outcome, the journal of the results its script got, and the
//! values scripts keep per conversation.

use eukhe_chord::json::JsonValue;
use serde::{Deserialize, Serialize};

use super::types::{CodemodeDeclaredGlobal, CodemodeOutcome};
use crate::documents::{DocDefinition, RewindableConversationDoc, TaskDoc};
use crate::harness::types::ToolExecutionResult;
use crate::types::RewindableFork;

/// One tool as the script sees it: `tools.<js_name>`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct StartTool {
    pub name: String,
    pub js_name: String,
    pub description: String,
    /// The tool declares `structured_output_schema`, so an error result with
    /// a value resolves with it.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub structured: bool,
    /// An internal tool of code mode (`pi.codemode.*`), which scripts reach
    /// only through a global such as `models.classify()`; never in `tools`,
    /// `ALL_TOOLS`, or tool search.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub hidden: bool,
}

/// A namespace of the tools, as `describeNamespace()` and `searchTools()`
/// see it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct StartNamespace {
    pub name: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub description: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub instructions: Option<String>,
    pub tools: Vec<String>,
}

/// What a call starts with; a rerun starts the VM from exactly this.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CodemodeStart {
    pub version: u32,
    pub started_at: f64,
    pub seed: u32,
    /// The VM's fingerprint, recorded by the first run before any call is
    /// admitted.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub fingerprint: Option<String>,
    /// `started_at + timeout_ms` when the script set one.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub deadline: Option<f64>,
    pub tools: Vec<StartTool>,
    pub namespaces: Vec<StartNamespace>,
    pub globals: Vec<CodemodeDeclaredGlobal>,
    /// `max_output_tokens` of the script's options line, or the default.
    pub max_output_tokens: u64,
    /// The conversation's stored values when the call started: an object.
    pub store: JsonValue,
}

/// `pi.codemode.run`: the start data, the result's directory, and the
/// outcome, decided once.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CodemodeRunState {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub start: Option<CodemodeStart>,
    /// Directory of the result's files (the full output, images), created
    /// once: a rerun writes the same files again.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub output_dir: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub result: Option<ToolExecutionResult>,
}

/// A global's call and outcome, journaled because nothing else stores it.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct JournalGlobal {
    pub name: String,
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        deserialize_with = "crate::types::json_serde::present"
    )]
    pub args: Option<JsonValue>,
    pub outcome: CodemodeOutcome,
}

/// One delivered result.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct JournalEntry {
    /// The VM's call ID. Its result is the entry's position + 1 (`seq`).
    pub id: u64,
    /// The VM clock while it processes this result.
    pub at: f64,
    /// Calls the VM had issued after processing this result; absent until
    /// acknowledged.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub issued_after: Option<u64>,
    /// A global's call and outcome; a tool's result is its nested call's.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub global: Option<JournalGlobal>,
}

/// `pi.codemode.journal`: one entry per delivered result, in delivery
/// order.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CodemodeJournal {
    pub entries: Vec<JournalEntry>,
    /// Calls the VM had issued after the script's first run, before any
    /// result; absent until acknowledged.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub first_issued: Option<u64>,
}

/// `pi.codemode.store`: what scripts keep with `store()` and read with
/// `load()`, per conversation.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CodemodeStore {
    /// An object of the stored values.
    pub values: JsonValue,
}

impl Default for CodemodeStore {
    fn default() -> Self {
        Self {
            values: JsonValue::object(),
        }
    }
}

/// `pi.codemode.run` of a code mode call's task; gone when it settles.
pub static CODEMODE_RUN_DOC: TaskDoc<CodemodeRunState> = match TaskDoc::define(DocDefinition {
    kind: "pi.codemode.run",
    version: 1,
    initial: CodemodeRunState::default,
    migrate: None,
    checkpoint_when: None,
}) {
    Ok(token) => token,
    Err(_) => panic!("invalid pi.codemode.run definition"),
};

/// `pi.codemode.journal` of a code mode call's task; gone when it settles.
pub static CODEMODE_JOURNAL_DOC: TaskDoc<CodemodeJournal> = match TaskDoc::define(DocDefinition {
    kind: "pi.codemode.journal",
    version: 1,
    initial: CodemodeJournal::default,
    migrate: None,
    checkpoint_when: None,
}) {
    Ok(token) => token,
    Err(_) => panic!("invalid pi.codemode.journal definition"),
};

/// `pi.codemode.store` of a conversation: rewindable and copied as of the
/// fork point, so a fork sees the values as they were when its entry was
/// committed.
pub static CODEMODE_STORE_DOC: RewindableConversationDoc<CodemodeStore> =
    match RewindableConversationDoc::define(
        DocDefinition {
            kind: "pi.codemode.store",
            version: 1,
            initial: CodemodeStore::default,
            migrate: None,
            checkpoint_when: None,
        },
        RewindableFork::AsOf,
    ) {
        Ok(token) => token,
        Err(_) => panic!("invalid pi.codemode.store definition"),
    };
