//! What the code mode tool, its sandbox, and its result layout share
//! (pi-codemode `types.ts`, and the details types of pi-durable
//! `codemode.ts`).

use std::sync::Arc;

use eukhe_chord::json::{JsonObject, JsonValue};
use indexmap::IndexMap;
use serde::{Deserialize, Serialize};

/// Where a text item of a script's output came from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TextOrigin {
    /// `text()` or the script's returned value.
    Script,
    /// `console.*`.
    Console,
}

/// One item of a script's output, in the order the script produced it
/// (pi-codemode `CodemodeOutputItem`). `data` is base64.
#[derive(Debug, Clone, PartialEq)]
pub enum CodemodeOutputItem {
    Text { text: String, origin: TextOrigin },
    Image { data: String, mime_type: String },
}

/// Why a script failed (pi-codemode `CodemodeErrorKind`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CodemodeErrorKind {
    /// The script threw or failed to parse; `name` and `stack` come from its
    /// error.
    Script,
    /// The deadline expired. The VM was stopped.
    Timeout,
    /// The run was aborted or the sandbox was closed. The VM was stopped.
    Aborted,
    /// The VM or its bridge failed outside the script's control.
    Sandbox,
}

/// A script's failure (pi-codemode `CodemodeError`).
#[derive(Debug, Clone, PartialEq)]
pub struct CodemodeError {
    pub kind: CodemodeErrorKind,
    pub name: Option<String>,
    pub message: String,
    pub stack: Option<String>,
}

/// Keys a successful script changed with `store()` (pi-codemode
/// `CodemodeStoreWrites`).
#[derive(Debug, Clone, Default, PartialEq)]
pub struct CodemodeStoreWrites {
    pub set: IndexMap<String, JsonValue>,
    /// Keys stored as `undefined`.
    pub delete: Vec<String>,
}

/// The result a run was processing when the script ended it (returned,
/// threw, or exited): `seq` 0 for its first run, and the calls issued by
/// then (pi-codemode `CodemodeDuring`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CodemodeDuring {
    pub seq: u64,
    pub issued: u64,
}

/// How a script ended.
#[derive(Debug, Clone, PartialEq)]
pub enum CodemodeEnding {
    /// It returned (`value` `None`: `undefined`) or called `exit()`.
    Completed {
        value: Option<JsonValue>,
        store_writes: CodemodeStoreWrites,
    },
    Failed(CodemodeError),
}

/// A run's outcome (pi-codemode `CodemodeResult`). `output` is kept for a
/// failed run too, up to the failure.
#[derive(Debug, Clone, PartialEq)]
pub struct CodemodeResult {
    pub ending: CodemodeEnding,
    pub output: Vec<CodemodeOutputItem>,
    pub during: Option<CodemodeDuring>,
}

impl CodemodeResult {
    /// Whether the script completed.
    #[must_use]
    pub fn is_ok(&self) -> bool {
        matches!(self.ending, CodemodeEnding::Completed { .. })
    }
}

/// What a script called.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum CodemodeCallTarget {
    /// `tools.<name>(args)`.
    Tool,
    /// A top-level global such as `searchTools()`.
    Global,
}

/// A call the script made, answered with the run's `deliver()`
/// (pi-codemode `CodemodeHostCall`).
#[derive(Debug, Clone, PartialEq)]
pub struct CodemodeHostCall {
    /// The VM's number for the call, `1`, `2`, ... in the order the script
    /// made its calls, tools and globals.
    pub id: u64,
    pub target: CodemodeCallTarget,
    pub name: String,
    /// What the script passed after a JSON round trip; for spread globals
    /// the argument list. `None`: `undefined`.
    pub args: Option<JsonValue>,
}

/// A call's answer (pi-codemode `CodemodeOutcome`), stored in the journal in
/// its JS shape: `{ ok: true, value? }` or `{ ok: false, message,
/// properties? }`. A rejection becomes an `Error` with `message` in the
/// script, carrying the own properties of `properties` except `name`,
/// `message`, and `stack`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(try_from = "OutcomeRepr", into = "OutcomeRepr")]
pub enum CodemodeOutcome {
    /// Resolves with `value`; `None` is `undefined`.
    Ok { value: Option<JsonValue> },
    Err {
        message: String,
        properties: Option<JsonObject>,
    },
}

#[derive(Serialize, Deserialize)]
struct OutcomeRepr {
    ok: bool,
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        deserialize_with = "crate::types::json_serde::present"
    )]
    value: Option<JsonValue>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    message: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    properties: Option<JsonValue>,
}

impl TryFrom<OutcomeRepr> for CodemodeOutcome {
    type Error = String;

    fn try_from(repr: OutcomeRepr) -> Result<Self, Self::Error> {
        if repr.ok {
            return Ok(Self::Ok { value: repr.value });
        }
        let message = repr
            .message
            .ok_or_else(|| "a failed outcome has no message".to_owned())?;
        let properties = match repr.properties {
            None => None,
            Some(JsonValue::Object(object)) => Some(JsonObject::clone(&object)),
            Some(_) => {
                return Err("the properties of a failed outcome are not an object".to_owned())
            }
        };
        Ok(Self::Err {
            message,
            properties,
        })
    }
}

impl From<CodemodeOutcome> for OutcomeRepr {
    fn from(outcome: CodemodeOutcome) -> Self {
        match outcome {
            CodemodeOutcome::Ok { value } => Self {
                ok: true,
                value,
                message: None,
                properties: None,
            },
            CodemodeOutcome::Err {
                message,
                properties,
            } => Self {
                ok: false,
                value: None,
                message: Some(message),
                properties: properties.map(|object| JsonValue::Object(Arc::new(object))),
            },
        }
    }
}

/// A tool as a run's script sees it: `tools.<js_name>` and its `ALL_TOOLS`
/// entry (pi-codemode `CodemodeDeclaredTool`). A replay passes the
/// `js_name` the run started with.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CodemodeDeclaredTool {
    pub name: String,
    pub js_name: String,
    pub description: String,
}

/// A global as a run's script sees it (pi-codemode
/// `CodemodeDeclaredGlobal`): an identifier, or `namespace.member`.
/// `spread`: the call passes its whole argument list instead of the first
/// argument.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CodemodeDeclaredGlobal {
    pub name: String,
    pub spread: bool,
}

/// The status of one tool call a script made.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum CodemodeCallStatus {
    Running,
    Ok,
    Error,
    Cancelled,
}

/// One tool call a script made, as the code mode call's details show it
/// (pi-durable `CodemodeNestedCall`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CodemodeNestedCall {
    /// The VM's number for the call; its nested call ID is
    /// `<callId>/c<id>`.
    pub id: u64,
    pub name: String,
    /// Compact JSON of the arguments, cut for display.
    pub args: String,
    pub status: CodemodeCallStatus,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub duration_ms: Option<u64>,
    /// Error text, cut for display.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// The code mode call's details (pi-durable `CodemodeToolDetails`): its
/// tool calls in the order it made them, with their status.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CodemodeToolDetails {
    pub calls: Vec<CodemodeNestedCall>,
    /// Temp file with the complete text output, when the output was cut to
    /// its token budget.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub full_output_path: Option<String>,
}
