//! The `cvar` command's wire shapes (docs/control.md S4): the values it
//! answers and the typed data of a rejected command.

use serde::{Deserialize, Serialize};
use serde_json::Value;

/// The value of one cvar.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CvarValue {
    pub id: String,
    pub value: Value,
}

/// A `cvar` success: the session's replicated values after the line.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct CvarReply {
    pub values: Vec<CvarValue>,
    #[serde(default)]
    pub errors: Vec<String>,
}

/// Why a `cvar` command was rejected.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CvarFailureKind {
    /// A session set of a Global cvar (only `/set --global` sets one).
    Global,
    /// No such cvar.
    Undeclared,
    /// The value does not have the cvar's type.
    BadValue,
    /// A toggle of a cvar that is not a bool.
    NotBool,
    /// An alias that runs itself.
    Cycle,
    /// A run of an alias that does not exist.
    UnknownAlias,
    /// The line does not parse.
    Parse,
    /// An `action`, which only a key bind runs.
    Action,
}

/// The `data` of a rejected `cvar` command. A failure line with `data`
/// carries no `error` on the wire (the TS response shape), so the error's
/// text travels here as `message`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CvarFailureData {
    pub kind: CvarFailureKind,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub id: Option<String>,
    pub message: String,
}
