//! Data-only types of `harness/types.ts` that durable records reference.

use serde::{Deserialize, Serialize};

/// Severity of a [`ToolDiagnostic`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum ToolDiagnosticSeverity {
    /// `"info"`.
    Info,
    /// `"warn"`.
    Warn,
    /// `"error"`.
    Error,
}

/// Remark about a call for the model and the UI, such as truncation or a
/// spill path; never part of the tool's data. Field order is the order every
/// TS literal that builds one writes: `{ severity, code, message }`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ToolDiagnostic {
    /// How serious the remark is.
    pub severity: ToolDiagnosticSeverity,
    /// Optional machine-readable code.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub code: Option<String>,
    /// The remark.
    pub message: String,
}

/// Why a compaction runs: `compact()`, a threshold in generation preparation,
/// or a context overflow.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum CompactionReason {
    /// `"manual"`.
    Manual,
    /// `"threshold"`.
    Threshold,
    /// `"overflow"`.
    Overflow,
}
