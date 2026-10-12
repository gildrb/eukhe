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
    /// Output the call's single bound left out of the result.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub omitted: Option<OmittedOutput>,
    /// Where the complete output is stored.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub artifact: Option<String>,
}

/// Output a bound left out of a result.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct OmittedOutput {
    pub bytes: u64,
    pub lines: u64,
    pub at: OmittedAt,
}

/// Where the omitted output was.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum OmittedAt {
    /// Before the kept output (the end was kept).
    Start,
    /// After the kept output (the beginning was kept).
    End,
    /// After this kept line (1-based); the rest of the kept output follows.
    AfterLine(u64),
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
