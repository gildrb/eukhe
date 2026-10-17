//! The vocabulary of a bounded output: the default bound, and what the one
//! bound left out.

use std::fmt::Write as _;

use serde::{Deserialize, Serialize};

/// The default line bound of a tool result and of every bounded output.
pub const DEFAULT_MAX_LINES: u64 = 2000;
/// The default byte bound of a tool result and of every bounded output
/// (50 KiB).
pub const DEFAULT_MAX_BYTES: u64 = 50 * 1024;

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

/// The typed facts of a bounded output, as the one text every renderer
/// shows: what was omitted and where, then where the whole output is.
#[must_use]
pub fn describe_bound(omitted: Option<&OmittedOutput>, artifact: Option<&str>) -> String {
    let mut text = String::new();
    if let Some(omitted) = omitted {
        let at = match omitted.at {
            OmittedAt::Start => "at the start".to_owned(),
            OmittedAt::End => "at the end".to_owned(),
            OmittedAt::AfterLine(kept) => format!("after line {kept}"),
        };
        let _infallible = write!(
            text,
            "{} bytes ({} lines) omitted {at}.",
            omitted.bytes, omitted.lines
        );
    }
    if let Some(artifact) = artifact {
        if !text.is_empty() {
            text.push(' ');
        }
        let _infallible = write!(text, "Full output: {artifact}");
    }
    text
}

/// The notice a bounded user-bash output carries into the model text, the
/// same `<harness>` block a tool result renders.
#[must_use]
pub fn bound_notice(omitted: Option<&OmittedOutput>, artifact: Option<&str>) -> String {
    format!(
        "<harness>\n[info] Output bounded. {}\n</harness>",
        describe_bound(omitted, artifact)
    )
}
