//! Saved-session fixtures for the CLI e2e tests: legacy `<id>.jsonl`
//! session files (version-3 rows) that the first open imports into the
//! session's durable storage (`<sessions>/<id>/`).
//!
//! The rows form a real v3 tree (each row's `parentId` names the row
//! before it) and the assistant rows are complete pi-ai messages: the
//! durable import follows the tree from the file's leaf and converts typed
//! messages, so a parentless or partial row would not import.

#![allow(dead_code)] // each including test binary uses its own subset

use std::fmt::Write as _;
use std::path::{Path, PathBuf};

/// The id of the fixture's `session_info` row (the tree's root).
pub fn info_id(id: &str) -> String {
    format!("{id}-info")
}

/// The id of the fixture's last row: the last turn's assistant row, or
/// the `session_info` row of a fixture without turns.
pub fn leaf_id(id: &str, turns: usize) -> String {
    match turns.checked_sub(1) {
        Some(last) => format!("{id}-m{last}a"),
        None => info_id(id),
    }
}

/// One complete assistant message object with `text`, `usage` token
/// counts, and `cost` as the output and total cost.
pub fn assistant_message(
    text: &str,
    provider: &str,
    model: &str,
    input: u64,
    output: u64,
    cost: f64,
    timestamp: u64,
) -> String {
    format!(
        "{{\"role\":\"assistant\",\"content\":[{{\"type\":\"text\",\"text\":\"{text}\"}}],\"api\":\"openai-completions\",\"provider\":\"{provider}\",\"model\":\"{model}\",\"usage\":{{\"input\":{input},\"output\":{output},\"cacheRead\":0,\"cacheWrite\":0,\"totalTokens\":{},\"cost\":{{\"input\":0.0,\"output\":{cost},\"cacheRead\":0.0,\"cacheWrite\":0.0,\"total\":{cost}}}}},\"stopReason\":\"stop\",\"timestamp\":{timestamp}}}",
        input + output,
    )
}

/// Write `<dir>/<id>.jsonl`: a version-3 session header (`parentSession`
/// and `rlmDepth` give the catalog the subagent linkage), the display
/// name, and one user/assistant exchange per turn.
pub fn write_fixture(
    dir: &Path,
    id: &str,
    name: &str,
    parent: Option<&Path>,
    rlm_depth: Option<u64>,
    turns: &[(&str, &str)],
) -> PathBuf {
    let path = dir.join(format!("{id}.jsonl"));
    let mut content = format!(
        "{{\"type\":\"session\",\"version\":3,\"id\":\"{id}\",\"timestamp\":\"2024-01-01T00:00:00.000Z\",\"cwd\":\"/tmp\""
    );
    if let Some(parent) = parent {
        let _ = write!(content, ",\"parentSession\":\"{}\"", parent.display());
    }
    if let Some(rlm_depth) = rlm_depth {
        let _ = write!(content, ",\"rlmDepth\":{rlm_depth}");
    }
    content.push_str("}\n");
    let _ = writeln!(
        content,
        "{{\"type\":\"session_info\",\"id\":\"{}\",\"parentId\":null,\"timestamp\":\"2024-01-01T00:00:00.000Z\",\"name\":\"{name}\"}}",
        info_id(id)
    );
    let mut previous = info_id(id);
    let mut at = 0u64;
    for (index, (user, assistant)) in turns.iter().enumerate() {
        let _ = writeln!(
            content,
            "{{\"type\":\"message\",\"id\":\"{id}-m{index}u\",\"parentId\":\"{previous}\",\"timestamp\":\"2024-01-01T00:00:0{index}.000Z\",\"message\":{{\"role\":\"user\",\"content\":\"{user}\",\"timestamp\":{at}}}}}"
        );
        let _ = writeln!(
            content,
            "{{\"type\":\"message\",\"id\":\"{id}-m{index}a\",\"parentId\":\"{id}-m{index}u\",\"timestamp\":\"2024-01-01T00:00:0{index}.000Z\",\"message\":{}}}",
            assistant_message(assistant, "battery", "mock-1", 0, 0, 0.0, at + 1)
        );
        previous = format!("{id}-m{index}a");
        at += 1000;
    }
    std::fs::write(&path, content).expect("write fixture");
    path
}
