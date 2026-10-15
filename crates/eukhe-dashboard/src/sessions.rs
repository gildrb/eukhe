//! The saved root sessions the tab picks from: the `list_saved_sessions`
//! rows of depth 0 without a parent, newest first.

use anyhow::Context;
use serde::{Deserialize, Serialize};
use serde_json::Value;

/// One saved root session as the tab lists it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct SavedSession {
    pub(crate) id: String,
    pub(crate) path: String,
    pub(crate) cwd: String,
    /// The session name, else its first message; `None` when both are
    /// absent or blank.
    pub(crate) title: Option<String>,
    /// The last write, RFC 3339 UTC; empty when the daemon could not date it.
    pub(crate) modified: String,
}

/// One `list_saved_sessions` row (`serializeSavedSessionInfo`).
#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct SavedRow {
    path: String,
    id: String,
    cwd: String,
    rlm_depth: u32,
    parent_session_path: Option<String>,
    modified: String,
    name: Option<String>,
    first_message: String,
}

#[derive(Deserialize)]
struct SavedList {
    sessions: Vec<SavedRow>,
}

/// The root rows of a `list_saved_sessions` answer, in the daemon's order
/// (newest first).
///
/// # Errors
///
/// The answer does not have the `{ sessions: [row...] }` shape.
pub(crate) fn root_sessions(data: &Value) -> anyhow::Result<Vec<SavedSession>> {
    let list = SavedList::deserialize(data).context("read the saved-session list")?;
    Ok(list
        .sessions
        .into_iter()
        .filter(|row| row.rlm_depth == 0 && row.parent_session_path.is_none())
        .map(|row| SavedSession {
            id: row.id,
            path: row.path,
            cwd: row.cwd,
            title: row
                .name
                .filter(|name| !name.trim().is_empty())
                .or_else(|| Some(row.first_message).filter(|first| !first.trim().is_empty())),
            modified: row.modified,
        })
        .collect())
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    #[test]
    fn only_root_rows_list_with_a_title() {
        let row = |id: &str, depth: u32, parent: Option<&str>, name: Option<&str>, first: &str| {
            json!({
                "path": format!("/s/{id}.jsonl"), "id": id, "cwd": "/home/u",
                "rlmDepth": depth, "parentSessionPath": parent,
                "modified": "2026-10-15T08:00:00Z", "name": name, "firstMessage": first,
            })
        };
        let data = json!({ "sessions": [
            row("a", 0, None, Some("named"), "hello"),
            row("b", 1, Some("/s/a.jsonl"), None, "child"),
            row("c", 0, None, Some("  "), "first words"),
            row("d", 0, None, None, " "),
        ] });
        let session = |id: &str, title: Option<&str>| SavedSession {
            id: id.to_string(),
            path: format!("/s/{id}.jsonl"),
            cwd: "/home/u".to_string(),
            title: title.map(str::to_string),
            modified: "2026-10-15T08:00:00Z".to_string(),
        };
        assert_eq!(
            root_sessions(&data).unwrap(),
            vec![
                session("a", Some("named")),
                session("c", Some("first words")),
                session("d", None),
            ]
        );
    }
}
