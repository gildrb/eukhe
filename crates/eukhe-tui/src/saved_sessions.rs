//! What the gateway and the dashboard share as daemon clients that open
//! saved root sessions: the daemon launcher, the saved root-session list,
//! and the resident create + slim attach.

use std::future::Future;
use std::path::Path;

use anyhow::Context;
use eukhe_types::daemon::{DaemonCommand, DaemonSessionLifecycle};
use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};

use crate::daemon_client::DaemonClient;

/// Starts the daemon (or confirms one is running) before a connection.
/// The launcher owns the spawn and readiness wait; `ensure` must return
/// quickly when a daemon already runs.
pub trait DaemonLauncher: Send + Sync + 'static {
    fn ensure(&self) -> impl Future<Output = anyhow::Result<()>> + Send;
}

/// The attach capabilities: the interactive client's set (snapshot state
/// without duplicated history or image payloads).
const ATTACH_CAPABILITIES: [&str; 4] = [
    "attach_snapshot",
    "event_sequence",
    "slim_attach",
    "elide_snapshot_images",
];

/// One saved root session.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SavedSession {
    pub id: String,
    pub path: String,
    pub cwd: String,
    /// The session name, else its first message; `None` when both are
    /// absent or blank.
    pub title: Option<String>,
    /// The last write, RFC 3339 UTC; empty when the daemon could not date it.
    pub modified: String,
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

/// The reply rules every prompt the Signal gateway sends carries ahead of
/// the user's text.
pub const SIGNAL_REPLY_RULES: &str = "[Signal reply rules: ASD-STE100 Simplified Technical English. Lead with the answer. Max 8 short lines. Max 20 words per sentence. No filler, no prose, no tables. Markdown bold/code only.]";

/// A prompt text without the [`SIGNAL_REPLY_RULES`] the gateway puts first
/// (the first message of a phone-started session).
#[must_use]
pub fn strip_signal_reply_rules(text: &str) -> &str {
    text.strip_prefix(SIGNAL_REPLY_RULES)
        .map_or(text, str::trim_start)
}

/// The root rows (depth 0, no parent) of a `list_saved_sessions` answer,
/// newest first (the daemon's order). A phone-started session's first
/// message titles it without the [`SIGNAL_REPLY_RULES`], on every surface
/// that lists it.
///
/// # Errors
///
/// The answer does not have the `{ sessions: [row...] }` shape.
fn root_sessions(data: &Value) -> anyhow::Result<Vec<SavedSession>> {
    let list = SavedList::deserialize(data).context("read the saved-session list")?;
    Ok(list
        .sessions
        .into_iter()
        .filter(|row| row.rlm_depth == 0 && row.parent_session_path.is_none())
        .map(|row| {
            let first = strip_signal_reply_rules(&row.first_message);
            SavedSession {
                title: row
                    .name
                    .filter(|name| !name.trim().is_empty())
                    .or_else(|| Some(first.to_string()).filter(|first| !first.trim().is_empty())),
                id: row.id,
                path: row.path,
                cwd: row.cwd,
                modified: row.modified,
            }
        })
        .collect())
}

/// The saved root sessions of `session_dir`, newest first; see
/// [`root_sessions`].
///
/// # Errors
///
/// The request fails or the answer has another shape.
pub async fn list_root_sessions(
    client: &DaemonClient,
    session_dir: &Path,
    cwd: &Path,
) -> anyhow::Result<Vec<SavedSession>> {
    let data = client
        .request_ok(DaemonCommand::ListSavedSessions {
            id: None,
            active_session_id: None,
            // Required by the cwd-addressed form; without the `current`
            // scope every cwd's sessions answer.
            cwd: Some(cwd.display().to_string()),
            session_dir: Some(session_dir.display().to_string()),
            scope: Value::Null,
            rest: Map::default(),
        })
        .await
        .context("list the saved sessions")?;
    root_sessions(&data)
}

/// The ids of a session the daemon opened.
pub struct CreatedSession {
    pub active_session_id: String,
    pub session_id: String,
    pub session_file: String,
}

/// Open a session as a resident one (a saved `session_path`, else a new
/// session). The daemon reuses a live worker of the same session.
///
/// # Errors
///
/// The create fails, or its answer lacks the session ids.
pub async fn create_resident(
    client: &DaemonClient,
    session_path: Option<String>,
    config: Value,
) -> anyhow::Result<CreatedSession> {
    let created = client
        .request_ok(DaemonCommand::Create {
            id: None,
            session_path,
            continue_recent: None,
            no_session: None,
            name: None,
            config: Some(config),
            runtime_metadata: None,
            lifecycle: Some(DaemonSessionLifecycle::Resident),
            env: None,
            launch_env: None,
            rest: Map::default(),
        })
        .await
        .context("open the session")?;
    let field = |key: &str| {
        created
            .get(key)
            .and_then(Value::as_str)
            .filter(|value| !value.is_empty())
            .map(str::to_string)
            .with_context(|| format!("the daemon opened a session without {key}"))
    };
    Ok(CreatedSession {
        active_session_id: field("activeSessionId")?,
        session_id: field("sessionId")?,
        session_file: field("sessionFile")?,
    })
}

/// Attach to `active_session_id` with the interactive client's
/// capabilities; answers the attach data (with its `snapshot`).
///
/// # Errors
///
/// The attach request fails.
pub async fn attach(client: &DaemonClient, active_session_id: &str) -> anyhow::Result<Value> {
    client
        .request_ok(DaemonCommand::Attach {
            id: None,
            active_session_id: active_session_id.to_string(),
            client_id: None,
            capabilities: Some(ATTACH_CAPABILITIES.map(str::to_string).to_vec()),
            resume_cursor: None,
            recovery_config: None,
            env: None,
            launch_env: None,
            rest: Map::default(),
        })
        .await
        .context("attach to the session")
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
        let rules = |text: &str| format!("{SIGNAL_REPLY_RULES}\n\n{text}");
        let data = json!({ "sessions": [
            row("a", 0, None, Some("named"), "hello"),
            row("b", 1, Some("/s/a.jsonl"), None, "child"),
            row("c", 0, None, Some("  "), "first words"),
            row("d", 0, None, None, " "),
            row("e", 0, None, None, &rules("ask")),
            row("f", 0, None, None, SIGNAL_REPLY_RULES),
            row("g", 0, None, None, "[rules] kept"),
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
                session("e", Some("ask")),
                session("f", None),
                session("g", Some("[rules] kept")),
            ]
        );
    }
}
