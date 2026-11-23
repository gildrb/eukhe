//! The work in flight an older daemon shows, read through its `list` of
//! resident sessions. A client that replaces an older daemon reads it to
//! decide whether a refused idle shutdown means work: a 0.10.78 supervisor
//! counts a worker that does not answer its quiesce in time (a hung child
//! worker whose parent is gone) as busy, while its `list` shows every
//! session idle. The rows are read as plain JSON, field by field, so the
//! reading holds across schema revisions (0.10.78's rows included); a
//! field a row lacks shows no work.

use anyhow::{anyhow, Result};
use eukhe_types::daemon::DaemonCommand;
use serde_json::Value;

use crate::daemon_client::DaemonClient;

/// How many sessions a line names before it counts the rest.
const NAMED_SESSIONS: usize = 3;

/// The longest session label a line shows, in chars.
const LABEL_CHARS: usize = 40;

/// The work in flight on the daemon `client` is connected to, one entry
/// per resident session that holds some (`a turn in "fix tests"`); empty
/// when every resident session is idle. A list the daemon does not answer
/// is one entry: unknown never reads idle.
pub async fn in_flight(client: &DaemonClient) -> Vec<String> {
    match listed_sessions(client).await {
        Ok(sessions) => work_in(&sessions),
        Err(error) => vec![format!("an answer to its session list ({error:#})")],
    }
}

/// The resident sessions' summaries (`list` without `all`: the live
/// residents only, the workers a stop of the daemon reaches).
async fn listed_sessions(client: &DaemonClient) -> Result<Vec<Value>> {
    let response = client
        .request(DaemonCommand::List {
            id: None,
            all: None,
            cwd: None,
            session_dir: None,
            include_client_owned: None,
            rest: serde_json::Map::default(),
        })
        .await?;
    if !response.success {
        return Err(anyhow!(
            "{}",
            response.error.unwrap_or_else(|| "list failed".to_string())
        ));
    }
    match response
        .data
        .and_then(|mut data| data.get_mut("sessions").map(Value::take))
    {
        Some(Value::Array(sessions)) => Ok(sessions),
        _ => Err(anyhow!("the list carried no sessions")),
    }
}

/// The work in flight in `sessions` (session summaries), one entry per
/// session that holds some.
#[must_use]
pub fn work_in(sessions: &[Value]) -> Vec<String> {
    sessions
        .iter()
        .filter_map(|session| {
            work_of(session).map(|work| format!("{work} in \"{}\"", label_of(session)))
        })
        .collect()
}

/// The work one session summary shows, if any: a run (streaming, running
/// tools, retrying a provider, parked on a usage limit), a compaction, a
/// user shell command, running subagents, or the background work its turn
/// left (jobs, kernel commands, children, workflow runs).
fn work_of(session: &Value) -> Option<&'static str> {
    let flag = |key: &str| session.get(key).and_then(Value::as_bool) == Some(true);
    let present = |key: &str| session.get(key).is_some_and(|value| !value.is_null());
    if flag("isCompacting") {
        Some("a compaction")
    } else if flag("isBashRunning") {
        Some("a shell command")
    } else if flag("isQuotaParked") {
        Some("a turn waiting out a usage limit")
    } else if present("retry") {
        Some("a turn retrying its provider")
    } else if flag("isStreaming")
        || flag("isRunningTools")
        || session.get("activity").and_then(Value::as_str) == Some("working")
    {
        Some("a turn")
    } else if flag("hasRunningSubagents") {
        Some("running subagents")
    } else if present("waitingOn") {
        Some("background work")
    } else {
        None
    }
}

/// What a line calls a session: its name, else its first message, else its
/// id; at most [`LABEL_CHARS`] chars.
fn label_of(session: &Value) -> String {
    let text = |key: &str| {
        session
            .get(key)
            .and_then(Value::as_str)
            .map(str::trim)
            .filter(|text| !text.is_empty())
    };
    let label = text("sessionName")
        .or_else(|| text("firstMessage"))
        .or_else(|| text("id"))
        .unwrap_or("a session");
    let label = label.lines().next().unwrap_or(label);
    match label.char_indices().nth(LABEL_CHARS) {
        Some((end, _)) => format!("{}...", &label[..end]),
        None => label.to_string(),
    }
}

/// The entries of `work` as one phrase: the first [`NAMED_SESSIONS`], then
/// how many more.
#[must_use]
pub fn describe(work: &[String]) -> String {
    let named = work
        .iter()
        .take(NAMED_SESSIONS)
        .cloned()
        .collect::<Vec<_>>();
    match work.len().saturating_sub(NAMED_SESSIONS) {
        0 => match named.split_last() {
            Some((last, [])) => last.clone(),
            Some((last, rest)) => format!("{} and {last}", rest.join(", ")),
            None => String::new(),
        },
        more => format!("{}, and {more} more", named.join(", ")),
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    /// An idle row as a 0.10.78 supervisor lists it, and the recovering
    /// row it lists for a worker that does not answer.
    fn idle(name: &str) -> Value {
        json!({
            "id": "711a6f152319", "lifecycle": "live", "activity": "idle",
            "isSessionActive": false, "sessionName": name, "isStreaming": false,
            "isCompacting": false, "isQuotaParked": false, "isBashRunning": false,
            "isRunningTools": false, "hasRunningSubagents": false,
            "attachedClients": 0, "messageCount": 4,
        })
    }

    #[test]
    fn idle_and_recovering_rows_hold_no_work() {
        let recovering = json!({
            "id": "21e8a8e407b4", "lifecycle": "recovering", "activity": "idle",
            "isSessionActive": false, "sessionId": "", "cwd": "",
            "isStreaming": false, "isCompacting": false, "attachedClients": 0,
        });
        assert_eq!(work_in(&[idle("docs"), recovering]), Vec::<String>::new());
    }

    #[test]
    fn each_kind_of_work_is_named_with_its_session() {
        let with = |key: &str, value: Value| {
            let mut row = idle("fix tests");
            row[key] = value;
            row
        };
        let mut untitled = with("isStreaming", json!(true));
        untitled.as_object_mut().expect("row").remove("sessionName");
        untitled["firstMessage"] =
            json!("refactor the launcher so that it waits for work to settle\nmore");
        assert_eq!(
            work_in(&[
                with("isStreaming", json!(true)),
                with("activity", json!("working")),
                with("isCompacting", json!(true)),
                with("isBashRunning", json!(true)),
                with("isQuotaParked", json!(true)),
                with("retry", json!({"attempt": 1})),
                with("hasRunningSubagents", json!(true)),
                with("waitingOn", json!({"jobs": 1})),
                with("waitingOn", Value::Null),
                untitled,
            ]),
            [
                "a turn in \"fix tests\"",
                "a turn in \"fix tests\"",
                "a compaction in \"fix tests\"",
                "a shell command in \"fix tests\"",
                "a turn waiting out a usage limit in \"fix tests\"",
                "a turn retrying its provider in \"fix tests\"",
                "running subagents in \"fix tests\"",
                "background work in \"fix tests\"",
                "a turn in \"refactor the launcher so that it waits f...\"",
            ]
        );
    }

    #[test]
    fn a_phrase_names_three_sessions_then_counts() {
        let work = |count: usize| {
            (0..count)
                .map(|at| format!("a turn in \"s{at}\""))
                .collect::<Vec<_>>()
        };
        assert_eq!(
            [1, 2, 3, 5].map(|count| describe(&work(count))),
            [
                "a turn in \"s0\"",
                "a turn in \"s0\" and a turn in \"s1\"",
                "a turn in \"s0\", a turn in \"s1\" and a turn in \"s2\"",
                "a turn in \"s0\", a turn in \"s1\", a turn in \"s2\", and 2 more",
            ]
        );
    }
}
