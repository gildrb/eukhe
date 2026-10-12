//! Delivering one user message to another agent of the family: the
//! agents view's reply box and the main prompt's `@name message` share
//! it. A generating target is steered, an idle one gets a plain prompt
//! (its next turn), and a saved target without a live runtime resumes
//! into the daemon first (`create` with the resume config).

use serde_json::Value;

use crate::daemon_client::DaemonClient;
use eukhe_types::daemon::{DaemonCommand, PromptInput, StreamingBehavior};

/// One message for one agent: the CURRENT summary the send resolves
/// to, the text, the streaming behavior, the resume config the saved
/// path's create carries, and the session (live id) the agent's answer
/// returns to as an `agent_reply` row.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct AgentDelivery {
    pub(crate) summary: Value,
    pub(crate) text: String,
    pub(crate) behavior: Option<StreamingBehavior>,
    pub(crate) resume_config: Value,
    pub(crate) reply_to: Option<String>,
}

/// The summary's live runtime id (`activeSessionId`, non-empty).
fn live_id(summary: &Value) -> Option<String> {
    summary
        .get("activeSessionId")
        .and_then(Value::as_str)
        .filter(|id| !id.is_empty())
        .map(str::to_string)
}

/// TS `sendReply`'s ladder: a live target that is streaming is steered;
/// anything else takes the plain prompt (an idle agent wakes on it).
#[must_use]
pub(crate) fn steer_when_streaming(summary: &Value) -> Option<StreamingBehavior> {
    (summary.get("activeSessionId").is_some()
        && summary.get("isStreaming").and_then(Value::as_bool) == Some(true))
    .then_some(StreamingBehavior::Steer)
}

/// TS `createAgentsViewResumeConfig` + `resolveAgentsViewOpenCwd`
/// (:225-236 + :493-504): the base create config with the saved
/// session's cwd removed -- or overridden with `fallback_cwd` (and its
/// notice) when the saved directory no longer exists.
#[must_use]
pub(crate) fn resume_config_for(
    base: &Value,
    fallback_cwd: &std::path::Path,
    summary: &Value,
) -> (Value, Option<String>) {
    let mut config = base.clone();
    let saved_cwd = summary
        .get("cwd")
        .and_then(Value::as_str)
        .filter(|cwd| !cwd.is_empty());
    let exists = saved_cwd.is_some_and(|cwd| std::path::Path::new(cwd).exists());
    let fallback = fallback_cwd.to_string_lossy().to_string();
    let notice = if saved_cwd.is_none_or(|_| exists) {
        None
    } else {
        Some(format!(
            "Original directory is missing ({}); opened in {fallback} instead.",
            saved_cwd.unwrap_or_default()
        ))
    };
    if notice.is_some() {
        config["cwd"] = serde_json::json!(fallback);
    } else if let Some(object) = config.as_object_mut() {
        object.remove("cwd");
    }
    (config, notice)
}

/// Deliver one message (TS `sendReply`, :1981-2026): a saved target
/// resumes first, and `before_prompt` runs once the target is live, right
/// before the prompt; the answer is the resumed summary (`None` for a
/// live target).
pub(crate) async fn deliver_agent_message(
    client: &DaemonClient,
    delivery: AgentDelivery,
    before_prompt: impl FnOnce() + Send,
) -> Result<Option<Value>, String> {
    let mut resumed = None;
    let active_session_id = if let Some(id) = live_id(&delivery.summary) {
        id
    } else {
        let Some(session_path) = delivery
            .summary
            .get("sessionFile")
            .and_then(Value::as_str)
            .filter(|path| !path.is_empty())
            .map(str::to_string)
        else {
            return Err("Cannot resume a session without a saved session file".to_string());
        };
        // The resumed session runs in THIS pane: the create carries the
        // client's Herdr pane identity like every create (a client
        // outside a Herdr pane sends nothing -- the wire keeps its shape).
        let client_env = {
            let env =
                eukhe_types::daemon::herdr_env::collect_client_env(|key| std::env::var(key).ok());
            (!env.is_empty()).then_some(env)
        };
        let created = client
            .request(DaemonCommand::Create {
                id: None,
                session_path: Some(session_path),
                continue_recent: None,
                no_session: None,
                name: None,
                config: Some(delivery.resume_config.clone()),
                runtime_metadata: None,
                lifecycle: None,
                env: client_env,
                launch_env: None,
                rest: serde_json::Map::default(),
            })
            .await;
        let summary = match created {
            Ok(response) if response.success => response.data.unwrap_or(Value::Null),
            Ok(response) => {
                return Err(response
                    .error
                    .unwrap_or_else(|| "the command failed".into()))
            }
            Err(error) => return Err(format!("{error:#}")),
        };
        let Some(active) = live_id(&summary) else {
            return Err("Daemon returned a session without an active session id".to_string());
        };
        resumed = Some(summary);
        active
    };
    before_prompt();
    let prompt = client
        .request(DaemonCommand::Prompt {
            id: None,
            active_session_id,
            message: delivery.text,
            input: PromptInput {
                content: None,
                images: None,
                streaming_behavior: delivery.behavior,
                queue_if_busy: None,
                expand_prompt_templates: None,
                source: None,
                agent_message_id: None,
                custom_message: None,
                queue_key: None,
                prefix_messages: None,
                admission_id: None,
                rlm_notice_nonce: None,
                reply_to: delivery.reply_to,
            },
            rest: serde_json::Map::default(),
        })
        .await;
    match prompt {
        Ok(response) if response.success => Ok(resumed),
        Ok(response) => Err(response
            .error
            .unwrap_or_else(|| "the command failed".into())),
        Err(error) => Err(format!("{error:#}")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn streaming_live_targets_steer_and_idle_ones_take_the_plain_prompt() {
        let streaming = json!({ "activeSessionId": "w1", "isStreaming": true });
        let idle = json!({ "activeSessionId": "w1", "isStreaming": false });
        let saved = json!({ "sessionFile": "/s/w1.jsonl", "isStreaming": true });
        assert_eq!(
            [
                steer_when_streaming(&streaming),
                steer_when_streaming(&idle),
                steer_when_streaming(&saved),
            ],
            [Some(StreamingBehavior::Steer), None, None]
        );
    }

    #[test]
    fn the_resume_config_drops_an_existing_cwd_and_overrides_a_missing_one() {
        let base = json!({ "cwd": "/view", "sessionDir": "/sessions" });
        let dir = tempfile::TempDir::new().expect("temp dir");
        let existing = json!({ "cwd": dir.path().to_string_lossy() });
        assert_eq!(
            resume_config_for(&base, std::path::Path::new("/view"), &existing),
            (json!({ "sessionDir": "/sessions" }), None)
        );
        let missing = json!({ "cwd": "/gone/dir" });
        assert_eq!(
            resume_config_for(&base, std::path::Path::new("/view"), &missing),
            (
                json!({ "cwd": "/view", "sessionDir": "/sessions" }),
                Some(
                    "Original directory is missing (/gone/dir); opened in /view instead."
                        .to_string()
                )
            )
        );
    }
}
