//! The agent family from the main prompt: `@name message` talks to one
//! agent of this session's family instead of the main model, `/agents`
//! prints the family inline, relayed peer messages land as dim rows, and
//! the prompt's `@` completions offer the family's names.
//!
//! `@` at prompt start is shared with the file mentions. The prompt routes
//! to an agent only when its first word is `@<token>` (unquoted) and the
//! token names an agent of the family (see [`crate::swarm_block`] for the
//! name forms). An `@token` that names no agent but an existing path is
//! a file mention and goes to the model as before; anything else is an
//! unknown agent: an error row, and the text stays in the editor.

use eukhe_types::daemon::{AgentRelayEvent, StreamingBehavior};

use super::{AgentView, ChatEntry, SessionUi, SubmitBehavior};
use crate::agent_delivery::{
    deliver_agent_message, resume_config_for, steer_when_streaming, AgentDelivery,
};
use crate::swarm_block::{
    agent_name, family_members, mention_items, resolve_agent, roster_lines, AgentLookup, SwarmRow,
};

/// One settled `@name message` delivery (the backgrounded request's
/// fold-back).
#[derive(Debug)]
pub(crate) struct AgentMessageOutcome {
    /// The submit-time active id: the outcome applies only while the
    /// client still holds that session.
    pub(crate) active_session_id: String,
    /// The agent's display name.
    pub(crate) target: String,
    /// The submitted prompt (`@name message`): a failure restores it into
    /// an empty editor.
    pub(crate) draft: String,
    /// The resume's missing-directory notice on success; the daemon
    /// failure otherwise.
    pub(crate) result: Result<Option<String>, String>,
}

/// Whether the main prompt's leading `@token` was an agent message.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MentionRoute {
    /// Not an agent: the prompt continues to the main model.
    NotAgent,
    /// Routed to an agent, or refused with an error row.
    Handled,
}

/// The prompt's leading `@token` and the message after it; `None` when
/// the prompt does not start with an unquoted `@token`.
fn split_mention(text: &str) -> Option<(&str, &str)> {
    let rest = text.strip_prefix('@')?;
    if rest.starts_with('"') {
        return None;
    }
    let end = rest.find(char::is_whitespace).unwrap_or(rest.len());
    let token = &rest[..end];
    (!token.is_empty()).then(|| (token, rest[end..].trim()))
}

/// Whether `token` names an existing path below `cwd` (or an absolute or
/// `~` path): the file-mention reading of an `@token`.
fn names_path(cwd: &std::path::Path, token: &str) -> bool {
    let path = match token.strip_prefix("~/") {
        Some(rest) => eukhe_types::platform::home_dir()
            .unwrap_or_default()
            .join(rest),
        None => cwd.join(token),
    };
    path.exists()
}

impl SessionUi {
    /// The display name the family's `parent/child` paths use for this
    /// session: its roster row's name, else its own session name, else
    /// its active id.
    fn family_root_name(&self) -> String {
        let keys = self.family_identity().keys();
        self.roster
            .iter()
            .find(|entry| {
                crate::subagents::summary_identity_keys(&entry["summary"])
                    .iter()
                    .any(|key| keys.contains(key))
            })
            .and_then(|entry| {
                entry["summary"]
                    .get("sessionName")
                    .and_then(serde_json::Value::as_str)
                    .filter(|name| !name.is_empty())
                    .map(str::to_string)
            })
            .or_else(|| self.session_name.clone().filter(|name| !name.is_empty()))
            .unwrap_or_else(|| self.active_session_id.clone())
    }

    /// Route a prompt that starts with `@token` to the family agent it
    /// names (see the module docs for the file-mention rule).
    pub(super) fn route_agent_mention(
        &mut self,
        text: &str,
        behavior: SubmitBehavior,
        view: &mut AgentView,
    ) -> MentionRoute {
        let Some((token, message)) = split_mention(text) else {
            return MentionRoute::NotAgent;
        };
        let identity = self.family_identity();
        let root_name = self.family_root_name();
        let members = family_members(&self.roster, &identity);
        let (name, summary) = match resolve_agent(&members, &root_name, token) {
            AgentLookup::Found(entry) => (agent_name(entry), entry["summary"].clone()),
            AgentLookup::Ambiguous(paths) => {
                let choices = paths
                    .iter()
                    .map(|path| format!("@{path}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                view.editor.set_text(text);
                self.error_row(
                    &format!("@{token} names several agents; use one of {choices}"),
                    view,
                );
                return MentionRoute::Handled;
            }
            AgentLookup::Unknown if names_path(&self.cwd, token) => {
                return MentionRoute::NotAgent;
            }
            AgentLookup::Unknown => {
                view.editor.set_text(text);
                self.error_row(
                    &format!("No agent named @{token} in this session (/agents lists them)"),
                    view,
                );
                return MentionRoute::Handled;
            }
        };
        if message.is_empty() {
            view.editor.set_text(text);
            self.error_row(&format!("Usage: @{token} <message>"), view);
            return MentionRoute::Handled;
        }
        if let Some(error) = self.reconnection_failed.clone() {
            self.error_row(&format!("Daemon reconnection failed: {error}"), view);
            view.editor.set_text(text);
            return MentionRoute::Handled;
        }
        // The reply box's ladder: the follow-up key queues, Enter steers a
        // generating agent and wakes an idle one.
        let streaming = match behavior {
            SubmitBehavior::FollowUp => Some(StreamingBehavior::FollowUp),
            SubmitBehavior::Steer => steer_when_streaming(&summary),
        };
        let (resume_config, cwd_notice) =
            resume_config_for(&self.create_options().create_config(), &self.cwd, &summary);
        view.push_entry(ChatEntry::Swarm(Box::new(SwarmRow::Sent {
            to: name.clone(),
            text: message.to_string(),
        })));
        self.last_status_index = None;
        self.dirty = true;
        let client = self.client.clone();
        let notes = self.agent_message_notes.clone();
        let active_session_id = self.active_session_id.clone();
        let delivery = AgentDelivery {
            summary,
            text: message.to_string(),
            behavior: streaming,
            resume_config,
            // The answer comes back to this chat as `name -> you`.
            reply_to: Some(active_session_id.clone()),
        };
        let draft = text.to_string();
        tokio::spawn(async move {
            let result = deliver_agent_message(&client, delivery, || {})
                .await
                .map(|resumed| resumed.and(cwd_notice));
            let _ = notes.send(AgentMessageOutcome {
                active_session_id,
                target: name,
                draft,
                result,
            });
        });
        MentionRoute::Handled
    }

    /// Fold one settled `@name message` delivery: a failure is an error
    /// row and the draft returns to an empty editor; a resume into a
    /// fallback directory says so. A session switch since the submit
    /// drops it.
    pub(crate) fn apply_agent_message_outcome(
        &mut self,
        outcome: AgentMessageOutcome,
        view: &mut AgentView,
    ) {
        if outcome.active_session_id != self.active_session_id {
            return;
        }
        match outcome.result {
            Ok(None) => {}
            Ok(Some(notice)) => self.note(&notice, view),
            Err(error) => {
                self.error_row(
                    &format!("Message to {} failed: {error}", outcome.target),
                    view,
                );
                if view.editor.get_text().is_empty() {
                    view.editor.set_text(&outcome.draft);
                }
            }
        }
        self.dirty = true;
    }

    /// `/agents`: the family as inline rows (name, status, depth, model,
    /// note), tree-indented.
    pub(super) fn handle_agents_command(&mut self, args: &str, text: &str, view: &mut AgentView) {
        if !args.trim().is_empty() {
            view.editor.set_text(text);
            self.error_row("Usage: /agents", view);
            return;
        }
        let members = family_members(&self.roster, &self.family_identity());
        if members.is_empty() {
            self.note("This session has no agents.", view);
            return;
        }
        view.push_entry(ChatEntry::Swarm(Box::new(SwarmRow::Roster(roster_lines(
            &members,
        )))));
        self.last_status_index = None;
        self.dirty = true;
    }

    /// One relayed peer message: a dim transcript row.
    pub(super) fn apply_agent_relay(&mut self, relay: AgentRelayEvent, view: &mut AgentView) {
        view.push_entry(ChatEntry::Swarm(Box::new(SwarmRow::Relay(relay))));
        self.last_status_index = None;
        self.dirty = true;
    }

    /// Hand the family's names to the prompt's `@` completions.
    pub(super) fn refresh_agent_mentions(&self, view: &mut AgentView) {
        let members = family_members(&self.roster, &self.family_identity());
        let items = mention_items(&members, &self.family_root_name());
        view.editor.set_autocomplete_agent_mentions(items);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn only_an_unquoted_leading_token_is_a_mention() {
        assert_eq!(
            [
                split_mention("@worker-1 check the tests"),
                split_mention("@worker-1"),
                split_mention("@\"my file.txt\" explain"),
                split_mention("ask @worker-1"),
                split_mention("@ hello"),
            ],
            [
                Some(("worker-1", "check the tests")),
                Some(("worker-1", "")),
                None,
                None,
                None,
            ]
        );
    }
}
