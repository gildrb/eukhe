//! What the goal extension's hooks and host requests share, and the
//! `goal.get` / `goal.create` / `goal.complete` kernel host requests (port of
//! `session_engine/host_requests.rs`'s `handle_goal_host_request`).

use std::sync::Arc;

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::harness::Conversation;
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::ConversationId;
use futures::FutureExt;
use serde_json::Value;

use super::ops::{conversation_of, goal_state, update_goal};
use super::state::{completed, new_goal};
use crate::autonomous::GateCommandRunner;
use crate::durable::{HarnessCell, HostCall, HostRequestRegistry};
use crate::goals::{goal_host_response, GoalStatus};

/// The services of the goal extension: the session's Harness and the runner
/// of autonomous quality gates.
#[derive(Clone)]
pub(crate) struct GoalsHost {
    pub(crate) harness: HarnessCell,
    pub(crate) gates: Arc<dyn GateCommandRunner>,
}

impl GoalsHost {
    /// The conversation `conversation_id` of the open Harness.
    pub(crate) async fn conversation(
        &self,
        conversation_id: ConversationId,
        cx: &Context,
    ) -> SessionResult<Conversation> {
        conversation_of(&self.harness.require()?, conversation_id, cx).await
    }

    /// The conversation a host request targets: the executing tool call's
    /// conversation, else the root.
    fn call_conversation(&self, call: &HostCall) -> SessionResult<ConversationTarget> {
        match &call.call {
            Some(api) => Ok(ConversationTarget::Id(api.conversation_id())),
            None => self
                .harness
                .root()
                .map(ConversationTarget::Root)
                .ok_or_else(|| SessionError::error("Harness is closed")),
        }
    }

    async fn target(&self, call: &HostCall, cx: &Context) -> SessionResult<Conversation> {
        match self.call_conversation(call)? {
            ConversationTarget::Id(id) => self.conversation(id, cx).await,
            ConversationTarget::Root(root) => Ok(root),
        }
    }

    async fn handle(&self, request: GoalRequest, call: HostCall) -> anyhow::Result<Value> {
        let cx = BACKGROUND_CONTEXT.clone();
        let conversation = self.target(&call, &cx).await?;
        let response = match request {
            GoalRequest::Get => {
                let harness = self.harness.require()?;
                goal_host_response(&goal_state(&harness, conversation.id(), &cx).await?, false)
            }
            GoalRequest::Create => {
                let record = call.data.as_object().cloned().unwrap_or_default();
                let Some(objective) = record.get("objective").and_then(Value::as_str) else {
                    anyhow::bail!("goal.create objective must be a string");
                };
                let token_budget = match record.get("token_budget") {
                    None | Some(Value::Null) => None,
                    Some(value) => Some(value.as_u64().ok_or_else(|| {
                        anyhow::anyhow!("goal.create token_budget must be an integer when provided")
                    })?),
                };
                let objective = objective.to_owned();
                let (goal, _) = update_goal(
                    &conversation,
                    move |current, now| {
                        if let Some(refusal) = create_refusal(current.status) {
                            return Err(refusal);
                        }
                        let goal = new_goal(&objective, token_budget, now)
                            .map_err(|error| SessionError::error(format!("{error:#}")))?;
                        Ok(Some((goal, None)))
                    },
                    &cx,
                )
                .await?;
                goal_host_response(&goal, false)
            }
            GoalRequest::Complete => {
                let (goal, _) = update_goal(
                    &conversation,
                    |current, _| match completed(current) {
                        Some(goal) => Ok(Some((goal, None))),
                        None => Err(SessionError::error(
                            "cannot complete goal because this thread has no goal",
                        )),
                    },
                    &cx,
                )
                .await?;
                goal_host_response(&goal, true)
            }
        };
        Ok(serde_json::to_value(response)?)
    }
}

enum ConversationTarget {
    Id(ConversationId),
    Root(Conversation),
}

#[derive(Clone, Copy)]
enum GoalRequest {
    Get,
    Create,
    Complete,
}

/// Why `goal.create` refuses while a goal exists (old
/// `create_goal_from_host`); idle and terminal goals start fresh.
fn create_refusal(status: GoalStatus) -> Option<SessionError> {
    let message = match status {
        GoalStatus::Active => {
            "cannot create a new goal because this thread already has an active goal; run `await goal.complete()` when it is achieved, or ask the user to clear it with /goal clear"
        }
        GoalStatus::Paused => {
            "cannot create a new goal because a paused goal exists; ask the user to resume it with /goal resume or clear it with /goal clear"
        }
        GoalStatus::BudgetLimited => {
            "cannot create a new goal because a budget-limited goal exists; ask the user to resume it with /goal resume or clear it with /goal clear"
        }
        GoalStatus::Idle | GoalStatus::Complete | GoalStatus::Error => return None,
    };
    Some(SessionError::error(message))
}

/// Register `goal.get`, `goal.create`, and `goal.complete`.
pub(crate) fn register_host_requests(host: &GoalsHost, registry: &HostRequestRegistry) {
    for (request_type, request) in [
        ("goal.get", GoalRequest::Get),
        ("goal.create", GoalRequest::Create),
        ("goal.complete", GoalRequest::Complete),
    ] {
        let host = host.clone();
        registry.register(
            request_type,
            Arc::new(move |call: HostCall| {
                let host = host.clone();
                async move { host.handle(request, call).await }.boxed()
            }),
        );
    }
}
