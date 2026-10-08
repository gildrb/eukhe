//! The queue command surface: `mutate_queued_message` and `resume_queue`
//! (TS daemon-mode `case "mutate_queued_message"` / `case "resume_queue"`).
//!
//! The queue is the visible projection: the main conversation's queued
//! inbox inputs (durable submissions) followed by the inputs an `abort`
//! suspended. A mutation addresses one preview by `lane` + `index` +
//! `expectedText`; the status vocabulary is TS-verbatim (`applied`,
//! `rejected`). A queued submission cannot be edited in place: a delete
//! withdraws it, a replace or move withdraws the affected submissions and
//! admits them again in the new order.

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_durable::harness::types::{InputSubmissionDraft, WhenBusy};
use eukhe_durable::harness::AbortSubmissionResult;
use eukhe_types::pi_ai::{TextContent, UserContent, UserContentBlock};
use serde_json::{json, Value};

use crate::protocol::{response_failure, response_success, DaemonResponse};
use crate::worker::durable_host::bridge::{content_preview, QueuedInput, QueuedMode};
use crate::worker::durable_host::suspended::{SuspendedState, WithdrawnInput};
use crate::worker::set_withdrawn;
use crate::worker::{HostedSession, Worker};

const COMMAND: &str = "mutate_queued_message";

/// TS `QueuedMessageLane`: wire names `"steering"` and `"followUp"`.
fn wire_lane(value: Option<&Value>) -> Option<QueuedMode> {
    match value.and_then(Value::as_str) {
        Some("steering") => Some(QueuedMode::Steer),
        Some("followUp") => Some(QueuedMode::FollowUp),
        _ => None,
    }
}

/// Where a queued input lives.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Origin {
    Inbox,
    /// An abort suspended it or an input-pause lease holds it.
    Withdrawn,
}

/// One parsed mutation.
enum Mutation {
    Delete,
    Move {
        direction: i64,
    },
    Replace {
        content: UserContent,
        text: String,
        lane: Option<QueuedMode>,
    },
}

impl Mutation {
    fn parse(mutation: &Value) -> Result<Self, &'static str> {
        match mutation.get("type").and_then(Value::as_str) {
            Some("delete") => Ok(Self::Delete),
            Some("move") => Ok(Self::Move {
                direction: mutation
                    .get("direction")
                    .and_then(Value::as_i64)
                    .unwrap_or(0),
            }),
            Some("replace") => {
                let text = mutation
                    .get("text")
                    .and_then(Value::as_str)
                    .unwrap_or_default()
                    .to_string();
                let images = crate::worker::parse_prompt_images(mutation);
                let content = if images.is_empty() {
                    UserContent::Text(text.clone())
                } else {
                    let mut blocks = vec![UserContentBlock::Text(TextContent::new(text.clone()))];
                    blocks.extend(images.into_iter().map(UserContentBlock::Image));
                    UserContent::Blocks(blocks)
                };
                Ok(Self::Replace {
                    content,
                    text,
                    lane: wire_lane(mutation.get("lane")),
                })
            }
            _ => Err(
                "mutate_queued_message requires mutation.type \"delete\", \"move\", or \"replace\"",
            ),
        }
    }
}

impl Worker {
    /// `mutate_queued_message { lane, index, expectedText, mutation }`.
    /// Rejections are statuses, not errors; only a malformed request fails.
    pub(crate) async fn handle_mutate_queued_message(&self, payload: &Value) -> DaemonResponse {
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let Some(lane) = wire_lane(payload.get("lane")) else {
            return response_failure(
                None,
                COMMAND,
                "mutate_queued_message requires lane \"steering\" or \"followUp\"",
                None,
            );
        };
        let Some(index) = payload
            .get("index")
            .and_then(Value::as_u64)
            .and_then(|index| usize::try_from(index).ok())
        else {
            return response_failure(
                None,
                COMMAND,
                "mutate_queued_message requires an index",
                None,
            );
        };
        let expected = payload
            .get("expectedText")
            .and_then(Value::as_str)
            .unwrap_or_default();
        let Some(mutation) = payload.get("mutation") else {
            return response_failure(
                None,
                COMMAND,
                "mutate_queued_message requires a mutation",
                None,
            );
        };
        let mutation = match Mutation::parse(mutation) {
            Ok(mutation) => mutation,
            Err(error) => return response_failure(None, COMMAND, error, None),
        };
        let status = match self
            .mutate_queue(&hosted, lane, index, expected, mutation)
            .await
        {
            Ok(status) => status,
            Err(error) => return response_failure(None, COMMAND, &error, None),
        };
        if status == "applied" {
            self.emit_action_update();
        }
        response_success(None, COMMAND, Some(json!({ "status": status })))
    }

    async fn mutate_queue(
        &self,
        hosted: &HostedSession,
        lane: QueuedMode,
        index: usize,
        expected: &str,
        mutation: Mutation,
    ) -> Result<&'static str, String> {
        // The queue as the client saw it: inbox inputs, then the
        // withdrawn ones (suspended and held keep their membership).
        let (inbox, withdrawn) = {
            let core = self
                .core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            (
                core.view
                    .as_ref()
                    .map(|view| view.inbox.clone())
                    .unwrap_or_default(),
                core.suspended
                    .iter()
                    .cloned()
                    .chain(core.held.iter().cloned())
                    .collect::<Vec<QueuedInput>>(),
            )
        };
        let mut queue: Vec<(Origin, QueuedInput)> = inbox
            .into_iter()
            .map(|input| (Origin::Inbox, input))
            .chain(
                withdrawn
                    .into_iter()
                    .map(|input| (Origin::Withdrawn, input)),
            )
            .collect();
        let positions: Vec<usize> = queue
            .iter()
            .enumerate()
            .filter(|(_, (_, input))| input.mode == lane)
            .map(|(position, _)| position)
            .collect();
        let Some(&position) = positions.get(index) else {
            return Ok("rejected");
        };
        if queue[position].1.text != expected {
            return Ok("rejected");
        }
        let original = queue.clone();
        match mutation {
            Mutation::Delete => {
                queue.remove(position);
            }
            Mutation::Move { direction } => {
                let target = i64::try_from(index)
                    .ok()
                    .and_then(|index| index.checked_add(direction))
                    .and_then(|target| usize::try_from(target).ok());
                let Some(&other) = target.and_then(|target| positions.get(target)) else {
                    return Ok("rejected");
                };
                if direction == 0 {
                    return Ok("rejected");
                }
                queue.swap(position, other);
            }
            Mutation::Replace {
                content,
                text,
                lane: target,
            } => {
                let (_, input) = &mut queue[position];
                input.content = content;
                input.text = if text.is_empty() {
                    content_preview(&input.content)
                } else {
                    text
                };
                if let Some(target) = target.filter(|target| *target != lane) {
                    // A lane change moves the item to the back of the queue.
                    let item = queue.remove(position);
                    queue.push((
                        item.0,
                        QueuedInput {
                            mode: target,
                            ..item.1
                        },
                    ));
                }
            }
        }
        self.apply_queue(hosted, &original, queue).await
    }

    /// Make the queue `next`: withdraw the inbox submissions from the first
    /// changed position on and admit them again in order; suspended inputs
    /// stay suspended in their new order.
    async fn apply_queue(
        &self,
        hosted: &HostedSession,
        original: &[(Origin, QueuedInput)],
        next: Vec<(Origin, QueuedInput)>,
    ) -> Result<&'static str, String> {
        let unchanged = original
            .iter()
            .zip(&next)
            .take_while(|((_, before), (_, after))| before == after)
            .count();
        let main = hosted.main().map_err(|error| error.to_string())?;
        // Withdraw every inbox submission from the first difference on.
        for (origin, input) in &original[unchanged..] {
            if *origin != Origin::Inbox {
                continue;
            }
            match hosted
                .harness()
                .abort_submission(input.id, Some(main.id()), &BACKGROUND_CONTEXT)
                .await
                .map_err(|error| error.to_string())?
            {
                AbortSubmissionResult::Aborted => {}
                // A run already placed it: the queue moved under the edit.
                AbortSubmissionResult::AlreadyPlaced
                | AbortSubmissionResult::Settled
                | AbortSubmissionResult::NotFound => {
                    return Ok("rejected");
                }
            }
        }
        // The reordered withdrawn inputs keep each one's membership
        // (abort-suspended vs pause-held), and the durable store follows.
        let held_ids: std::collections::HashSet<_> = {
            let core = self
                .core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            core.held.iter().map(|input| input.id).collect()
        };
        let mut withdrawn = Vec::new();
        for (index, (origin, input)) in next.into_iter().enumerate() {
            match origin {
                Origin::Withdrawn => withdrawn.push(input),
                Origin::Inbox if index >= unchanged => {
                    main.submit(
                        InputSubmissionDraft {
                            request_id: None,
                            content: input.content,
                            when_busy: Some(match input.mode {
                                QueuedMode::Steer => WhenBusy::Steer,
                                QueuedMode::FollowUp => WhenBusy::FollowUp,
                            }),
                        },
                        &BACKGROUND_CONTEXT,
                    )
                    .await
                    .map_err(|error| error.to_string())?;
                }
                Origin::Inbox => {}
            }
        }
        let (suspended, held): (Vec<QueuedInput>, Vec<QueuedInput>) = withdrawn
            .into_iter()
            .partition(|input| !held_ids.contains(&input.id));
        let state = SuspendedState {
            suspended: suspended.iter().map(WithdrawnInput::from).collect(),
            held: held.iter().map(WithdrawnInput::from).collect(),
        };
        set_withdrawn(hosted, &self.core, &self.events, state).await?;
        Ok("applied")
    }

    /// `resume_queue`: the inputs an abort suspended are admitted again;
    /// the failure string is TS-verbatim for the empty queue.
    pub(crate) async fn handle_resume_queue(&self) -> DaemonResponse {
        const RESUME: &str = "resume_queue";
        let hosted = match self.hosted(RESUME) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let resumed = match self.resume_suspended_inputs(&hosted).await {
            Ok(resumed) => resumed,
            Err(error) => return response_failure(None, RESUME, &error, None),
        };
        let queued = self
            .core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .view
            .as_ref()
            .is_some_and(|view| !view.inbox.is_empty());
        if !resumed && !queued {
            return response_failure(None, RESUME, "No queued work to resume", None);
        }
        response_success(None, RESUME, None)
    }
}
