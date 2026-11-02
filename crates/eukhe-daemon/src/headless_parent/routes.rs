//! The supervisor side: the registered headless parents, their roster
//! rows, the `send_message` route to them, and the end of a registration
//! (the connection closed: the parent left, so its resident children
//! close like a dead parent worker's).

use std::collections::HashMap;
use std::path::Path;
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use eukhe_types::daemon::DaemonCommand;
use serde_json::{json, Value};
use tokio::sync::{mpsc, oneshot};

use super::DELIVERY_FRAME;
use crate::protocol::{response_failure, response_success, DaemonResponse};
use crate::supervisor::{Outbound, Supervisor};

/// The outbound queue of one client connection (its responses and the
/// frames pushed to it).
pub(crate) type ConnectionOutbound = mpsc::Sender<(Vec<Outbound>, bool)>;

/// One registered headless parent.
struct Registered {
    /// The connection the registration lives on.
    connection_id: String,
    /// Its roster row (the supervisor summary shape).
    summary: Value,
    outbound: ConnectionOutbound,
}

/// A delivery waiting for the parent's receipt.
struct Pending {
    parent: String,
    connection_id: String,
    answer: oneshot::Sender<Answer>,
}

/// A parent's answer to one delivery.
enum Answer {
    Receipt(Value),
    Refused(String),
}

/// The headless parents registered on this supervisor (keyed by session
/// id, which is their live session id) and the deliveries they owe a
/// receipt for.
#[derive(Default)]
pub(crate) struct HeadlessParents {
    parents: Mutex<HashMap<String, Registered>>,
    deliveries: Mutex<HashMap<String, Pending>>,
}

/// A registered parent a message is routed to.
pub(crate) struct HeadlessTarget {
    pub(crate) session_id: String,
    /// The parent's storage (`None`: a memory session).
    pub(crate) session_file: Option<std::path::PathBuf>,
    outbound: ConnectionOutbound,
}

/// A registered parent sending a message to one of its children.
pub(crate) struct HeadlessSender {
    pub(crate) session_id: String,
    /// The parent's storage (`None`: a memory session).
    pub(crate) session_file: Option<std::path::PathBuf>,
    /// Its roster row (the sender endpoint).
    pub(crate) summary: Value,
}

impl HeadlessParents {
    fn parents(&self) -> std::sync::MutexGuard<'_, HashMap<String, Registered>> {
        self.parents.lock().unwrap_or_else(PoisonError::into_inner)
    }

    fn deliveries(&self) -> std::sync::MutexGuard<'_, HashMap<String, Pending>> {
        self.deliveries
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
    }

    /// The registered parent `selector` (its session id) names.
    pub(crate) fn target(&self, selector: &str) -> Option<HeadlessTarget> {
        self.parents().get(selector).map(|parent| HeadlessTarget {
            session_id: selector.to_string(),
            session_file: parent
                .summary
                .get("sessionFile")
                .and_then(Value::as_str)
                .map(std::path::PathBuf::from),
            outbound: parent.outbound.clone(),
        })
    }

    /// The registered parent `selector` (its session id) names, as the
    /// sender of an agent message.
    pub(crate) fn sender(&self, selector: &str) -> Option<HeadlessSender> {
        self.parents().get(selector).map(|parent| HeadlessSender {
            session_id: selector.to_string(),
            session_file: parent
                .summary
                .get("sessionFile")
                .and_then(Value::as_str)
                .map(std::path::PathBuf::from),
            summary: parent.summary.clone(),
        })
    }

    /// The roster rows of the registered parents (the supervisor summary
    /// shape), each with its session file when it has one.
    pub(crate) fn rows(&self) -> Vec<Value> {
        self.parents()
            .values()
            .map(|parent| parent.summary.clone())
            .collect()
    }

    /// Whether a registered parent's storage is `session_file`.
    pub(crate) fn hosts_file(&self, session_file: &Path) -> bool {
        let wanted = crate::lease::canonical_session_path(session_file);
        self.parents().values().any(|parent| {
            parent
                .summary
                .get("sessionFile")
                .and_then(Value::as_str)
                .is_some_and(|file| crate::lease::canonical_session_path(Path::new(file)) == wanted)
        })
    }

    /// Drop the registrations of `connection_id` and fail the deliveries
    /// they owe; returns the parents that left.
    fn leave(&self, connection_id: &str) -> Vec<String> {
        let left: Vec<String> = {
            let mut parents = self.parents();
            let left = parents
                .iter()
                .filter(|(_, parent)| parent.connection_id == connection_id)
                .map(|(id, _)| id.clone())
                .collect::<Vec<_>>();
            for id in &left {
                parents.remove(id);
            }
            left
        };
        // Dropping a pending answer ends its wait as a departure.
        self.deliveries()
            .retain(|_, pending| !left.contains(&pending.parent));
        left
    }
}

impl Supervisor {
    /// `register_headless_parent`: the session the command names joins the
    /// roster as a client-hosted parent, for the life of `connection_id`
    /// (whose outbound queue is `outbound`).
    #[tracing::instrument(level = "debug", skip_all, fields(connection = connection_id))]
    pub(crate) async fn handle_register_headless_parent(
        &self,
        command: &DaemonCommand,
        connection_id: &str,
        outbound: &ConnectionOutbound,
        command_id: &str,
        type_name: &str,
    ) -> DaemonResponse {
        let DaemonCommand::RegisterHeadlessParent {
            session_id,
            session_name,
            session_file,
            cwd,
            ..
        } = command
        else {
            return response_failure(Some(command_id), type_name, "invalid command", None);
        };
        if session_id.is_empty() {
            return response_failure(
                Some(command_id),
                type_name,
                "A headless parent needs its session id",
                None,
            );
        }
        if self.registry.resolve(session_id).await.is_ok() {
            return response_failure(
                Some(command_id),
                type_name,
                &format!("Session {session_id} is hosted by a daemon worker"),
                None,
            );
        }
        let mut summary = json!({
            "id": session_id,
            "activeSessionId": session_id,
            "sessionId": session_id,
            "cwd": cwd,
            "runtimeKind": "top-level",
            "rlmDepth": 0,
        });
        if let Some(name) = session_name.as_deref().filter(|name| !name.is_empty()) {
            summary["sessionName"] = json!(name);
        }
        if let Some(file) = session_file.as_deref().filter(|file| !file.is_empty()) {
            summary["sessionFile"] = json!(file);
        }
        self.headless_parents.parents().insert(
            session_id.clone(),
            Registered {
                connection_id: connection_id.to_string(),
                summary,
                outbound: outbound.clone(),
            },
        );
        self.log_line(&format!(
            "headless parent {session_id} registered on client connection {connection_id}"
        ));
        response_success(Some(command_id), type_name, None)
    }

    /// `headless_parent_receipt`: a registered parent answers one
    /// delivery, on the connection the delivery went to.
    pub(crate) fn handle_headless_parent_receipt(
        &self,
        command: &DaemonCommand,
        connection_id: &str,
        command_id: &str,
        type_name: &str,
    ) -> DaemonResponse {
        let DaemonCommand::HeadlessParentReceipt {
            delivery_id,
            receipt,
            error,
            ..
        } = command
        else {
            return response_failure(Some(command_id), type_name, "invalid command", None);
        };
        let answer = match (receipt, error) {
            (Some(receipt), None) => Answer::Receipt(receipt.clone()),
            (None, Some(error)) => Answer::Refused(error.clone()),
            (Some(_), Some(_)) | (None, None) => {
                return response_failure(
                    Some(command_id),
                    type_name,
                    "A headless parent receipt carries either a receipt or an error",
                    None,
                );
            }
        };
        let pending = {
            let mut deliveries = self.headless_parents.deliveries();
            match deliveries.get(delivery_id) {
                Some(pending) if pending.connection_id == connection_id => {
                    deliveries.remove(delivery_id)
                }
                Some(_) | None => None,
            }
        };
        let Some(pending) = pending else {
            return response_failure(
                Some(command_id),
                type_name,
                &format!("No delivery {delivery_id} waits for this connection"),
                None,
            );
        };
        if pending.answer.send(answer).is_err() {
            self.log_line(&format!(
                "headless parent {} answered delivery {delivery_id} after its sender stopped waiting",
                pending.parent
            ));
        }
        response_success(Some(command_id), type_name, None)
    }

    /// Deliver one message to a registered headless parent: push the
    /// `worker_deliver_message` payload `delivery` over its connection and
    /// wait (within `budget`) for its receipt.
    ///
    /// # Errors
    ///
    /// The parent's refusal, its departure, or the budget running out.
    #[tracing::instrument(level = "debug", skip(self, target, delivery), fields(parent = %target.session_id))]
    pub(crate) async fn deliver_to_headless_parent(
        &self,
        target: &HeadlessTarget,
        delivery: Value,
        budget: Duration,
    ) -> Result<Value, HeadlessDeliveryError> {
        let delivery_id = uuid::Uuid::new_v4().to_string();
        let (answer_tx, answer_rx) = oneshot::channel();
        let left = || HeadlessDeliveryError::Left {
            session_id: target.session_id.clone(),
        };
        let connection_id = {
            let parents = self.headless_parents.parents();
            let Some(parent) = parents.get(&target.session_id) else {
                return Err(left());
            };
            parent.connection_id.clone()
        };
        self.headless_parents.deliveries().insert(
            delivery_id.clone(),
            Pending {
                parent: target.session_id.clone(),
                connection_id,
                answer: answer_tx,
            },
        );
        let frame = json!({
            "type": DELIVERY_FRAME,
            "deliveryId": delivery_id,
            "delivery": delivery,
        });
        let answered = tokio::time::timeout(budget, async {
            if target
                .outbound
                .send((vec![Outbound::Line(frame)], false))
                .await
                .is_err()
            {
                return Err(left());
            }
            answer_rx.await.map_err(|_departed| left())
        })
        .await;
        self.headless_parents.deliveries().remove(&delivery_id);
        match answered {
            Ok(Ok(Answer::Receipt(receipt))) => Ok(receipt),
            Ok(Ok(Answer::Refused(error))) => Err(HeadlessDeliveryError::Refused(error)),
            Ok(Err(error)) => Err(error),
            Err(_elapsed) => Err(HeadlessDeliveryError::TimedOut {
                session_id: target.session_id.clone(),
                seconds: budget.as_secs(),
            }),
        }
    }

    /// The client connection `connection_id` closed: every parent it
    /// registered left, and their resident children close with them.
    pub(crate) async fn headless_connection_closed(self: &Arc<Self>, connection_id: &str) {
        for parent in self.headless_parents.leave(connection_id) {
            self.log_line(&format!("headless parent {parent} left"));
            // A draining supervisor retires every worker itself.
            if self.is_shutting_down() {
                continue;
            }
            self.close_children_of_headless_parent(&parent).await;
        }
    }
}

/// Why a headless parent did not take a delivered message.
#[derive(Debug, thiserror::Error)]
pub(crate) enum HeadlessDeliveryError {
    /// The parent's receipt refused it (the receipt's text).
    #[error("{0}")]
    Refused(String),
    /// The parent left before it answered.
    #[error("The headless session {session_id} left before it took the message")]
    Left { session_id: String },
    #[error("The headless session {session_id} did not take the message within {seconds} s")]
    TimedOut { session_id: String, seconds: u64 },
}
