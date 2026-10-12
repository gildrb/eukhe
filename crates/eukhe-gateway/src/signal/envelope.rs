//! The `receive` notification of `signal-cli` and which envelopes become
//! inbound messages.

use serde::de::IgnoredAny;
use serde::Deserialize;

use super::Peer;

/// The most images one message hands to the agent.
const MAX_IMAGES: usize = 4;

/// `params` of a `receive` notification.
#[derive(Deserialize)]
#[serde(untagged)]
pub(super) enum ReceiveParams {
    /// `--receive-mode=on-start`: `{envelope, account}`.
    Direct(Received),
    /// `subscribeReceive`: `{subscription, result: {envelope, account}}`.
    Subscribed { result: Received },
}

#[derive(Deserialize)]
pub(super) struct Received {
    envelope: Envelope,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Envelope {
    source_number: Option<String>,
    source_uuid: Option<String>,
    data_message: Option<DataMessage>,
    sync_message: Option<SyncMessage>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct DataMessage {
    timestamp: u64,
    /// Null when the message has no body (reactions, attachments only).
    message: Option<String>,
    #[serde(default)]
    attachments: Vec<Attachment>,
    group_info: Option<IgnoredAny>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct SyncMessage {
    sent_message: Option<SentMessage>,
}

/// A message one of the account's own devices sent.
#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct SentMessage {
    destination: Option<String>,
    destination_number: Option<String>,
    destination_uuid: Option<String>,
    #[serde(flatten)]
    data: DataMessage,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "camelCase")]
struct Attachment {
    content_type: String,
    /// Null when `signal-cli` did not store the attachment.
    id: Option<String>,
}

/// An image to fetch with `getAttachment`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ImageRef {
    pub(super) id: String,
    pub(super) content_type: String,
}

/// An accepted message whose images are not fetched yet.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Draft {
    pub(super) peer: Peer,
    /// Who sent the attachments: `getAttachment`'s `recipient`.
    pub(super) sender: String,
    pub(super) timestamp: u64,
    pub(super) text: String,
    pub(super) images: Vec<ImageRef>,
}

fn same_id(id: Option<&str>, other: &str) -> bool {
    id.is_some_and(|id| id.eq_ignore_ascii_case(other))
}

impl ReceiveParams {
    /// The message this envelope carries for the gateway: a direct message
    /// of an allowed sender, or a Note to Self from one of the account's own
    /// devices. Everything else is dropped.
    pub(super) fn into_draft(self, account: &str, allow: &[String]) -> Option<Draft> {
        let (ReceiveParams::Direct(Received { envelope })
        | ReceiveParams::Subscribed {
            result: Received { envelope },
        }) = self;
        let source_number = envelope.source_number.as_deref();
        let source_uuid = envelope.source_uuid.as_deref();
        let (peer, sender, data) = match (envelope.data_message, envelope.sync_message) {
            (Some(data), _) => {
                if data.group_info.is_some() {
                    tracing::debug!("dropped a group message");
                    return None;
                }
                if same_id(source_number, account) || same_id(source_uuid, account) {
                    tracing::debug!("dropped a message the account sent itself");
                    return None;
                }
                let Some(entry) = allow
                    .iter()
                    .find(|entry| same_id(source_number, entry) || same_id(source_uuid, entry))
                else {
                    tracing::warn!(
                        sender = source_number.or(source_uuid).unwrap_or("unknown"),
                        "dropped a message from a sender that is not allowed"
                    );
                    return None;
                };
                let sender = source_number.or(source_uuid).unwrap_or(entry).to_owned();
                (Peer::Contact(entry.clone()), sender, data)
            }
            (
                None,
                Some(SyncMessage {
                    sent_message: Some(sent),
                }),
            ) => {
                // Sync messages come only from the account's own devices, so
                // the source ACI is the account's ACI.
                let to_self = [
                    sent.destination_number.as_deref(),
                    sent.destination.as_deref(),
                    sent.destination_uuid.as_deref(),
                ]
                .into_iter()
                .any(|destination| same_id(destination, account))
                    || source_uuid
                        .is_some_and(|own| same_id(sent.destination_uuid.as_deref(), own));
                if !to_self || sent.data.group_info.is_some() {
                    tracing::debug!("dropped a sync message of a message to someone else");
                    return None;
                }
                (Peer::NoteToSelf, account.to_owned(), sent.data)
            }
            (None, Some(SyncMessage { sent_message: None }) | None) => {
                tracing::debug!("dropped an envelope without a message");
                return None;
            }
        };
        let mut text = data.message.unwrap_or_default();
        if text.is_empty() && data.attachments.is_empty() {
            tracing::debug!("dropped a message without text or attachments");
            return None;
        }
        let mut images = Vec::new();
        for attachment in data.attachments {
            let note = match (
                matches!(
                    attachment.content_type.as_str(),
                    "image/jpeg" | "image/png" | "image/webp" | "image/gif"
                ),
                attachment.id,
            ) {
                (true, Some(id)) if images.len() < MAX_IMAGES => {
                    images.push(ImageRef {
                        id,
                        content_type: attachment.content_type,
                    });
                    continue;
                }
                (true, Some(_)) => format!(
                    "[attachment {} skipped: at most {MAX_IMAGES} images per message]",
                    attachment.content_type
                ),
                (true, None) => format!("[attachment {} not downloaded]", attachment.content_type),
                (false, Some(_) | None) => {
                    format!("[attachment {} not supported]", attachment.content_type)
                }
            };
            if !text.is_empty() {
                text.push('\n');
            }
            text.push_str(&note);
        }
        Some(Draft {
            peer,
            sender,
            timestamp: data.timestamp,
            text,
            images,
        })
    }
}
