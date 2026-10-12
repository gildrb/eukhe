//! The Signal side of the gateway: a supervised `signal-cli jsonRpc` child,
//! inbound messages of allowed peers, and replies, typing and receipts.

mod envelope;
mod rpc;

use std::sync::Arc;

use anyhow::Result;
use serde::de::IgnoredAny;
use serde::{Deserialize, Serialize};
use tokio::sync::mpsc;

use crate::style::StyledText;
use crate::SignalConfig;
use envelope::ReceiveParams;
use rpc::{Notification, Rpc};

/// Inbound messages waiting for the gateway.
const INBOUND_QUEUE: usize = 64;

/// The other side of a Signal conversation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Peer {
    /// The account's own "Note to Self" conversation.
    NoteToSelf,
    /// A contact, by the allow-list entry it matched (number or ACI).
    Contact(String),
}

/// A message from an allowed peer.
pub(crate) struct Inbound {
    pub(crate) peer: Peer,
    /// The message timestamp: the id `read_receipt` takes.
    pub(crate) timestamp: u64,
    /// The message text, plus one `[attachment ...]` line per attachment the
    /// agent does not get.
    pub(crate) text: String,
    pub(crate) images: Vec<InboundImage>,
}

pub(crate) struct InboundImage {
    pub(crate) mime_type: String,
    pub(crate) data_base64: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Typing {
    Started,
    Stopped,
}

/// A handle to the supervised `signal-cli` child. Cheap to clone.
#[derive(Clone)]
pub(crate) struct SignalCli {
    rpc: Rpc,
    account: Arc<str>,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct SendParams<'a> {
    #[serde(flatten)]
    to: Recipient<'a>,
    message: &'a str,
    #[serde(skip_serializing_if = "<[String]>::is_empty")]
    text_style: &'a [String],
}

#[derive(Serialize)]
#[serde(untagged)]
enum Recipient<'a> {
    Contact {
        recipient: [&'a str; 1],
    },
    /// `notifySelf` sends a normal message instead of a sync message, so the
    /// phone notifies.
    #[serde(rename_all = "camelCase")]
    NoteToSelf {
        note_to_self: bool,
        notify_self: bool,
    },
}

#[derive(Deserialize)]
struct SendResult {
    timestamp: u64,
}

#[derive(Serialize)]
struct TypingParams<'a> {
    recipient: [&'a str; 1],
    stop: bool,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct ReceiptParams<'a> {
    /// A single value: `sendReceipt` reads `recipient` as one string.
    recipient: &'a str,
    target_timestamp: [u64; 1],
    #[serde(rename = "type")]
    kind: &'static str,
}

#[derive(Serialize)]
struct AttachmentParams<'a> {
    id: &'a str,
    recipient: &'a str,
}

#[derive(Deserialize)]
struct AttachmentData {
    data: String,
}

impl SignalCli {
    /// Spawns and supervises `signal-cli -a <account> jsonRpc`; inbound
    /// messages from allowed peers arrive on the receiver. Restarts the child
    /// with backoff if it exits; the receiver lives across restarts.
    ///
    /// # Errors
    /// The first `signal-cli` process fails to start.
    #[tracing::instrument(skip_all, fields(account = %config.account))]
    pub(crate) async fn spawn(
        config: &SignalConfig,
    ) -> Result<(SignalCli, mpsc::Receiver<Inbound>)> {
        let (inbound, receiver) = mpsc::channel(INBOUND_QUEUE);
        // Unbounded: the stdout reader must never wait on the consumer, or
        // the `getAttachment` answers the consumer waits for would stall.
        let (notify, notifications) = mpsc::unbounded_channel();
        let rpc = Rpc::start(config.cli_path.clone(), config.account.clone(), notify).await?;
        let cli = SignalCli {
            rpc,
            account: Arc::from(config.account.as_str()),
        };
        tokio::spawn(deliver(
            cli.clone(),
            config.allow.clone(),
            notifications,
            inbound,
        ));
        Ok((cli, receiver))
    }

    /// Sends one message; returns its timestamp.
    ///
    /// # Errors
    /// `signal-cli` is down, rejects the message, or does not answer in 30 s.
    #[tracing::instrument(skip(self, text))]
    pub(crate) async fn send(&self, peer: &Peer, text: &StyledText) -> Result<u64> {
        let to = match peer {
            Peer::NoteToSelf => Recipient::NoteToSelf {
                note_to_self: true,
                notify_self: true,
            },
            Peer::Contact(id) => Recipient::Contact { recipient: [id] },
        };
        let params = SendParams {
            to,
            message: &text.text,
            text_style: &text.styles,
        };
        let sent: SendResult = self.rpc.call("send", &params).await?;
        Ok(sent.timestamp)
    }

    /// Starts or stops the typing indicator.
    ///
    /// # Errors
    /// `signal-cli` is down, fails, or does not answer in 30 s.
    #[tracing::instrument(skip(self))]
    pub(crate) async fn typing(&self, peer: &Peer, typing: Typing) -> Result<()> {
        let recipient = match peer {
            Peer::NoteToSelf => &*self.account,
            Peer::Contact(id) => id.as_str(),
        };
        let stop = match typing {
            Typing::Started => false,
            Typing::Stopped => true,
        };
        let _: IgnoredAny = self
            .rpc
            .call(
                "sendTyping",
                &TypingParams {
                    recipient: [recipient],
                    stop,
                },
            )
            .await?;
        Ok(())
    }

    /// Marks a received message read.
    ///
    /// # Errors
    /// `signal-cli` is down, fails, or does not answer in 30 s.
    #[tracing::instrument(skip(self))]
    pub(crate) async fn read_receipt(&self, peer: &Peer, timestamp: u64) -> Result<()> {
        match peer {
            // Note to Self messages are the account's own: they take no receipt.
            Peer::NoteToSelf => Ok(()),
            Peer::Contact(id) => {
                let _: IgnoredAny = self
                    .rpc
                    .call(
                        "sendReceipt",
                        &ReceiptParams {
                            recipient: id,
                            target_timestamp: [timestamp],
                            kind: "read",
                        },
                    )
                    .await?;
                Ok(())
            }
        }
    }
}

/// Turns `receive` notifications into [`Inbound`] messages, in order, and
/// fetches their images. Returns when either channel closes.
#[tracing::instrument(skip_all)]
async fn deliver(
    cli: SignalCli,
    allow: Vec<String>,
    mut notifications: mpsc::UnboundedReceiver<Notification>,
    inbound: mpsc::Sender<Inbound>,
) {
    loop {
        let notification = tokio::select! {
            () = inbound.closed() => return,
            notification = notifications.recv() => match notification {
                Some(notification) => notification,
                None => return,
            },
        };
        if notification.method != "receive" {
            tracing::debug!(
                method = notification.method,
                "ignored a signal-cli notification"
            );
            continue;
        }
        let params = match serde_json::from_value::<ReceiveParams>(notification.params) {
            Ok(params) => params,
            Err(error) => {
                tracing::warn!(%error, "unrecognized signal-cli receive notification");
                continue;
            }
        };
        let Some(draft) = params.into_draft(&cli.account, &allow) else {
            continue;
        };
        let mut text = draft.text;
        let mut images = Vec::with_capacity(draft.images.len());
        for image in draft.images {
            let fetched: Result<AttachmentData> = cli
                .rpc
                .call(
                    "getAttachment",
                    &AttachmentParams {
                        id: &image.id,
                        recipient: &draft.sender,
                    },
                )
                .await;
            match fetched {
                Ok(fetched) => images.push(InboundImage {
                    mime_type: image.content_type,
                    data_base64: fetched.data,
                }),
                Err(error) => {
                    tracing::warn!("failed to fetch an image attachment: {error:#}");
                    if !text.is_empty() {
                        text.push('\n');
                    }
                    text.push_str("[attachment ");
                    text.push_str(&image.content_type);
                    text.push_str(" could not be loaded]");
                }
            }
        }
        let message = Inbound {
            peer: draft.peer,
            timestamp: draft.timestamp,
            text,
            images,
        };
        if inbound.send(message).await.is_err() {
            return;
        }
    }
}
