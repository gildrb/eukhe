//! One browser tab's bridge to the daemon: its own daemon connection, the
//! session it is bound to, the tab's requests, and the bound session's
//! events pushed as they come. When the daemon goes away the bridge ends
//! and the tab reconnects (a new bridge starts the daemon again).

use std::path::Path;
use std::sync::Arc;

use anyhow::Context;
use eukhe_tui::daemon_client::{outdated_daemon_notice, DaemonClient, DaemonClientEvent};
use eukhe_types::daemon::{DaemonCommand, DaemonSessionLifecycle, PromptInput, StreamingBehavior};
use futures::{Sink, SinkExt, Stream, StreamExt};
use serde_json::{json, Map, Value};
use tokio::sync::{mpsc, watch};
use tokio_tungstenite::tungstenite::{self, Message};

use crate::protocol::{ClientFrame, PromptMode, Request, ServerFrame};
use crate::sessions::{root_sessions, SavedSession};
use crate::{DaemonLauncher, DashboardConfig};

/// The attach capabilities: the interactive client's set (snapshot state
/// without duplicated history or image payloads).
const ATTACH_CAPABILITIES: [&str; 4] = [
    "attach_snapshot",
    "event_sequence",
    "slim_attach",
    "elide_snapshot_images",
];

pub(crate) struct Bridge {
    config: Arc<DashboardConfig>,
    client: DaemonClient,
    events: mpsc::UnboundedReceiver<DaemonClientEvent>,
    reader_dead: watch::Receiver<bool>,
    /// The active id of the session the tab is bound to.
    binding: Option<String>,
}

impl Bridge {
    /// Start the daemon when needed and connect to it.
    ///
    /// # Errors
    ///
    /// The launcher cannot start a daemon, or the connection fails.
    #[tracing::instrument(skip_all)]
    pub(crate) async fn connect(
        config: Arc<DashboardConfig>,
        launcher: &impl DaemonLauncher,
    ) -> anyhow::Result<Self> {
        launcher.ensure().await.context("start the eukhe daemon")?;
        let (client, events) = DaemonClient::connect(&config.socket_path)
            .await
            .context("connect to the eukhe daemon")?;
        if let Some(version) = client.outdated_daemon_version() {
            tracing::warn!("{}", outdated_daemon_notice(&version));
        }
        Ok(Self {
            reader_dead: client.reader_dead(),
            config,
            client,
            events,
            binding: None,
        })
    }

    /// Serve the tab until it closes or the daemon connection ends.
    #[tracing::instrument(skip_all)]
    pub(crate) async fn run<S>(mut self, socket: S)
    where
        S: Stream<Item = Result<Message, tungstenite::Error>>
            + Sink<Message, Error = tungstenite::Error>
            + Unpin,
    {
        let (mut sink, mut stream) = socket.split();
        loop {
            if *self.reader_dead.borrow() {
                tracing::info!("the daemon connection ended; closing the tab's socket");
                break;
            }
            let outgoing = tokio::select! {
                message = stream.next() => match message {
                    Some(Ok(Message::Text(text))) => Some(self.answer(text.as_str()).await),
                    Some(Ok(Message::Close(_))) | None => break,
                    Some(Ok(Message::Binary(_) | Message::Ping(_) | Message::Pong(_) | Message::Frame(_))) => None,
                    Some(Err(error)) => {
                        tracing::debug!(%error, "the tab's socket failed");
                        break;
                    }
                },
                event = self.events.recv() => match event {
                    Some(event) => self.forward(event),
                    None => break,
                },
                changed = self.reader_dead.changed() => {
                    if changed.is_err() {
                        break;
                    }
                    None
                }
            };
            if let Some(text) = outgoing {
                if let Err(error) = sink.send(Message::text(text)).await {
                    tracing::debug!(%error, "sending to the tab failed");
                    break;
                }
            }
        }
        if let Err(error) = sink.close().await {
            tracing::debug!(%error, "closing the tab's socket failed");
        }
        if let Some(active_session_id) = self.binding.take() {
            if let Err(error) = self.detach(&active_session_id).await {
                tracing::debug!(error = %format!("{error:#}"), "detach at close failed");
            }
        }
        self.client.close();
    }

    /// The reply frame to one text frame of the tab.
    async fn answer(&mut self, text: &str) -> String {
        let frame = match serde_json::from_str::<Value>(text) {
            Ok(value) => {
                let id = value.get("id").and_then(Value::as_u64).unwrap_or(0);
                serde_json::from_value::<ClientFrame>(value)
                    .map_err(|error| (id, format!("bad request: {error}")))
            }
            Err(error) => Err((0, format!("bad request: {error}"))),
        };
        let reply = match frame {
            Ok(ClientFrame { id, request }) => match self.handle(request).await {
                Ok(data) => ServerFrame::Reply { id, data },
                Err(error) => ServerFrame::Failure {
                    id,
                    error: format!("{error:#}"),
                },
            },
            Err((id, error)) => ServerFrame::Failure { id, error },
        };
        reply.to_text()
    }

    #[tracing::instrument(skip(self))]
    async fn handle(&mut self, request: Request) -> anyhow::Result<Value> {
        match request {
            Request::Sessions => Ok(serde_json::to_value(self.root_sessions().await?)?),
            Request::Open { path } => {
                let sessions = self.root_sessions().await?;
                let saved = match path {
                    Some(path) => Some(
                        sessions
                            .into_iter()
                            .find(|saved| saved.path == path)
                            .with_context(|| format!("no saved root session at {path}"))?,
                    ),
                    None => sessions.into_iter().next(),
                };
                self.open(saved.as_ref()).await
            }
            Request::New => self.open(None).await,
            Request::Prompt { text, mode } => {
                let active_session_id = self.bound()?;
                let response = self
                    .client
                    .request(DaemonCommand::Prompt {
                        id: None,
                        active_session_id,
                        message: text,
                        input: PromptInput {
                            content: None,
                            images: None,
                            streaming_behavior: Some(match mode {
                                PromptMode::Steer => StreamingBehavior::Steer,
                                PromptMode::FollowUp => StreamingBehavior::FollowUp,
                            }),
                            queue_if_busy: Some(true),
                            expand_prompt_templates: None,
                            source: None,
                            agent_message_id: None,
                            custom_message: None,
                            queue_key: None,
                            prefix_messages: None,
                            admission_id: Some(uuid::Uuid::new_v4().to_string()),
                            rlm_notice_nonce: None,
                            reply_to: None,
                        },
                        rest: Map::default(),
                    })
                    .await
                    .context("send the message; it may not have arrived")?;
                if response.success {
                    Ok(Value::Null)
                } else {
                    anyhow::bail!(
                        "the daemon refused the message: {}",
                        response
                            .error
                            .unwrap_or_else(|| "no reason given".to_string())
                    )
                }
            }
            Request::Abort => {
                let active_session_id = self.bound()?;
                self.client
                    .request_ok(DaemonCommand::Abort {
                        id: None,
                        active_session_id,
                        rest: Map::default(),
                    })
                    .await
                    .context("stop the turn")?;
                Ok(Value::Null)
            }
            Request::Memory { node } => {
                let active_session_id = self.bound()?;
                self.client
                    .request_ok(DaemonCommand::GetMemoryTree {
                        id: None,
                        active_session_id,
                        node,
                        rest: Map::default(),
                    })
                    .await
                    .context("read the chat memory")
            }
        }
    }

    /// The bound session's active id.
    fn bound(&self) -> anyhow::Result<String> {
        self.binding.clone().context("no session is open")
    }

    #[tracing::instrument(skip_all)]
    async fn root_sessions(&self) -> anyhow::Result<Vec<SavedSession>> {
        let data = self
            .client
            .request_ok(DaemonCommand::ListSavedSessions {
                id: None,
                active_session_id: None,
                cwd: Some(self.config.new_session_cwd.display().to_string()),
                session_dir: Some(self.config.session_dir.display().to_string()),
                scope: Value::Null,
                rest: Map::default(),
            })
            .await
            .context("list the saved sessions")?;
        root_sessions(&data)
    }

    /// Open `saved` (a new session when `None`) as a resident session,
    /// attach the tab to it, and answer its transcript and state. The
    /// daemon reuses a live worker of the same session, so the CLI, the
    /// gateway and every tab share it.
    #[tracing::instrument(skip_all)]
    async fn open(&mut self, saved: Option<&SavedSession>) -> anyhow::Result<Value> {
        let mut create_config = self.config.create_config.clone();
        create_config.insert(
            "sessionDir".to_string(),
            json!(self.config.session_dir.display().to_string()),
        );
        let new_cwd = json!(self.config.new_session_cwd.display().to_string());
        match saved {
            None => {
                create_config.insert("cwd".to_string(), new_cwd);
            }
            Some(saved) if !saved.cwd.is_empty() && !Path::new(&saved.cwd).exists() => {
                tracing::warn!(missing = %saved.cwd, "the session folder is missing; using the new-session folder");
                create_config.insert("cwd".to_string(), new_cwd);
            }
            // The session keeps its stored folder.
            Some(_) => {}
        }
        let created = self
            .client
            .request_ok(DaemonCommand::Create {
                id: None,
                session_path: saved.map(|saved| saved.path.clone()),
                continue_recent: None,
                no_session: None,
                name: None,
                config: Some(Value::Object(create_config)),
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
        let active_session_id = field("activeSessionId")?;
        let session_id = field("sessionId")?;
        let path = field("sessionFile")?;
        let previous = self.binding.replace(active_session_id.clone());
        if let Some(previous) = previous.filter(|previous| *previous != active_session_id) {
            if let Err(error) = self.detach(&previous).await {
                tracing::warn!(error = %format!("{error:#}"), "detach from the previous session failed");
            }
        }
        let mut attached = self
            .client
            .request_ok(DaemonCommand::Attach {
                id: None,
                active_session_id: active_session_id.clone(),
                client_id: None,
                capabilities: Some(ATTACH_CAPABILITIES.map(str::to_string).to_vec()),
                resume_cursor: None,
                recovery_config: None,
                env: None,
                launch_env: None,
                rest: Map::default(),
            })
            .await
            .context("attach to the session")?;
        let snapshot = attached
            .get_mut("snapshot")
            .map(Value::take)
            .context("the attach answer has no snapshot")?;
        tracing::info!(%path, %active_session_id, "a tab attached");
        Ok(json!({
            "session": { "id": session_id, "path": path },
            "state": snapshot.get("state").cloned().unwrap_or(Value::Null),
            "messages": snapshot.get("messages").cloned().unwrap_or_else(|| json!([])),
        }))
    }

    #[tracing::instrument(skip(self))]
    async fn detach(&self, active_session_id: &str) -> anyhow::Result<()> {
        self.client
            .request_ok(DaemonCommand::Detach {
                id: None,
                active_session_id: Some(active_session_id.to_string()),
                rest: Map::default(),
            })
            .await
            .with_context(|| format!("detach from {active_session_id}"))?;
        Ok(())
    }

    /// The frame one daemon event becomes for the tab, if any.
    fn forward(&mut self, event: DaemonClientEvent) -> Option<String> {
        let bound = |id: &str| self.binding.as_deref() == Some(id);
        match event {
            DaemonClientEvent::SessionEvent {
                active_session_id,
                event,
                ..
            } => bound(&active_session_id).then(|| ServerFrame::Event { event: &event }.to_text()),
            DaemonClientEvent::SessionClosed {
                active_session_id,
                reason,
            } => {
                if !bound(&active_session_id) {
                    return None;
                }
                self.binding = None;
                Some(
                    ServerFrame::Resync {
                        reason: format!("the session closed ({reason})"),
                    }
                    .to_text(),
                )
            }
            DaemonClientEvent::SessionBinding {
                previous_active_session_id,
                ..
            } => {
                if !bound(&previous_active_session_id) {
                    return None;
                }
                self.binding = None;
                Some(
                    ServerFrame::Resync {
                        reason: "the session moved to a new worker".to_string(),
                    }
                    .to_text(),
                )
            }
            DaemonClientEvent::UndecodableSessionEvent {
                active_session_id,
                error,
            } => {
                tracing::warn!(%active_session_id, %error, "a session event could not be decoded");
                None
            }
            DaemonClientEvent::DaemonClosing { reason } => {
                tracing::info!(%reason, "the daemon is closing");
                None
            }
            DaemonClientEvent::DirectLinkLost { .. }
            | DaemonClientEvent::SessionListItem { .. }
            | DaemonClientEvent::SessionListProgress { .. }
            | DaemonClientEvent::SideQuestionEvent { .. }
            | DaemonClientEvent::RosterUpdate { .. }
            | DaemonClientEvent::HeartbeatsChanged => None,
        }
    }
}
