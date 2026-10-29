//! The gateway's event loop: Signal messages go into the routed daemon
//! session; the agent's replies go back while Signal holds the floor.

use std::collections::{HashMap, VecDeque};
use std::path::Path;
use std::time::{Duration, Instant};

use anyhow::Context;
use eukhe_tui::daemon_build::{relation, Build, Relation};
use eukhe_tui::daemon_client::DaemonClientEvent;
use eukhe_types::ai::{UserContent, UserContentBlock};
use eukhe_types::daemon::{
    DaemonCommand, MemoryReply, MemorySnapshot, PromptInput, SessionEvent, StreamingBehavior,
};
use eukhe_types::session::AgentMessage;
use serde_json::{json, Map, Value};
use tokio::signal::unix::{signal, SignalKind};
use tokio::sync::{mpsc, watch};

use crate::answer::{answer, Answer};
use crate::commands::{Parsed, PhoneCommand};
use crate::link::{reconnect_delay, Binding, Link, Opened, Reconnect};
use crate::sessions::{Route, SavedSession, SessionRef, LISTED_SESSIONS};
use crate::signal::{Inbound, Peer, SignalCli, Typing};
use crate::style::{self, StyledText};
use crate::GatewayConfig;
use eukhe_tui::saved_sessions::{strip_signal_reply_rules, DaemonLauncher, SIGNAL_REPLY_RULES};

/// Signal shows a typing indicator for about 15 s; refresh it sooner.
const TYPING_REFRESH: Duration = Duration::from_secs(10);

/// How long the typing indicator stays without a running turn (a prompt
/// that starts no turn, such as a session slash command).
const TYPING_WITHOUT_TURN: Duration = Duration::from_secs(30);

/// How many sent prompt texts the floor check remembers.
const SENT_PROMPTS_KEPT: usize = 16;

/// How long the shutdown cleanup (typing stop, detach) may take.
const SHUTDOWN_BUDGET: Duration = Duration::from_secs(5);

/// The typing indicator the gateway shows.
struct TypingShown {
    peer: Peer,
    since: Instant,
}

/// The daemon connection's state.
enum DaemonState {
    Up,
    /// The daemon announced its shutdown (`eukhe shutdown`, a signal, or a
    /// launcher replacing it): when its connection ends, wait for the
    /// daemon another client starts instead of starting one.
    Closing,
    /// The daemon stopped on request: retry a plain connect at `retry_at`.
    /// The next Signal message starts a daemon.
    Waiting {
        retry_at: tokio::time::Instant,
        delay: Duration,
    },
}

pub(crate) struct Gateway<L> {
    config: GatewayConfig,
    signal: SignalCli,
    inbound: mpsc::Receiver<Inbound>,
    link: Link<L>,
    shutdown: watch::Receiver<bool>,
    daemon: DaemonState,
    route: Route,
    binding: Option<Binding>,
    /// The Signal peer that gets the agent's replies; `None` while the CLI
    /// holds the floor.
    floor: Option<Peer>,
    /// Whether the bound session runs a turn.
    running: bool,
    typing: Option<TypingShown>,
    /// The peer that sent `/stop` while a turn ran: it hears `Stopped.`
    /// when the turn ends (an abort before any reply writes no aborted
    /// message).
    stop_pending: Option<Peer>,
    /// Prompt texts the gateway sent: their user rows do not hand the
    /// floor to the CLI.
    sent_prompts: VecDeque<String>,
    /// Each peer's last `/sessions` list, which `/use N` indexes.
    listings: HashMap<Peer, Vec<SavedSession>>,
}

impl<L: DaemonLauncher> Gateway<L> {
    /// Install the signal handlers, connect to the daemon, and start
    /// `signal-cli`.
    ///
    /// # Errors
    ///
    /// A handler cannot install, the first daemon connection fails, or
    /// `signal-cli` cannot start.
    #[tracing::instrument(skip_all)]
    pub(crate) async fn start(config: GatewayConfig, launcher: L) -> anyhow::Result<Self> {
        let mut interrupt =
            signal(SignalKind::interrupt()).context("install the SIGINT handler")?;
        let mut terminate =
            signal(SignalKind::terminate()).context("install the SIGTERM handler")?;
        let (stop, shutdown) = watch::channel(false);
        tokio::spawn(async move {
            let name = tokio::select! {
                _ = interrupt.recv() => "SIGINT",
                _ = terminate.recv() => "SIGTERM",
            };
            tracing::info!(signal = name, "stopping the gateway");
            if stop.send(true).is_err() {
                tracing::debug!("the gateway stopped first");
            }
        });
        let link = Link::connect(config.socket_path.clone(), launcher, shutdown.clone()).await?;
        let (signal, inbound) = SignalCli::spawn(&config.signal)
            .await
            .context("start signal-cli")?;
        tracing::info!("the gateway runs");
        Ok(Self {
            config,
            signal,
            inbound,
            link,
            shutdown,
            daemon: DaemonState::Up,
            route: Route::Follow,
            binding: None,
            floor: None,
            running: false,
            typing: None,
            stop_pending: None,
            sent_prompts: VecDeque::new(),
            listings: HashMap::new(),
        })
    }

    /// Serve until shutdown: inbound messages strictly in arrival order,
    /// daemon events as they come, reconnects when the daemon goes away.
    ///
    /// # Errors
    ///
    /// The `signal-cli` supervisor stops delivering messages.
    #[tracing::instrument(skip_all)]
    pub(crate) async fn serve(mut self) -> anyhow::Result<()> {
        let mut typing_tick = tokio::time::interval(TYPING_REFRESH);
        typing_tick.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Delay);
        let outcome = loop {
            if *self.shutdown.borrow() {
                break Ok(());
            }
            if self.link.is_dead() {
                match self.daemon {
                    DaemonState::Up => {
                        self.recover().await;
                        continue;
                    }
                    DaemonState::Closing => {
                        tracing::info!(
                            "the daemon stopped on request; waiting for a new daemon (the next Signal message starts one)"
                        );
                        self.daemon = DaemonState::Waiting {
                            retry_at: tokio::time::Instant::now() + reconnect_delay(None),
                            delay: reconnect_delay(None),
                        };
                        self.stop_typing().await;
                        if self.running {
                            self.running = false;
                            if let Some(peer) = self.floor.clone() {
                                self.reply(
                                    &peer,
                                    "Error: the daemon stopped. The next message starts it."
                                        .to_string(),
                                )
                                .await;
                            }
                        }
                    }
                    DaemonState::Waiting { .. } => {}
                }
            }
            let retry = match self.daemon {
                DaemonState::Waiting { retry_at, delay } => Some((retry_at, delay)),
                DaemonState::Up | DaemonState::Closing => None,
            };
            let connected = retry.is_none();
            tokio::select! {
                changed = self.shutdown.changed() => {
                    if changed.is_err() {
                        break Ok(());
                    }
                }
                inbound = self.inbound.recv() => match inbound {
                    Some(inbound) => self.handle_inbound(inbound).await,
                    None => break Err(anyhow::anyhow!("the signal-cli supervisor stopped")),
                },
                event = self.link.events.recv(), if connected => {
                    if let Some(event) = event {
                        self.handle_event(event).await;
                    } else {
                        tracing::warn!("the daemon event stream closed");
                        self.recover().await;
                    }
                }
                // The loop top handles a dead connection.
                _ = self.link.reader_dead.changed(), if connected => {}
                () = tokio::time::sleep_until(retry.map_or_else(tokio::time::Instant::now, |(at, _)| at)), if !connected => {
                    match self.link.try_reconnect().await {
                        Ok(()) => {
                            // Another client started this daemon. A daemon not older than this gateway means
                            // eukhe was upgraded: stop, so the service starts the gateway again on the new build.
                            // An older daemon keeps serving this gateway, which never replaces a daemon.
                            if let Relation::Newer | Relation::Other = relation(Build::THIS, self.link.client.daemon_build()) {
                                tracing::info!(version = self.link.client.daemon_build().version, "a daemon of another eukhe build runs; the gateway stops so its service restarts it on that build");
                                break Ok(());
                            }
                            self.daemon = DaemonState::Up;
                            self.reattach().await;
                        }
                        Err(error) => {
                            let delay = reconnect_delay(retry.map(|(_, delay)| delay));
                            tracing::debug!(error = %format!("{error:#}"), retry_ms = delay.as_millis(), "no daemon yet");
                            self.daemon = DaemonState::Waiting {
                                retry_at: tokio::time::Instant::now() + delay,
                                delay,
                            };
                        }
                    }
                }
                _ = typing_tick.tick() => self.refresh_typing().await,
            }
        };
        let cleanup = async {
            self.stop_typing().await;
            if let Some(binding) = self.binding.take() {
                if let Err(error) = self.link.detach(&binding.active_session_id).await {
                    tracing::warn!(error = %format!("{error:#}"), "detach at shutdown failed");
                }
            }
        };
        if tokio::time::timeout(SHUTDOWN_BUDGET, cleanup)
            .await
            .is_err()
        {
            tracing::warn!("the shutdown cleanup timed out");
        }
        outcome
    }

    /// Start the daemon again after it went away, reconnect, and attach
    /// the bound session again. Messages that arrive meanwhile wait in the
    /// inbound channel.
    #[tracing::instrument(skip_all)]
    async fn recover(&mut self) {
        match self.link.reconnect().await {
            Reconnect::ShuttingDown => {}
            Reconnect::Connected => {
                self.daemon = DaemonState::Up;
                self.reattach().await;
            }
        }
    }

    /// Attach the bound session on a new connection.
    #[tracing::instrument(skip_all)]
    async fn reattach(&mut self) {
        self.running = false;
        let Some(binding) = self.binding.take() else {
            return;
        };
        match self
            .link
            .open(Some(&binding.session.path), binding.create_config.clone())
            .await
        {
            Ok(opened) => {
                self.running = opened.streaming;
                self.binding = Some(opened.binding);
            }
            Err(error) => {
                let error = format!("{error:#}");
                tracing::warn!(%error, "re-attach after reconnect failed");
                self.stop_typing().await;
                if let Some(peer) = self.floor.take() {
                    self.reply(&peer, format!("Error: lost the session: {error}"))
                        .await;
                }
            }
        }
    }

    #[tracing::instrument(skip_all, fields(peer = ?inbound.peer, timestamp = inbound.timestamp))]
    async fn handle_inbound(&mut self, inbound: Inbound) {
        if let Err(error) = self
            .signal
            .read_receipt(&inbound.peer, inbound.timestamp)
            .await
        {
            tracing::warn!(error = %format!("{error:#}"), "read receipt failed");
        }
        // Apply the daemon events that came first, so the floor and the
        // run state are current.
        while let Ok(event) = self.link.events.try_recv() {
            self.handle_event(event).await;
        }
        let parsed = if inbound.images.is_empty() {
            crate::commands::parse(&inbound.text)
        } else {
            Parsed::Prompt
        };
        let peer = inbound.peer.clone();
        let outcome = match parsed {
            Parsed::Command(command) => self.run_command(&peer, command).await.map(Some),
            Parsed::Answer(answer) => Ok(Some(answer)),
            Parsed::Prompt if inbound.text.trim().is_empty() && inbound.images.is_empty() => {
                tracing::info!("ignored an empty message");
                Ok(None)
            }
            Parsed::Prompt => self.prompt(&inbound).await.map(|()| None),
        };
        match outcome {
            Ok(Some(reply)) => self.reply(&peer, reply).await,
            Ok(None) => {}
            Err(error) => {
                let error = format!("{error:#}");
                tracing::warn!(%error, "message failed");
                self.reply(&peer, format!("Error: {error}")).await;
            }
        }
    }

    /// Run one phone command; the answer is the reply text.
    #[tracing::instrument(skip_all)]
    async fn run_command(&mut self, peer: &Peer, command: PhoneCommand) -> anyhow::Result<String> {
        match command {
            PhoneCommand::Help => Ok(crate::commands::help()),
            PhoneCommand::Sessions => {
                let bound = self.binding.as_ref().map(|binding| binding.session.clone());
                let now_ms = std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .context("read the clock")?
                    .as_millis();
                let now_ms = u64::try_from(now_ms).context("the clock is out of range")?;
                let sessions = self.refresh_listing(peer).await?;
                if sessions.is_empty() {
                    return Ok("No sessions. Send a message to start one.".to_string());
                }
                let mut lines: Vec<String> = sessions
                    .iter()
                    .enumerate()
                    .map(|(index, saved)| {
                        crate::sessions::session_line(index + 1, saved, bound.as_ref(), now_ms)
                    })
                    .collect();
                lines.push("Send /use N to select.".to_string());
                Ok(lines.join("\n"))
            }
            PhoneCommand::Use(number) => {
                if !self.listings.contains_key(peer) {
                    self.refresh_listing(peer).await?;
                }
                let listing = self.listings.get(peer).map_or(&[][..], Vec::as_slice);
                let saved = number
                    .parse::<usize>()
                    .ok()
                    .and_then(|number| number.checked_sub(1))
                    .and_then(|index| listing.get(index))
                    .cloned()
                    .with_context(|| {
                        format!(
                            "no session {number}. Send /sessions, then /use N with N from 1 to {}",
                            listing.len()
                        )
                    })?;
                self.open(Some(&saved.path), Some(&saved.cwd)).await?;
                self.route = Route::Pinned(SessionRef::from(&saved));
                let title = saved.title.as_deref().unwrap_or("(no title)");
                Ok(format!(
                    "Using session {number}: {title}\nSend /latest to use the newest session."
                ))
            }
            PhoneCommand::Latest => {
                self.route = Route::Follow;
                Ok("Messages go to the newest session.".to_string())
            }
            PhoneCommand::New => {
                let binding = self.open(None, None).await?;
                self.route = Route::Pinned(binding.session);
                Ok(format!(
                    "New session in {}.\nSend /latest to use the newest session.",
                    self.config.new_session_cwd.display()
                ))
            }
            PhoneCommand::Stop => {
                let Some(binding) = &self.binding else {
                    return Ok("No session is open.".to_string());
                };
                self.link
                    .client
                    .request_ok(DaemonCommand::Abort {
                        id: None,
                        active_session_id: binding.active_session_id.clone(),
                        rest: Map::default(),
                    })
                    .await
                    .context("stop the turn")?;
                if self.running {
                    self.stop_pending = Some(peer.clone());
                }
                Ok("Stop sent.".to_string())
            }
            PhoneCommand::Status => self.status().await,
            PhoneCommand::Memory => self.memory().await,
        }
    }

    /// List the newest root sessions and keep them as `peer`'s listing,
    /// which `/use N` indexes.
    ///
    /// # Errors
    ///
    /// The daemon cannot list the sessions.
    #[tracing::instrument(skip_all)]
    async fn refresh_listing(&mut self, peer: &Peer) -> anyhow::Result<&[SavedSession]> {
        let mut sessions = self
            .link
            .root_sessions(&self.config.session_dir, &self.config.new_session_cwd)
            .await?;
        sessions.truncate(LISTED_SESSIONS);
        Ok(self
            .listings
            .entry(peer.clone())
            .insert_entry(sessions)
            .into_mut())
    }

    /// The `/status` reply: the bound session's name, folder, and run
    /// state, and the routing mode.
    ///
    /// # Errors
    ///
    /// The daemon cannot report the session state, or the state lacks a
    /// field.
    #[tracing::instrument(skip_all)]
    async fn status(&self) -> anyhow::Result<String> {
        let mode = match &self.route {
            Route::Follow => "follow (newest session)",
            Route::Pinned(_) => "pinned",
        };
        let Some(binding) = &self.binding else {
            return Ok(format!(
                "Session: none open. The next message opens one.\nMode: {mode}"
            ));
        };
        let state = self
            .link
            .client
            .request_ok(DaemonCommand::GetState {
                id: None,
                active_session_id: binding.active_session_id.clone(),
                rest: Map::default(),
            })
            .await
            .context("read the session state")?;
        let text = |key: &str| {
            state
                .get(key)
                .and_then(Value::as_str)
                .filter(|value| !value.trim().is_empty())
        };
        let name = text("sessionName")
            .or_else(|| {
                text("firstMessage")
                    .map(strip_signal_reply_rules)
                    .filter(|first| !first.trim().is_empty())
            })
            .map_or_else(|| "(no name)".to_string(), crate::sessions::short_title);
        let cwd = text("cwd").context("the session state has no cwd")?;
        let busy = state
            .get("isStreaming")
            .and_then(Value::as_bool)
            .context("the session state has no isStreaming")?;
        let busy = if busy { "yes" } else { "no" };
        // `get_state` leaves `model` out when the session has none.
        let model = match state.get("model") {
            None => "none".to_string(),
            Some(model) => {
                let field = |key: &str| {
                    model
                        .get(key)
                        .and_then(Value::as_str)
                        .with_context(|| format!("the session model has no {key}"))
                };
                format!("{}/{}", field("provider")?, field("id")?)
            }
        };
        Ok(format!(
            "Session: {name}\nFolder: {cwd}\nModel: {model}\nMode: {mode}\nBusy: {busy}"
        ))
    }

    /// The `/memory` reply: the chat memory's size and compactor state.
    /// Every root session shares the one chat memory, so this opens the
    /// routed session when none is bound.
    ///
    /// # Errors
    ///
    /// No session can open, or the daemon cannot report the memory.
    #[tracing::instrument(skip_all)]
    async fn memory(&mut self) -> anyhow::Result<String> {
        let binding = self.routed_binding().await?;
        let data = self
            .link
            .client
            .request_ok(DaemonCommand::GetMemory {
                id: None,
                active_session_id: binding.active_session_id,
                zoom: None,
                rest: Map::default(),
            })
            .await
            .context("read the chat memory")?;
        let reply: MemoryReply =
            serde_json::from_value(data).context("malformed get_memory reply")?;
        let Some(MemorySnapshot { status, .. }) = reply.memory else {
            return Ok("This session keeps no chat memory.".to_string());
        };
        let model = status.model.as_deref().unwrap_or("default model");
        let mut lines = vec![
            format!("Messages: {}", status.messages),
            format!(
                "View: {} lines, {} kB",
                status.lines,
                status.view_bytes.div_ceil(1000)
            ),
            format!("Not summarized: {}", status.unsummarized),
            format!("Compactor: {model}, {} running", status.running),
        ];
        if let Some(error) = status.last_error {
            lines.push(format!("Last error: {error}"));
        }
        Ok(lines.join("\n"))
    }

    /// Send one message to the agent; on success Signal holds the floor.
    #[tracing::instrument(skip_all)]
    async fn prompt(&mut self, inbound: &Inbound) -> anyhow::Result<()> {
        let message = format!("{SIGNAL_REPLY_RULES}\n\n{}", inbound.text);
        let shown = match inbound.images.len() {
            0 => inbound.text.clone(),
            1 => format!("{}\n[1 image]", inbound.text),
            count => format!("{}\n[{count} images]", inbound.text),
        };
        let peer_label = match &inbound.peer {
            Peer::NoteToSelf => "note-to-self".to_string(),
            Peer::Contact(contact) => contact.clone(),
        };
        let images = (!inbound.images.is_empty()).then(|| {
            Value::Array(
                inbound
                    .images
                    .iter()
                    .map(|image| {
                        json!({ "type": "image", "data": image.data_base64, "mimeType": image.mime_type })
                    })
                    .collect(),
            )
        });
        let command = |active_session_id: String| DaemonCommand::Prompt {
            id: None,
            active_session_id,
            message: message.clone(),
            input: PromptInput {
                content: None,
                images: images.clone(),
                streaming_behavior: Some(StreamingBehavior::FollowUp),
                queue_if_busy: Some(true),
                expand_prompt_templates: None,
                source: None,
                agent_message_id: None,
                custom_message: Some(json!({
                    "role": "custom",
                    "customType": "signal",
                    "content": shown,
                    "display": true,
                    "details": { "peer": peer_label },
                })),
                queue_key: None,
                prefix_messages: None,
                admission_id: Some(uuid::Uuid::new_v4().to_string()),
                rlm_notice_nonce: None,
                reply_to: None,
            },
            rest: Map::default(),
        };
        let binding = self.routed_binding().await?;
        self.select_model(&binding.active_session_id).await?;
        if self.sent_prompts.len() == SENT_PROMPTS_KEPT {
            self.sent_prompts.pop_front();
        }
        self.sent_prompts.push_back(message.clone());
        let response = self
            .link
            .client
            .request(command(binding.active_session_id.clone()))
            .await
            .context("send the message; it may not have arrived")?;
        if !response.success {
            // A refusal admitted nothing: open the session again and retry
            // once (a replaced worker answers under a new id).
            let refusal = response
                .error
                .unwrap_or_else(|| "no reason given".to_string());
            tracing::warn!(%refusal, "prompt refused; reopening the session");
            self.binding = None;
            if let Err(error) = self.link.detach(&binding.active_session_id).await {
                tracing::debug!(error = %format!("{error:#}"), "detach of the refused binding failed");
            }
            let binding = self
                .routed_binding()
                .await
                .with_context(|| format!("the daemon refused the message ({refusal})"))?;
            self.select_model(&binding.active_session_id).await?;
            let response = self
                .link
                .client
                .request(command(binding.active_session_id))
                .await
                .context("send the message; it may not have arrived")?;
            if !response.success {
                anyhow::bail!(
                    "the daemon refused the message: {}",
                    response
                        .error
                        .unwrap_or_else(|| "no reason given".to_string())
                );
            }
        }
        self.floor = Some(inbound.peer.clone());
        self.start_typing(&inbound.peer).await;
        Ok(())
    }

    /// Switch the session to the Signal model (`gateway.signal.model`)
    /// when it runs another model. Without the setting the session keeps
    /// its model.
    ///
    /// # Errors
    ///
    /// The daemon cannot report the session state, or refuses the switch
    /// (an unknown model, a provider without credentials).
    #[tracing::instrument(skip(self))]
    async fn select_model(&self, active_session_id: &str) -> anyhow::Result<()> {
        let Some(model) = &self.config.model else {
            return Ok(());
        };
        let state = self
            .link
            .client
            .request_ok(DaemonCommand::GetState {
                id: None,
                active_session_id: active_session_id.to_string(),
                rest: Map::default(),
            })
            .await
            .context("read the session state")?;
        let current = |key: &str| {
            state
                .get("model")
                .and_then(|current| current.get(key))
                .and_then(Value::as_str)
        };
        if current("provider") == Some(model.provider.as_str())
            && current("id") == Some(model.model_id.as_str())
        {
            return Ok(());
        }
        self.link
            .client
            .request_ok(DaemonCommand::SetModel {
                id: None,
                active_session_id: active_session_id.to_string(),
                provider: model.provider.clone(),
                model_id: model.model_id.clone(),
                rest: Map::default(),
            })
            .await
            .with_context(|| format!("switch the session to {model} (gateway.signal.model)"))?;
        tracing::info!(%model, "switched the session to the Signal model");
        Ok(())
    }

    /// The binding the route selects now, opened when it changed: the
    /// pinned session, or the newest root session (the bound one when
    /// none is saved yet; a new one when nothing exists).
    #[tracing::instrument(skip_all)]
    async fn routed_binding(&mut self) -> anyhow::Result<Binding> {
        if self.link.is_dead() {
            self.recover().await;
            if self.link.is_dead() {
                anyhow::bail!("the daemon is not reachable");
            }
        }
        let (target, saved_cwd) = match &self.route {
            Route::Pinned(session) => (Some(session.clone()), None),
            Route::Follow => {
                let newest = self
                    .link
                    .root_sessions(&self.config.session_dir, &self.config.new_session_cwd)
                    .await?
                    .into_iter()
                    .next();
                match newest {
                    Some(saved) => (Some(SessionRef::from(&saved)), Some(saved.cwd)),
                    None => (None, None),
                }
            }
        };
        match (target, &self.binding) {
            (Some(target), Some(binding)) if binding.session.id == target.id => Ok(binding.clone()),
            (None, Some(binding)) => Ok(binding.clone()),
            (Some(target), _) => self.open(Some(&target.path), saved_cwd.as_deref()).await,
            (None, None) => self.open(None, None).await,
        }
    }

    /// Open and attach a session (`session_path`, else a new one in the
    /// new-session folder) and make it the binding.
    #[tracing::instrument(skip(self))]
    async fn open(
        &mut self,
        session_path: Option<&str>,
        saved_cwd: Option<&str>,
    ) -> anyhow::Result<Binding> {
        let mut create_config =
            json!({ "sessionDir": self.config.session_dir.display().to_string() });
        let new_cwd = self.config.new_session_cwd.display().to_string();
        match (session_path, saved_cwd) {
            (None, _) => create_config["cwd"] = json!(new_cwd),
            (Some(_), Some(cwd)) if !cwd.is_empty() && !Path::new(cwd).exists() => {
                tracing::warn!(missing = cwd, cwd = %new_cwd, "the session folder is missing; using the new-session folder");
                create_config["cwd"] = json!(new_cwd);
            }
            // The session keeps its stored folder.
            (Some(_), _) => {}
        }
        let Opened { binding, streaming } = self.link.open(session_path, create_config).await?;
        let previous = self.binding.replace(binding.clone());
        if let Some(previous) = previous {
            if previous.active_session_id != binding.active_session_id {
                if let Err(error) = self.link.detach(&previous.active_session_id).await {
                    tracing::warn!(error = %format!("{error:#}"), "detach from the previous session failed");
                }
                // The new session's turns answer nobody on Signal yet.
                self.floor = None;
                self.stop_pending = None;
                self.stop_typing().await;
            }
        }
        self.running = streaming;
        Ok(binding)
    }

    #[tracing::instrument(skip_all)]
    async fn handle_event(&mut self, event: DaemonClientEvent) {
        match event {
            DaemonClientEvent::SessionEvent {
                active_session_id,
                event,
                ..
            } => {
                if self
                    .binding
                    .as_ref()
                    .is_some_and(|binding| binding.active_session_id == active_session_id)
                {
                    self.relay(&event).await;
                }
            }
            DaemonClientEvent::UndecodableSessionEvent {
                active_session_id,
                error,
            } => {
                tracing::warn!(%active_session_id, %error, "a session event could not be decoded");
            }
            DaemonClientEvent::SessionClosed {
                active_session_id,
                reason,
            } => {
                if self
                    .binding
                    .as_ref()
                    .is_some_and(|binding| binding.active_session_id == active_session_id)
                {
                    tracing::info!(%reason, "the bound session closed");
                    self.binding = None;
                    self.running = false;
                    self.stop_typing().await;
                    if let Some(peer) = self.floor.take() {
                        self.reply(&peer, format!("Error: the session closed ({reason}). The next message opens a session."))
                            .await;
                    }
                }
            }
            DaemonClientEvent::DaemonClosing { reason } => {
                tracing::info!(%reason, "the daemon is closing");
                self.daemon = DaemonState::Closing;
            }
            DaemonClientEvent::SessionBinding {
                previous_active_session_id,
                active_session_id,
            } => {
                // A replaced worker serves the bound session under a new id:
                // open it again to attach there.
                let Some(binding) = self
                    .binding
                    .clone()
                    .filter(|binding| binding.active_session_id == previous_active_session_id)
                else {
                    return;
                };
                tracing::info!(%active_session_id, "the bound session moved to a new worker");
                match self
                    .link
                    .open(Some(&binding.session.path), binding.create_config)
                    .await
                {
                    Ok(opened) => {
                        self.running = opened.streaming;
                        self.binding = Some(opened.binding);
                    }
                    Err(error) => {
                        tracing::warn!(error = %format!("{error:#}"), "re-attach after a worker replacement failed");
                        self.binding = None;
                    }
                }
            }
            DaemonClientEvent::DirectLinkLost { .. }
            | DaemonClientEvent::SessionListItem { .. }
            | DaemonClientEvent::SessionListProgress { .. }
            | DaemonClientEvent::SideQuestionEvent { .. }
            | DaemonClientEvent::ShellApproval { .. }
            | DaemonClientEvent::ShellApprovalSettled { .. }
            | DaemonClientEvent::RosterUpdate { .. }
            | DaemonClientEvent::StateTreeUpdate { .. }
            | DaemonClientEvent::HeartbeatsChanged => {}
        }
    }

    /// Apply one session event of the bound session: run state, the floor,
    /// and the replies Signal gets while it holds the floor.
    #[tracing::instrument(skip_all)]
    async fn relay(&mut self, event: &SessionEvent) {
        match event {
            SessionEvent::AgentStart => {
                self.running = true;
                if let Some(peer) = self.floor.clone() {
                    self.start_typing(&peer).await;
                }
            }
            SessionEvent::AgentEnd { .. } => {
                self.running = false;
                self.stop_typing().await;
                if let Some(peer) = self.stop_pending.take() {
                    // A stopped run answers `Stopped.` only.
                    self.reply(&peer, "Stopped.".to_string()).await;
                    return;
                }
            }
            SessionEvent::MessageStart {
                message: AgentMessage::User(user),
                ..
            } => {
                let text = user_text(&user.content);
                if let Some(index) = self.sent_prompts.iter().position(|sent| *sent == text) {
                    self.sent_prompts.remove(index);
                } else if self.floor.take().is_some() {
                    tracing::info!("the CLI took the floor");
                    self.stop_typing().await;
                }
            }
            SessionEvent::MessageStart { .. }
            | SessionEvent::MessageUpdate { .. }
            | SessionEvent::MessageEnd { .. }
            | SessionEvent::TurnStart
            | SessionEvent::TurnEnd { .. }
            | SessionEvent::PromptProgress { .. }
            | SessionEvent::ToolExecutionStart { .. }
            | SessionEvent::ToolExecutionUpdate { .. }
            | SessionEvent::ToolExecutionEnd { .. }
            | SessionEvent::AutoRetryStart { .. }
            | SessionEvent::AutoRetryEnd { .. }
            | SessionEvent::CompactionStart { .. }
            | SessionEvent::CompactionSummaryDelta { .. }
            | SessionEvent::CompactionEnd { .. }
            | SessionEvent::SessionInfoChanged { .. }
            | SessionEvent::ServiceTierChanged { .. }
            | SessionEvent::SessionActionUpdate { .. }
            | SessionEvent::GoalUpdate { .. }
            | SessionEvent::MemoryUpdate { .. }
            | SessionEvent::AgentRelay(_)
            | SessionEvent::BashStart { .. }
            | SessionEvent::BashOutput { .. }
            | SessionEvent::BashEnd { .. }
            | SessionEvent::RefineComplete { .. }
            | SessionEvent::RefineFailed { .. }
            | SessionEvent::IpythonSentAgentMessage { .. } => {}
        }
        if let Some(answer) = answer(event) {
            self.relay_answer(answer).await;
        }
    }

    /// Relay one answer to the peer holding the floor.
    async fn relay_answer(&mut self, answer: Answer) {
        let Some(peer) = self.floor.clone() else {
            return;
        };
        match answer {
            Answer::Text(text) => {
                for chunk in style::render(&text) {
                    if let Err(error) = self.signal.send(&peer, &chunk).await {
                        tracing::error!(error = %format!("{error:#}"), "reply send failed");
                        break;
                    }
                }
            }
            Answer::Failed(reason) => self.reply(&peer, format!("Error: {reason}")).await,
            Answer::Stopped => {
                if self.stop_pending.as_ref() == Some(&peer) {
                    self.stop_pending = None;
                }
                self.reply(&peer, "Stopped.".to_string()).await;
            }
        }
    }

    /// Send plain text (no styles) to `peer`.
    #[tracing::instrument(skip_all, fields(peer = ?peer))]
    async fn reply(&self, peer: &Peer, text: String) {
        let styled = StyledText {
            text,
            styles: Vec::new(),
        };
        if let Err(error) = self.signal.send(peer, &styled).await {
            tracing::error!(error = %format!("{error:#}"), "reply send failed");
        }
    }

    #[tracing::instrument(skip_all, fields(peer = ?peer))]
    async fn start_typing(&mut self, peer: &Peer) {
        if self
            .typing
            .as_ref()
            .is_some_and(|shown| shown.peer == *peer)
        {
            return;
        }
        self.stop_typing().await;
        if let Err(error) = self.signal.typing(peer, Typing::Started).await {
            tracing::warn!(error = %format!("{error:#}"), "typing start failed");
        }
        self.typing = Some(TypingShown {
            peer: peer.clone(),
            since: Instant::now(),
        });
    }

    #[tracing::instrument(skip_all)]
    async fn stop_typing(&mut self) {
        if let Some(shown) = self.typing.take() {
            if let Err(error) = self.signal.typing(&shown.peer, Typing::Stopped).await {
                tracing::warn!(error = %format!("{error:#}"), "typing stop failed");
            }
        }
    }

    /// Keep the typing indicator alive while a turn runs; drop it when a
    /// prompt started no turn.
    #[tracing::instrument(skip_all)]
    async fn refresh_typing(&mut self) {
        let Some(shown) = &self.typing else {
            return;
        };
        if !self.running && shown.since.elapsed() > TYPING_WITHOUT_TURN {
            self.stop_typing().await;
            return;
        }
        if let Err(error) = self.signal.typing(&shown.peer, Typing::Started).await {
            tracing::warn!(error = %format!("{error:#}"), "typing refresh failed");
        }
    }
}

/// The text of a user message: its text blocks, blank-line separated.
fn user_text(content: &UserContent) -> String {
    match content {
        UserContent::Text(text) => text.clone(),
        UserContent::Blocks(blocks) => blocks
            .iter()
            .filter_map(|block| match block {
                UserContentBlock::Text(text) => Some(text.text.as_str()),
                UserContentBlock::Image(_) | UserContentBlock::Raw(_) => None,
            })
            .collect::<Vec<_>>()
            .join("\n\n"),
    }
}
