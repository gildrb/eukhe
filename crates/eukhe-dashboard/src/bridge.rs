//! One browser tab's bridge to the daemon: its own daemon connection, the
//! session it is bound to, the tab's requests, and the bound session's
//! events, approval questions and resyncs pushed as they come. Each
//! request runs on its own task and answers under its id, so a slow one
//! (an open, a memory read) never holds back another or the events. When
//! the daemon goes away the bridge ends and the tab reconnects (a new
//! bridge starts the daemon again).

use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use anyhow::Context;
use base64::Engine as _;
use eukhe_tui::daemon_build::{kept_daemon_notice, Build};
use eukhe_tui::daemon_client::{DaemonClient, DaemonClientEvent};
use eukhe_tui::saved_sessions::{
    create_resident, list_root_sessions, CreatedSession, DaemonLauncher, SavedSession,
};
use eukhe_types::daemon::{
    DaemonCommand, DaemonReplayStatus, DaemonResumeCursor, PromptInput, SessionEvent,
    StreamingBehavior,
};
use futures::{Sink, SinkExt, Stream, StreamExt};
use serde::Deserialize;
use serde_json::{json, Map, Value};
use tokio::sync::{mpsc, watch};
use tokio::task::JoinSet;
use tokio_tungstenite::tungstenite::{self, Message};

use crate::command_policy::{verdict, Verdict};
use crate::protocol::{ClientFrame, EventCursor, ExportFormat, PromptMode, Request, ServerFrame};
use crate::DashboardConfig;

/// The attach capabilities: the interactive client's set (snapshot state
/// without duplicated history or image payloads, and event sequences for
/// the resume cursor), as `eukhe_tui::saved_sessions::attach` sends them.
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
}

/// What the tab's request tasks and its event loop share.
struct Tab {
    config: Arc<DashboardConfig>,
    client: DaemonClient,
    /// Frames for the tab, in the order they must arrive.
    outgoing: mpsc::UnboundedSender<String>,
    binding: Mutex<Binding>,
}

/// The session the tab is bound to.
enum Binding {
    Unbound,
    /// An open is attaching the session: its events wait here until the
    /// open's reply (the snapshot they follow) is out.
    Opening {
        active_session_id: String,
        held: Vec<HeldEvent>,
    },
    /// The session's events go to the tab as they come.
    Bound {
        active_session_id: String,
        stream: EventStream,
    },
}

/// Where the tab's view of the bound session's event stream starts.
struct EventStream {
    /// The event generation of the attach's cursor; with an event's
    /// sequence it makes the event's resume cursor.
    generation: Option<String>,
    /// The last event sequence the attach snapshot holds: an event at or
    /// before it (one already in flight when the attach answered) is not
    /// sent again.
    snapshot_sequence: u64,
}

impl Binding {
    fn active_session_id(&self) -> Option<&str> {
        match self {
            Binding::Unbound => None,
            Binding::Opening {
                active_session_id, ..
            }
            | Binding::Bound {
                active_session_id, ..
            } => Some(active_session_id),
        }
    }
}

/// An event that came while its session was being opened.
struct HeldEvent {
    event: Box<SessionEvent>,
    /// The daemon's event sequence; 0 when it gave none.
    sequence: u64,
}

/// What a request answers.
enum Answer {
    Data(Value),
    /// An open attached `active_session_id`: the reply goes out first,
    /// then the events the open held that the snapshot does not hold.
    Opened {
        data: Value,
        active_session_id: String,
        stream: EventStream,
    },
}

/// One row of the daemon's `list` (with `all`): a saved session, or the
/// live summary of the worker that hosts its file.
#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct ListedSession {
    #[serde(default)]
    active_session_id: Option<String>,
    #[serde(default)]
    session_file: Option<String>,
    #[serde(default)]
    attached_clients: u32,
}

/// A worker that hosts a saved session's file.
struct LiveWorker {
    active_session_id: String,
    /// The clients attached to it (the tab itself, when it is bound there).
    attached_clients: u32,
}

/// The session an open binds.
enum Target {
    /// A saved session; `resume` is the cursor of the last event the tab
    /// saw.
    Saved {
        saved: SavedSession,
        resume: Option<DaemonResumeCursor>,
    },
    /// A new session in `cwd`.
    New { cwd: PathBuf },
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
        if let Some(notice) = kept_daemon_notice(Build::THIS, client.daemon_build()) {
            tracing::warn!("{notice}");
        }
        Ok(Self {
            reader_dead: client.reader_dead(),
            config,
            client,
            events,
        })
    }

    /// Serve the tab until it closes or the daemon connection ends.
    #[tracing::instrument(skip_all)]
    pub(crate) async fn run<S>(self, socket: S)
    where
        S: Stream<Item = Result<Message, tungstenite::Error>>
            + Sink<Message, Error = tungstenite::Error>
            + Unpin,
    {
        let Bridge {
            config,
            client,
            mut events,
            mut reader_dead,
        } = self;
        let (outgoing, mut frames) = mpsc::unbounded_channel();
        let tab = Arc::new(Tab {
            config,
            client,
            outgoing,
            binding: Mutex::new(Binding::Unbound),
        });
        let (mut sink, mut stream) = socket.split();
        let mut requests = JoinSet::new();
        loop {
            if *reader_dead.borrow() {
                tracing::info!("the daemon connection ended; closing the tab's socket");
                break;
            }
            tokio::select! {
                message = stream.next() => match message {
                    Some(Ok(Message::Text(text))) => {
                        let tab = Arc::clone(&tab);
                        requests.spawn(async move { tab.answer(text.as_str()).await });
                    }
                    Some(Ok(Message::Close(_))) | None => break,
                    Some(Ok(Message::Binary(_) | Message::Ping(_) | Message::Pong(_) | Message::Frame(_))) => {}
                    Some(Err(error)) => {
                        tracing::debug!(%error, "the tab's socket failed");
                        break;
                    }
                },
                event = events.recv() => match event {
                    Some(event) => tab.forward(event),
                    None => break,
                },
                // The tab holds a sender, so the channel never closes here.
                Some(text) = frames.recv() => {
                    if let Err(error) = sink.send(Message::text(text)).await {
                        tracing::debug!(%error, "sending to the tab failed");
                        break;
                    }
                }
                Some(finished) = requests.join_next(), if !requests.is_empty() => {
                    if let Err(error) = finished {
                        tracing::warn!(%error, "a tab request task failed");
                    }
                }
                changed = reader_dead.changed() => {
                    if changed.is_err() {
                        break;
                    }
                }
            }
        }
        requests.abort_all();
        if let Err(error) = sink.close().await {
            tracing::debug!(%error, "closing the tab's socket failed");
        }
        let bound = tab.binding().active_session_id().map(str::to_string);
        if let Some(active_session_id) = bound {
            if let Err(error) = tab.detach(&active_session_id).await {
                tracing::debug!(error = %format!("{error:#}"), "detach at close failed");
            }
        }
        tab.client.close();
    }
}

impl Tab {
    fn binding(&self) -> MutexGuard<'_, Binding> {
        self.binding.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Queue one frame for the tab.
    fn send(&self, frame: &ServerFrame<'_>) {
        if self.outgoing.send(frame.to_text()).is_err() {
            tracing::debug!("the tab closed before a frame went out");
        }
    }

    /// Queue one event of the bound session with its cursor, unless the
    /// snapshot the tab holds already has it. `sequence` 0: the daemon
    /// gave none.
    fn send_event(&self, event: &SessionEvent, sequence: u64, stream: &EventStream) {
        if sequence != 0 && sequence <= stream.snapshot_sequence {
            return;
        }
        self.send(&ServerFrame::Event {
            event,
            cursor: (sequence != 0).then_some(EventCursor {
                generation: stream.generation.as_deref(),
                sequence,
            }),
        });
    }

    /// Answer one text frame of the tab.
    async fn answer(&self, text: &str) {
        let frame = match serde_json::from_str::<Value>(text) {
            Ok(value) => {
                let id = value.get("id").and_then(Value::as_u64).unwrap_or(0);
                serde_json::from_value::<ClientFrame>(value)
                    .map_err(|error| (id, format!("bad request: {error}")))
            }
            Err(error) => Err((0, format!("bad request: {error}"))),
        };
        let ClientFrame { id, request } = match frame {
            Ok(frame) => frame,
            Err((id, error)) => {
                self.send(&ServerFrame::Failure { id, error });
                return;
            }
        };
        match self.handle(request).await {
            Ok(Answer::Data(data)) => self.send(&ServerFrame::Reply { id, data }),
            Ok(Answer::Opened {
                data,
                active_session_id,
                stream,
            }) => {
                // Under the lock, so no event of the session can slip in
                // between the reply and the held events.
                let mut binding = self.binding();
                self.send(&ServerFrame::Reply { id, data });
                match &mut *binding {
                    Binding::Opening {
                        active_session_id: opening,
                        held,
                    } if *opening == active_session_id => {
                        for HeldEvent { event, sequence } in std::mem::take(held) {
                            self.send_event(&event, sequence, &stream);
                        }
                        *binding = Binding::Bound {
                            active_session_id,
                            stream,
                        };
                    }
                    // Another open, or a resync, replaced this one meanwhile.
                    Binding::Unbound | Binding::Opening { .. } | Binding::Bound { .. } => {}
                }
            }
            Err(error) => self.send(&ServerFrame::Failure {
                id,
                error: format!("{error:#}"),
            }),
        }
    }

    // One arm per op of the protocol.
    #[allow(clippy::too_many_lines)]
    #[tracing::instrument(skip_all)]
    async fn handle(&self, request: Request) -> anyhow::Result<Answer> {
        match request {
            Request::Sessions => Ok(Answer::Data(serde_json::to_value(
                self.root_sessions().await?,
            )?)),
            Request::Open {
                session_id,
                path,
                resume,
            } => {
                let sessions = self.root_sessions().await?;
                let target = match (session_id, path) {
                    (Some(session_id), None) => Target::Saved {
                        saved: sessions
                            .into_iter()
                            .find(|saved| saved.id == session_id)
                            .with_context(|| format!("no saved root session {session_id}"))?,
                        resume,
                    },
                    (None, Some(path)) => Target::Saved {
                        saved: sessions
                            .into_iter()
                            .find(|saved| saved.path == path)
                            .with_context(|| format!("no saved root session at {path}"))?,
                        resume,
                    },
                    (None, None) => match sessions.into_iter().next() {
                        Some(saved) => Target::Saved { saved, resume },
                        None => Target::New {
                            cwd: self.config.new_session_cwd.clone(),
                        },
                    },
                    (Some(_), Some(_)) => {
                        anyhow::bail!("open takes a sessionId or a path, not both")
                    }
                };
                self.open(target).await
            }
            Request::New { cwd } => {
                let cwd = match cwd {
                    Some(cwd) => {
                        let folder = PathBuf::from(&cwd);
                        anyhow::ensure!(
                            folder.is_absolute() && folder.is_dir(),
                            "no folder at {cwd}"
                        );
                        folder
                    }
                    None => self.config.new_session_cwd.clone(),
                };
                self.open(Target::New { cwd }).await
            }
            Request::Prompt {
                text,
                mode,
                admission_id,
                images,
            } => {
                let active_session_id = self.bound()?;
                let images = (!images.is_empty()).then(|| {
                    images
                        .into_iter()
                        .map(|image| {
                            json!({ "type": "image", "data": image.data, "mimeType": image.mime_type })
                        })
                        .collect::<Value>()
                });
                let response = self
                    .client
                    .request(DaemonCommand::Prompt {
                        id: None,
                        active_session_id,
                        message: text,
                        input: PromptInput {
                            content: None,
                            images,
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
                            admission_id: Some(
                                admission_id.unwrap_or_else(|| uuid::Uuid::new_v4().to_string()),
                            ),
                            rlm_notice_nonce: None,
                            reply_to: None,
                        },
                        rest: Map::default(),
                    })
                    .await
                    .context("send the message; it may not have arrived")?;
                if response.success {
                    Ok(Answer::Data(Value::Null))
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
                Ok(Answer::Data(Value::Null))
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
                    .map(Answer::Data)
            }
            Request::Run { mut command } => {
                let active_session_id = self.bound()?;
                let kind = command
                    .get("type")
                    .and_then(Value::as_str)
                    .unwrap_or_default()
                    .to_string();
                // The bridge numbers the daemon's requests and owns the
                // session the command addresses.
                command.remove("id");
                let mut addressed = command.clone();
                addressed.insert("activeSessionId".to_string(), json!(active_session_id));
                let read = |fields: Map<String, Value>| {
                    serde_json::from_value::<DaemonCommand>(Value::Object(fields))
                        .with_context(|| format!("read the {kind:?} command"))
                };
                let addressed = read(addressed)?;
                match verdict(&addressed) {
                    Verdict::Bound => self.client.request_ok(addressed).await.map(Answer::Data),
                    // A catalog command names its sessions itself: with no
                    // session id the supervisor answers for every session
                    // (with one, a worker would answer for its own).
                    Verdict::Catalog => {
                        command.remove("activeSessionId");
                        self.client
                            .request_ok(read(command)?)
                            .await
                            .map(Answer::Data)
                    }
                    Verdict::Refused => anyhow::bail!("the dashboard does not run {kind}"),
                }
            }
            Request::Export { format } => {
                let active_session_id = self.bound()?;
                let (extension, mime_type) = match format {
                    ExportFormat::Html => ("html", "text/html"),
                    ExportFormat::Jsonl => ("jsonl", "application/jsonl"),
                };
                let name = format!("eukhe-session-{active_session_id}.{extension}");
                // A private folder: the transcript never sits where another
                // user of the machine can read it.
                let folder = std::env::temp_dir()
                    .join(format!("eukhe-dashboard-export-{}", uuid::Uuid::new_v4()));
                tokio::fs::DirBuilder::new()
                    .mode(0o700)
                    .create(&folder)
                    .await
                    .with_context(|| format!("create {}", folder.display()))?;
                let file = folder.join(&name);
                let output_path = Some(file.display().to_string());
                let command = match format {
                    ExportFormat::Html => DaemonCommand::ExportHtml {
                        id: None,
                        active_session_id,
                        output_path,
                        // The dashboard registers no themes of its own: the
                        // daemon resolves the session's resource themes.
                        theme_paths: None,
                        rest: Map::default(),
                    },
                    ExportFormat::Jsonl => DaemonCommand::ExportJsonl {
                        id: None,
                        active_session_id,
                        output_path,
                        rest: Map::default(),
                    },
                };
                let exported = match self.client.request_ok(command).await {
                    Ok(_) => tokio::fs::read(&file)
                        .await
                        .with_context(|| format!("read {}", file.display())),
                    Err(error) => Err(error.context("export the session")),
                };
                if let Err(error) = tokio::fs::remove_dir_all(&folder).await {
                    tracing::warn!(%error, folder = %folder.display(), "could not remove the export folder");
                }
                Ok(Answer::Data(json!({
                    "name": name,
                    "mimeType": mime_type,
                    "data": base64::engine::general_purpose::STANDARD.encode(exported?),
                })))
            }
            Request::Delete { session_id } => {
                let saved = self.saved_root(&session_id).await?;
                if let Some(LiveWorker {
                    active_session_id,
                    attached_clients,
                }) = self.live_worker(&saved).await?
                {
                    let here =
                        self.binding().active_session_id() == Some(active_session_id.as_str());
                    let others = attached_clients.saturating_sub(u32::from(here));
                    anyhow::ensure!(
                        others == 0,
                        "the chat is open in another window: close it there first"
                    );
                    // The tab lets its own chat go before its worker stops.
                    let let_go = {
                        let mut binding = self.binding();
                        let bound_here =
                            binding.active_session_id() == Some(active_session_id.as_str());
                        if bound_here {
                            *binding = Binding::Unbound;
                        }
                        bound_here
                    };
                    if let_go {
                        self.detach(&active_session_id).await?;
                    }
                    self.client
                        .request_ok(DaemonCommand::Kill {
                            id: None,
                            active_session_id,
                            rest: Map::default(),
                        })
                        .await
                        .context("stop the chat's worker")?;
                }
                let deleted = self
                    .client
                    .request_ok(DaemonCommand::DeleteSavedSession {
                        id: None,
                        active_session_id: None,
                        session_path: saved.path,
                        rest: Map::default(),
                    })
                    .await
                    .context("delete the chat")?;
                if deleted.get("ok").and_then(Value::as_bool) == Some(false) {
                    anyhow::bail!(
                        "{}",
                        deleted
                            .get("error")
                            .and_then(Value::as_str)
                            .unwrap_or("the daemon did not delete the chat")
                    );
                }
                Ok(Answer::Data(json!({ "deleted": session_id })))
            }
            Request::Rename { session_id, name } => {
                let saved = self.saved_root(&session_id).await?;
                // A live worker owns its file: it renames the session. With
                // none, the catalog renames the saved file.
                if let Some(LiveWorker {
                    active_session_id, ..
                }) = self.live_worker(&saved).await?
                {
                    self.client
                        .request_ok(DaemonCommand::SetSessionName {
                            id: None,
                            active_session_id,
                            name: name.clone(),
                            worker_token: None,
                            rest: Map::default(),
                        })
                        .await
                        .context("rename the chat")?;
                } else {
                    let renamed = self
                        .client
                        .request_ok(DaemonCommand::RenameSavedSession {
                            id: None,
                            active_session_id: None,
                            session_path: saved.path,
                            name: name.clone(),
                            rest: Map::default(),
                        })
                        .await
                        .context("rename the chat")?;
                    if renamed.get("ok").and_then(Value::as_bool) == Some(false) {
                        anyhow::bail!(
                            "{}",
                            renamed
                                .get("error")
                                .and_then(Value::as_str)
                                .unwrap_or("the daemon did not rename the chat")
                        );
                    }
                }
                Ok(Answer::Data(json!({ "renamed": session_id, "name": name })))
            }
        }
    }

    /// The saved root session `session_id` names.
    async fn saved_root(&self, session_id: &str) -> anyhow::Result<SavedSession> {
        self.root_sessions()
            .await?
            .into_iter()
            .find(|saved| saved.id == session_id)
            .with_context(|| format!("no saved root session {session_id}"))
    }

    /// The worker that hosts `saved`'s file, if any: the daemon's list
    /// answers a hosted file with the worker's live summary.
    #[tracing::instrument(skip_all, fields(session = %saved.id))]
    async fn live_worker(&self, saved: &SavedSession) -> anyhow::Result<Option<LiveWorker>> {
        let listed = self
            .client
            .request_ok(DaemonCommand::List {
                id: None,
                all: Some(true),
                cwd: None,
                session_dir: Some(self.config.session_dir.display().to_string()),
                include_client_owned: Some(true),
                rest: Map::default(),
            })
            .await
            .context("list the live sessions")?;
        let rows: Vec<ListedSession> = serde_json::from_value(
            listed
                .get("sessions")
                .cloned()
                .context("the session list has no sessions")?,
        )
        .context("read the session list")?;
        let saved_file = tokio::fs::canonicalize(&saved.path).await.ok();
        for row in rows {
            let (Some(active_session_id), Some(file)) = (row.active_session_id, row.session_file)
            else {
                continue;
            };
            let same_file = file == saved.path
                || (saved_file.is_some()
                    && tokio::fs::canonicalize(&file).await.ok() == saved_file);
            if same_file && !active_session_id.is_empty() {
                return Ok(Some(LiveWorker {
                    active_session_id,
                    attached_clients: row.attached_clients,
                }));
            }
        }
        Ok(None)
    }

    /// The bound session's active id.
    fn bound(&self) -> anyhow::Result<String> {
        match &*self.binding() {
            Binding::Bound {
                active_session_id, ..
            } => Ok(active_session_id.clone()),
            Binding::Unbound | Binding::Opening { .. } => anyhow::bail!("no session is open"),
        }
    }

    #[tracing::instrument(skip_all)]
    async fn root_sessions(&self) -> anyhow::Result<Vec<SavedSession>> {
        list_root_sessions(
            &self.client,
            &self.config.session_dir,
            &self.config.new_session_cwd,
        )
        .await
    }

    /// Open `target` as a resident session, attach the tab to it, and
    /// answer its transcript, state, summary and resume cursor. The daemon
    /// reuses a live worker of the same session, so the CLI, the gateway
    /// and every tab share it. With a resume cursor whose events the tab
    /// already has all of (`replay` `complete`), the transcript is left
    /// out.
    // One linear open: create, rebind, attach, and the reply's fields.
    #[allow(clippy::too_many_lines)]
    #[tracing::instrument(skip_all)]
    async fn open(&self, target: Target) -> anyhow::Result<Answer> {
        let mut create_config = self.config.create_config.clone();
        create_config.insert(
            "sessionDir".to_string(),
            json!(self.config.session_dir.display().to_string()),
        );
        let (session_path, resume) = match target {
            Target::Saved { saved, resume } => {
                if !saved.cwd.is_empty() && !Path::new(&saved.cwd).exists() {
                    tracing::warn!(missing = %saved.cwd, "the session folder is missing; using the new-session folder");
                    create_config.insert(
                        "cwd".to_string(),
                        json!(self.config.new_session_cwd.display().to_string()),
                    );
                }
                (Some(saved.path), resume)
            }
            Target::New { cwd } => {
                create_config.insert("cwd".to_string(), json!(cwd.display().to_string()));
                (None, None)
            }
        };
        let CreatedSession {
            active_session_id,
            session_id,
            session_file: path,
        } = create_resident(&self.client, session_path, Value::Object(create_config)).await?;
        let previous = {
            let mut binding = self.binding();
            let previous = binding.active_session_id().map(str::to_string);
            *binding = Binding::Opening {
                active_session_id: active_session_id.clone(),
                held: Vec::new(),
            };
            previous
        };
        if let Some(previous) = previous.filter(|previous| *previous != active_session_id) {
            if let Err(error) = self.detach(&previous).await {
                tracing::warn!(error = %format!("{error:#}"), "detach from the previous session failed");
            }
        }
        let resumed = resume.is_some();
        let attached = self
            .client
            .request_ok(DaemonCommand::Attach {
                id: None,
                active_session_id: active_session_id.clone(),
                client_id: None,
                capabilities: Some(ATTACH_CAPABILITIES.map(str::to_string).to_vec()),
                resume_cursor: resume,
                recovery_config: None,
                env: None,
                launch_env: None,
                rest: Map::default(),
            })
            .await
            .context("attach to the session");
        let mut attached = match attached {
            Ok(attached) => attached,
            Err(error) => {
                let mut binding = self.binding();
                if matches!(&*binding, Binding::Opening { active_session_id: opening, .. } if *opening == active_session_id)
                {
                    *binding = Binding::Unbound;
                }
                return Err(error);
            }
        };
        let mut snapshot = attached
            .get_mut("snapshot")
            .map(Value::take)
            .context("the attach answer has no snapshot")?;
        let take = |value: &mut Value, key: &str| {
            value
                .get_mut(key)
                .map(Value::take)
                .filter(|value| !value.is_null())
        };
        let cursor = take(&mut attached, "lastEventCursor")
            .or_else(|| take(&mut snapshot, "lastEventCursor"))
            .unwrap_or(Value::Null);
        let stream = EventStream {
            generation: cursor
                .get("generation")
                .and_then(Value::as_str)
                .map(str::to_string),
            snapshot_sequence: cursor
                .get("sequence")
                .or_else(|| attached.get("lastEventSequence"))
                .and_then(Value::as_u64)
                .unwrap_or_default(),
        };
        let replay = resumed.then(|| {
            attached
                .get("replay")
                .and_then(|replay| replay.get("status"))
                .and_then(|status| DaemonReplayStatus::deserialize(status).ok())
                .unwrap_or(DaemonReplayStatus::Unavailable)
        });
        let messages = match replay {
            Some(DaemonReplayStatus::Complete) => Value::Null,
            Some(DaemonReplayStatus::Partial | DaemonReplayStatus::Unavailable) | None => {
                take(&mut snapshot, "messages").unwrap_or_else(|| json!([]))
            }
        };
        tracing::info!(%path, %active_session_id, ?replay, "a tab attached");
        Ok(Answer::Opened {
            data: json!({
                "session": { "id": session_id, "path": path },
                "state": take(&mut snapshot, "state").unwrap_or(Value::Null),
                "summary": take(&mut snapshot, "summary").unwrap_or(Value::Null),
                "messages": messages,
                "cursor": cursor,
                "replay": replay,
            }),
            active_session_id,
            stream,
        })
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

    /// Push one daemon event to the tab when it concerns the bound session.
    fn forward(&self, event: DaemonClientEvent) {
        let mut binding = self.binding();
        // The session is gone or moved: the tab opens it again.
        let resync = |binding: &mut Binding, active_session_id: &str, reason: String| {
            if binding.active_session_id() == Some(active_session_id) {
                *binding = Binding::Unbound;
                self.send(&ServerFrame::Resync { reason });
            }
        };
        match event {
            DaemonClientEvent::SessionEvent {
                active_session_id,
                event,
                meta_sequence,
            } => match &mut *binding {
                Binding::Bound {
                    active_session_id: bound,
                    stream,
                } if *bound == active_session_id => self.send_event(&event, meta_sequence, stream),
                Binding::Opening {
                    active_session_id: opening,
                    held,
                } if *opening == active_session_id => held.push(HeldEvent {
                    event,
                    sequence: meta_sequence,
                }),
                Binding::Unbound | Binding::Opening { .. } | Binding::Bound { .. } => {}
            },
            DaemonClientEvent::ShellApproval {
                active_session_id,
                request,
            } => {
                if binding.active_session_id() == Some(active_session_id.as_str()) {
                    self.send(&ServerFrame::Approval { request: &request });
                }
            }
            DaemonClientEvent::SessionClosed {
                active_session_id,
                reason,
            } => resync(
                &mut binding,
                &active_session_id,
                format!("the session closed ({reason})"),
            ),
            DaemonClientEvent::SessionBinding {
                previous_active_session_id,
                ..
            } => resync(
                &mut binding,
                &previous_active_session_id,
                "the session moved to a new worker".to_string(),
            ),
            DaemonClientEvent::DirectLinkLost { active_session_id } => resync(
                &mut binding,
                &active_session_id,
                "the link to the session's worker was lost".to_string(),
            ),
            DaemonClientEvent::UndecodableSessionEvent {
                active_session_id,
                error,
            } => {
                tracing::warn!(%active_session_id, %error, "a session event could not be decoded");
            }
            DaemonClientEvent::DaemonClosing { reason } => {
                tracing::info!(%reason, "the daemon is closing");
            }
            DaemonClientEvent::SessionListItem { .. }
            | DaemonClientEvent::SessionListProgress { .. }
            | DaemonClientEvent::SideQuestionEvent { .. }
            | DaemonClientEvent::RosterUpdate { .. }
            | DaemonClientEvent::StateTreeUpdate { .. }
            | DaemonClientEvent::HeartbeatsChanged => {}
        }
    }
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use eukhe_types::shell::{ShellApprovalRequest, ShellEffect};
    use std::io::{BufRead, BufReader, Write};

    #[tokio::test]
    async fn only_the_bound_sessions_news_reaches_the_tab() {
        // A daemon that only greets: forwarding never asks it anything.
        let dir = tempfile::tempdir().expect("tempdir");
        let socket_path = dir.path().join("daemon.sock");
        let listener = std::os::unix::net::UnixListener::bind(&socket_path).expect("bind");
        std::thread::spawn(move || {
            let (mut stream, _) = listener.accept().expect("accept");
            let hello = json!({
                "type": "daemon_hello",
                "protocol": { "name": "eukhe.daemon", "version": 7 },
                "serverCapabilities": [],
                "clientId": "mock",
            });
            writeln!(stream, "{hello}").expect("greet");
            for line in BufReader::new(stream).lines() {
                if line.is_err() {
                    break;
                }
            }
        });
        let (client, _events) = DaemonClient::connect(&socket_path).await.expect("connect");
        let (outgoing, mut frames) = mpsc::unbounded_channel();
        let tab = Tab {
            config: Arc::new(DashboardConfig {
                socket_path,
                session_dir: dir.path().to_path_buf(),
                new_session_cwd: dir.path().to_path_buf(),
                create_config: Map::new(),
                allowed_hosts: Vec::new(),
            }),
            client,
            outgoing,
            binding: Mutex::new(Binding::Bound {
                active_session_id: "s1".to_string(),
                stream: EventStream {
                    generation: Some("g1".to_string()),
                    snapshot_sequence: 3,
                },
            }),
        };
        let event = |active_session_id: &str, meta_sequence| DaemonClientEvent::SessionEvent {
            active_session_id: active_session_id.to_string(),
            event: Box::new(SessionEvent::AgentStart),
            meta_sequence,
        };
        let approval = |active_session_id: &str| DaemonClientEvent::ShellApproval {
            active_session_id: active_session_id.to_string(),
            request: ShellApprovalRequest {
                request_id: format!("r-{active_session_id}"),
                step: 1,
                command: "make".to_string(),
                effect: ShellEffect::Exec,
            },
        };
        let lost = |active_session_id: &str| DaemonClientEvent::DirectLinkLost {
            active_session_id: active_session_id.to_string(),
        };
        for news in [
            // Already in the snapshot the tab holds.
            event("s1", 3),
            event("s1", 4),
            event("s2", 5),
            // No sequence from the daemon: no cursor.
            event("s1", 0),
            approval("s2"),
            approval("s1"),
            lost("s2"),
            lost("s1"),
            // Unbound now: the tab opens the session again first.
            event("s1", 6),
            approval("s1"),
        ] {
            tab.forward(news);
        }
        drop(tab);
        let mut pushed = Vec::new();
        while let Some(text) = frames.recv().await {
            pushed.push(serde_json::from_str::<Value>(&text).expect("JSON frame"));
        }
        assert_eq!(
            pushed,
            [
                json!({
                    "type": "event", "event": { "type": "agent_start" },
                    "cursor": { "generation": "g1", "sequence": 4 },
                }),
                json!({ "type": "event", "event": { "type": "agent_start" } }),
                json!({
                    "type": "approval",
                    "request": { "requestId": "r-s1", "step": 1, "command": "make", "effect": "exec" },
                }),
                json!({ "type": "resync", "reason": "the link to the session's worker was lost" }),
            ]
        );
    }
}
