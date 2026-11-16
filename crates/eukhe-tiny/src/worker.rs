//! The worker process of one model and backend: binds the model's socket
//! (or adopts a live worker on it), then serves [`Request`] lines, one
//! [`Response`] each, in order, until a shutdown or the idle window.

use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use tokio::io::{AsyncWriteExt, BufReader};
use tokio::net::{UnixListener, UnixStream};
use tokio::sync::watch;
use tokio::task::JoinSet;
use tokio::time::Instant;

use crate::catalog::{find, CatalogModel};
use crate::election::{seat, Seated};
use crate::engine::{Engine, EngineFactory, EngineOptions};
use crate::paths::{Backend, TinyHome};
use crate::protocol::{read_line, Line, Reply, Request, Response, WorkerFailure, MAX_LINE_BYTES};

/// The idle window without `--idle-secs`.
const DEFAULT_IDLE_SECS: u64 = 900;

/// Overrides the idle window, in milliseconds (tests).
const IDLE_MS_ENV: &str = "EUKHE_TINY_WORKER_IDLE_MS";

const USAGE: &str = "usage: eukhe tiny-worker <model> --backend onnx --agent-dir DIR [--device D] \
                     [--dtype T] [--runtime-library P] [--idle-secs N]";

/// The tag a worker answers ping with: this build and the settings it
/// launched with. A client replaces a worker whose tag differs from its
/// own.
#[must_use]
pub fn launch_tag(backend: Backend, options: &EngineOptions) -> String {
    format!(
        "{}|{}|{}|{}",
        eukhe_build_info::BUILD_ID,
        backend.id(),
        options.device,
        options.dtype
    )
}

/// The idle window: `idle_secs`, unless `env` (the value of
/// `EUKHE_TINY_WORKER_IDLE_MS`) holds milliseconds; an unusable value is
/// ignored, and said why.
fn idle_window(
    idle_secs: u64,
    env: Result<String, std::env::VarError>,
) -> (Duration, Option<IgnoredEnv>) {
    match env {
        Ok(value) => match value.parse() {
            Ok(millis) => (Duration::from_millis(millis), None),
            Err(error) => (
                Duration::from_secs(idle_secs),
                Some(IgnoredEnv::Invalid { value, error }),
            ),
        },
        Err(std::env::VarError::NotPresent) => (Duration::from_secs(idle_secs), None),
        Err(std::env::VarError::NotUnicode(value)) => (
            Duration::from_secs(idle_secs),
            Some(IgnoredEnv::NotUnicode(value)),
        ),
    }
}

/// Why the idle window ignored `EUKHE_TINY_WORKER_IDLE_MS`.
enum IgnoredEnv {
    Invalid {
        value: String,
        error: std::num::ParseIntError,
    },
    NotUnicode(std::ffi::OsString),
}

/// The idle window of this process's environment; an ignored value warns.
fn read_idle_window(idle_secs: u64) -> Duration {
    let (idle, ignored) = idle_window(idle_secs, std::env::var(IDLE_MS_ENV));
    match ignored {
        Some(IgnoredEnv::Invalid { value, error }) => {
            tracing::warn!("ignoring {IDLE_MS_ENV}={value:?}: {error}");
        }
        Some(IgnoredEnv::NotUnicode(value)) => {
            tracing::warn!(
                "ignoring {IDLE_MS_ENV}: {}",
                std::env::VarError::NotUnicode(value)
            );
        }
        None => {}
    }
    idle
}

/// The command line of `eukhe tiny-worker`.
#[derive(Debug, Clone, PartialEq, Eq)]
struct WorkerArgs {
    model: String,
    backend: Backend,
    /// The launching client's agent dir: the models and the socket are
    /// under it.
    agent_dir: PathBuf,
    options: EngineOptions,
    idle_secs: u64,
}

/// Why the `eukhe tiny-worker` command line was refused.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
enum WorkerArgsError {
    #[error("{flag} needs a value")]
    MissingValue { flag: String },
    #[error("unknown backend {id:?}")]
    UnknownBackend { id: String },
    #[error("--idle-secs {value:?}: {source}")]
    IdleSecs {
        value: String,
        #[source]
        source: std::num::ParseIntError,
    },
    #[error("unknown option {flag}")]
    UnknownOption { flag: String },
    #[error("unexpected argument {word:?}")]
    UnexpectedArgument { word: String },
    #[error("missing <model>")]
    MissingModel,
    #[error("missing --backend")]
    MissingBackend,
    #[error("missing --agent-dir")]
    MissingAgentDir,
}

/// Why a request line could not be read as a [`Request`].
#[derive(Debug, thiserror::Error)]
enum RequestLineError {
    #[error("{source}")]
    Json {
        #[source]
        source: serde_json::Error,
    },
    #[error("the request line is over {MAX_LINE_BYTES} bytes")]
    TooLong,
}

impl WorkerArgs {
    fn parse(args: &[String]) -> Result<WorkerArgs, WorkerArgsError> {
        let mut model = None;
        let mut backend = None;
        let mut agent_dir = None;
        let mut options = EngineOptions {
            device: "cpu".to_owned(),
            dtype: String::new(),
            runtime_library: PathBuf::new(),
        };
        let mut idle_secs = DEFAULT_IDLE_SECS;
        let mut words = args.iter();
        while let Some(word) = words.next() {
            let mut value = || {
                words
                    .next()
                    .cloned()
                    .ok_or_else(|| WorkerArgsError::MissingValue { flag: word.clone() })
            };
            match word.as_str() {
                "--backend" => {
                    let id = value()?;
                    backend =
                        Some(Backend::parse(&id).ok_or(WorkerArgsError::UnknownBackend { id })?);
                }
                "--agent-dir" => agent_dir = Some(PathBuf::from(value()?)),
                "--device" => options.device = value()?,
                "--dtype" => options.dtype = value()?,
                "--runtime-library" => options.runtime_library = PathBuf::from(value()?),
                "--idle-secs" => {
                    let secs = value()?;
                    idle_secs = secs.parse().map_err(|source| WorkerArgsError::IdleSecs {
                        value: secs,
                        source,
                    })?;
                }
                flag if flag.starts_with("--") => {
                    return Err(WorkerArgsError::UnknownOption {
                        flag: flag.to_owned(),
                    })
                }
                id => match model {
                    None => model = Some(id.to_owned()),
                    Some(_) => {
                        return Err(WorkerArgsError::UnexpectedArgument {
                            word: id.to_owned(),
                        })
                    }
                },
            }
        }
        Ok(WorkerArgs {
            model: model.ok_or(WorkerArgsError::MissingModel)?,
            backend: backend.ok_or(WorkerArgsError::MissingBackend)?,
            agent_dir: agent_dir.ok_or(WorkerArgsError::MissingAgentDir)?,
            options,
            idle_secs,
        })
    }
}

/// `eukhe tiny-worker <model> --backend onnx --agent-dir DIR [--device D]
/// [--dtype T] [--runtime-library P] [--idle-secs N]` (`args` are the words
/// after `tiny-worker`): opens the model with `factory`, then binds its
/// socket under the agent dir `DIR` and prints `ready`, or prints `adopted`
/// when a live worker already answers there; serves until a shutdown or the
/// idle window (`--idle-secs`, default 900; `EUKHE_TINY_WORKER_IDLE_MS`
/// overrides it). Failures go to stderr (the worker's log); a bad command
/// line exits 2, any other failure 1.
pub async fn run_worker(args: &[String], factory: EngineFactory) -> ExitCode {
    let args = match WorkerArgs::parse(args) {
        Ok(args) => args,
        Err(error) => {
            eprintln!("tiny-worker: {error}\n{USAGE}");
            return ExitCode::from(2);
        }
    };
    let Some(model) = find(&args.model) else {
        eprintln!(
            "tiny-worker: no local model {:?} in the catalog",
            args.model
        );
        return ExitCode::from(2);
    };
    let home = TinyHome::under(&args.agent_dir);
    let engine = match factory(model, home.model_dir(model.id), &args.options) {
        Ok(engine) => engine,
        Err(error) => {
            eprintln!("tiny-worker: {}: {error}", model.id);
            return ExitCode::FAILURE;
        }
    };
    let listening = match bind(&home, model, args.backend).await {
        Ok(Bound::Listening(listening)) => listening,
        Ok(Bound::Adopted) => return announce("adopted"),
        Err(error) => {
            eprintln!("tiny-worker: {}: cannot bind: {error}", model.id);
            return ExitCode::FAILURE;
        }
    };
    let announced = announce("ready");
    let tag = launch_tag(args.backend, &args.options);
    match serve(listening, tag, engine, read_idle_window(args.idle_secs)).await {
        Ok(exit) => {
            eprintln!("tiny-worker: {}: exit ({exit:?})", model.id);
            announced
        }
        Err(error) => {
            eprintln!("tiny-worker: {}: {error}", model.id);
            ExitCode::FAILURE
        }
    }
}

/// Prints the start line the launching client waits for.
fn announce(line: &str) -> ExitCode {
    let mut stdout = io::stdout();
    match writeln!(stdout, "{line}").and_then(|()| stdout.flush()) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("tiny-worker: cannot print {line:?}: {error}");
            ExitCode::FAILURE
        }
    }
}

/// How a start ended.
pub(crate) enum Bound {
    /// The socket is bound: serve it.
    Listening(Listening),
    /// A live worker answers on the socket: leave it.
    Adopted,
}

/// A bound worker socket.
pub(crate) struct Listening {
    listener: UnixListener,
    socket: PathBuf,
}

/// Why [`serve`] returned.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Exit {
    /// A client sent [`Request::Shutdown`].
    Shutdown,
    /// No request came for the idle window.
    Idle,
}

/// Binds the socket of `model` on `backend` under `home`, unless a live
/// worker answers on it, as the seat run decides ([`seat`]): the probe and
/// the bind run under the bind lock (`flock`), held across them only. A
/// stale socket is removed first. Creates the run dir and makes it 0700.
///
/// # Errors
///
/// The run dir, the lock, the probe or the bind fails.
#[tracing::instrument(level = "debug", skip(home, model), fields(model = model.id))]
pub(crate) async fn bind(
    home: &TinyHome,
    model: &CatalogModel,
    backend: Backend,
) -> io::Result<Bound> {
    home.create_run_dir()?;
    let lock_path = home.bind_lock(model.id, backend);
    let socket = home.socket(model.id, backend);
    let take_lock = || async move {
        tokio::task::spawn_blocking(move || {
            let file = std::fs::OpenOptions::new()
                .create(true)
                .truncate(false)
                .write(true)
                .open(lock_path)?;
            file.lock()?;
            Ok::<_, io::Error>(file)
        })
        .await
        .map_err(io::Error::other)?
    };
    match seat(&socket, take_lock).await? {
        Seated::Adopt => Ok(Bound::Adopted),
        Seated::Take(lock) => {
            remove_socket(&socket)?;
            let listener = UnixListener::bind(&socket)?;
            drop(lock);
            Ok(Bound::Listening(Listening { listener, socket }))
        }
    }
}

fn remove_socket(socket: &std::path::Path) -> io::Result<()> {
    match std::fs::remove_file(socket) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(error),
    }
}

/// When the worker last finished a request, or how many are in flight.
enum Activity {
    Idle { since: Instant },
    Busy { requests: std::num::NonZeroU32 },
}

impl Activity {
    fn start(self) -> Activity {
        match self {
            Activity::Idle { .. } => Activity::Busy {
                requests: std::num::NonZeroU32::MIN,
            },
            Activity::Busy { requests } => Activity::Busy {
                requests: std::num::NonZeroU32::new(requests.get().saturating_add(1))
                    .unwrap_or(std::num::NonZeroU32::MAX),
            },
        }
    }

    fn finish(self, now: Instant) -> Activity {
        match self {
            Activity::Idle { since } => Activity::Idle { since },
            Activity::Busy { requests } => match requests.get() {
                1 => Activity::Idle { since: now },
                count => Activity::Busy {
                    requests: std::num::NonZeroU32::new(count - 1)
                        .unwrap_or(std::num::NonZeroU32::MIN),
                },
            },
        }
    }
}

/// What a connection tells the serve loop about its requests.
enum Event {
    Started,
    Finished(Instant),
}

/// Whether the worker still takes connections and requests: a
/// [`Request::Shutdown`] makes it `Closing`, and it exits once the requests
/// in flight are answered.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Serving {
    Open,
    Closing,
}

/// What every connection of one worker shares.
struct Shared {
    tag: String,
    socket: PathBuf,
    engine: Mutex<Box<dyn Engine>>,
    events: tokio::sync::mpsc::UnboundedSender<Event>,
    closing: watch::Sender<Serving>,
}

impl Shared {
    /// Runs `infer` on the engine on the blocking pool, one at a time.
    async fn infer(
        self: &Arc<Shared>,
        infer: impl FnOnce(&mut dyn Engine) -> Result<Reply, WorkerFailure> + Send + 'static,
    ) -> Response {
        let shared = Arc::clone(self);
        match tokio::task::spawn_blocking(move || {
            let mut engine = shared.engine.lock().unwrap_or_else(PoisonError::into_inner);
            infer(engine.as_mut())
        })
        .await
        {
            Ok(Ok(reply)) => Response::Ok { reply },
            Ok(Err(error)) => Response::Err { error },
            Err(error) => Response::Err {
                error: WorkerFailure::Inference {
                    message: format!("the engine stopped: {error}"),
                },
            },
        }
    }
}

/// When the worker goes idle: `idle` after the last request finished, or
/// `idle` from `now` while requests are in flight.
fn deadline(activity: &Activity, idle: Duration, now: Instant) -> Instant {
    match activity {
        Activity::Idle { since } => *since + idle,
        Activity::Busy { .. } => now + idle,
    }
}

/// Whether the worker has been idle for `idle` at `now`.
fn is_idle(activity: &Activity, idle: Duration, now: Instant) -> bool {
    match activity {
        Activity::Idle { since } => *since + idle <= now,
        Activity::Busy { .. } => false,
    }
}

/// Serves `listening` with `engine`, answering ping with `tag`, until a
/// [`Request::Shutdown`] or `idle` without a request. On a shutdown the
/// socket is unlinked at once (a new worker may bind it), no connection or
/// request is taken any more, and the requests in flight (of other
/// clients) get their answers before it returns. The idle exit unlinks the
/// socket before it returns. The loop owns the [`Activity`]; connections
/// report theirs as [`Event`]s.
///
/// # Errors
///
/// Accepting a connection fails (the socket is unlinked first).
#[tracing::instrument(level = "debug", skip_all, fields(socket = %listening.socket.display()))]
pub(crate) async fn serve(
    listening: Listening,
    tag: String,
    engine: Box<dyn Engine>,
    idle: Duration,
) -> io::Result<Exit> {
    let Listening { listener, socket } = listening;
    let (event_tx, mut events) = tokio::sync::mpsc::unbounded_channel();
    let mut activity = Activity::Idle {
        since: Instant::now(),
    };
    let shared = Arc::new(Shared {
        tag,
        socket,
        engine: Mutex::new(engine),
        events: event_tx,
        closing: watch::Sender::new(Serving::Open),
    });
    let mut closing = shared.closing.subscribe();
    let mut connections = JoinSet::new();
    loop {
        let now = Instant::now();
        let deadline = deadline(&activity, idle, now);
        tokio::select! {
            accepted = listener.accept() => match accepted {
                Ok((stream, _)) => { connections.spawn(connection(Arc::clone(&shared), stream)); }
                Err(error) => { remove_socket(&shared.socket)?; return Err(error); }
            },
            _ = closing.wait_for(|state| *state == Serving::Closing) => break,
            Some(event) = events.recv() => {
                activity = match event {
                    Event::Started => activity.start(),
                    Event::Finished(at) => activity.finish(at),
                };
            }
            () = tokio::time::sleep_until(deadline) => {
                while let Ok(event) = events.try_recv() {
                    activity = match event {
                        Event::Started => activity.start(),
                        Event::Finished(at) => activity.finish(at),
                    };
                }
                if is_idle(&activity, idle, Instant::now()) {
                    remove_socket(&shared.socket)?;
                    return Ok(Exit::Idle);
                }
            },
            Some(result) = connections.join_next() => match result {
                Ok(()) => {}
                Err(error) => tracing::warn!("worker connection task failed: {error}"),
            }
        }
    }
    drop(listener);
    while let Some(result) = connections.join_next().await {
        match result {
            Ok(()) => {}
            Err(error) => tracing::warn!("worker connection task failed: {error}"),
        }
    }
    Ok(Exit::Shutdown)
}

/// The request a line holds.
fn parse_request(line: Result<String, RequestLineError>) -> Result<Request, RequestLineError> {
    line.and_then(|line| {
        serde_json::from_str(&line).map_err(|source| RequestLineError::Json { source })
    })
}

/// Whether a connection goes on after a response.
#[derive(Debug, PartialEq, Eq)]
enum After {
    Continue,
    Close,
}

/// The response to one request, and whether the connection goes on.
async fn answer(
    shared: &Arc<Shared>,
    request: Result<Request, RequestLineError>,
) -> (Response, After) {
    match request {
        Err(error) => (
            Response::Err {
                error: WorkerFailure::BadRequest {
                    message: error.to_string(),
                },
            },
            After::Continue,
        ),
        Ok(Request::Ping) => (
            Response::Ok {
                reply: Reply::Pong {
                    tag: shared.tag.clone(),
                },
            },
            After::Continue,
        ),
        Ok(Request::Shutdown) => {
            if let Err(error) = remove_socket(&shared.socket) {
                tracing::warn!("cannot unlink {}: {error}", shared.socket.display());
            }
            (Response::Ok { reply: Reply::Bye }, After::Close)
        }
        Ok(Request::Load) => (
            shared
                .infer(|engine| engine.load().map(|()| Reply::Loaded))
                .await,
            After::Continue,
        ),
        Ok(Request::Chat(request)) => (
            shared
                .infer(move |engine| engine.chat(&request).map(Reply::Chat))
                .await,
            After::Continue,
        ),
        Ok(Request::Transcribe(request)) => (
            shared
                .infer(move |engine| engine.transcribe(&request).map(Reply::Transcript))
                .await,
            After::Continue,
        ),
        Ok(Request::Speak(request)) => (
            shared
                .infer(move |engine| engine.speak(&request).map(Reply::Speech))
                .await,
            After::Continue,
        ),
    }
}

/// Writes `response` as one line.
async fn write_response(
    write: &mut tokio::net::unix::OwnedWriteHalf,
    response: &Response,
) -> io::Result<()> {
    let mut line = Vec::with_capacity(256);
    serde_json::to_writer(&mut line, response).map_err(io::Error::other)?;
    line.push(b'\n');
    write.write_all(&line).await?;
    write.flush().await
}

/// Serves one client connection: one response line per request line, in
/// order.
#[tracing::instrument(level = "debug", skip_all)]
async fn connection(shared: Arc<Shared>, stream: UnixStream) {
    let (read, mut write) = stream.into_split();
    let mut reader = BufReader::new(read);
    let mut closing = shared.closing.subscribe();
    loop {
        let line = tokio::select! {
            biased;
            _ = closing.wait_for(|state| *state == Serving::Closing) => return,
            line = read_line(&mut reader, MAX_LINE_BYTES) => match line {
                Ok(Line::Text(line)) => Ok(line),
                Ok(Line::TooLong) => Err(RequestLineError::TooLong),
                Ok(Line::End) => return,
                Err(error) => { tracing::debug!("client connection failed: {error}"); return; }
            },
        };
        // The receiver lives as long as the serve loop that spawned this
        // connection, so a failed send only means the worker is exiting.
        let _ = shared.events.send(Event::Started);
        let (response, after) = answer(&shared, parse_request(line)).await;
        let written = write_response(&mut write, &response).await;
        let _ = shared.events.send(Event::Finished(Instant::now()));
        match after {
            After::Close => {
                shared.closing.send_replace(Serving::Closing);
                return;
            }
            After::Continue => {}
        }
        if let Err(error) = written {
            tracing::debug!("cannot answer the client: {error}");
            return;
        }
    }
}

#[cfg(test)]
mod tests {
    use std::os::unix::ffi::OsStringExt;
    use std::os::unix::fs::PermissionsExt;
    use std::sync::mpsc;

    use super::*;
    use crate::election::{probe, Met};
    use crate::protocol::{
        Audio, ChatMessage, ChatReply, ChatRequest, ChatRole, SpeakRequest, StopReason,
        TranscribeRequest, Transcript,
    };
    use crate::testing::{Echo, ECHO};

    fn words(line: &str) -> Vec<String> {
        line.split_whitespace().map(str::to_owned).collect()
    }

    #[test]
    fn the_command_line_parses_every_option() {
        assert_eq!(
            WorkerArgs::parse(&words(
                "kokoro --backend onnx --agent-dir /a --device cuda --dtype fp16 --runtime-library /x/libonnxruntime.so --idle-secs 30"
            )),
            Ok(WorkerArgs {
                model: "kokoro".to_owned(),
                backend: Backend::Onnx,
                agent_dir: PathBuf::from("/a"),
                options: EngineOptions {
                    device: "cuda".to_owned(),
                    dtype: "fp16".to_owned(),
                    runtime_library: PathBuf::from("/x/libonnxruntime.so"),
                },
                idle_secs: 30,
            })
        );
        assert_eq!(
            WorkerArgs::parse(&words("whisper-base --backend onnx --agent-dir /a")),
            Ok(WorkerArgs {
                model: "whisper-base".to_owned(),
                backend: Backend::Onnx,
                agent_dir: PathBuf::from("/a"),
                options: EngineOptions {
                    device: "cpu".to_owned(),
                    dtype: String::new(),
                    runtime_library: PathBuf::new(),
                },
                idle_secs: DEFAULT_IDLE_SECS,
            })
        );
    }

    #[test]
    fn a_bad_command_line_is_refused() {
        assert_eq!(
            WorkerArgs::parse(&words("kokoro --agent-dir /a")).map_err(|error| error.to_string()),
            Err("missing --backend".to_owned())
        );
        assert_eq!(
            WorkerArgs::parse(&words("kokoro --backend onnx")).map_err(|error| error.to_string()),
            Err("missing --agent-dir".to_owned())
        );
        assert_eq!(
            WorkerArgs::parse(&words("kokoro --backend llama")).map_err(|error| error.to_string()),
            Err("unknown backend \"llama\"".to_owned())
        );
        assert_eq!(
            WorkerArgs::parse(&words("kokoro --backend onnx --idle-secs"))
                .map_err(|error| error.to_string()),
            Err("--idle-secs needs a value".to_owned())
        );
        assert_eq!(
            WorkerArgs::parse(&words("kokoro whisper-base --backend onnx"))
                .map_err(|error| error.to_string()),
            Err("unexpected argument \"whisper-base\"".to_owned())
        );
    }

    /// An engine whose chat tells `started` it began, then waits for
    /// `release`.
    struct Gated {
        started: mpsc::Sender<()>,
        release: mpsc::Receiver<()>,
    }

    impl Engine for Gated {
        fn load(&mut self) -> Result<(), WorkerFailure> {
            Ok(())
        }

        fn chat(&mut self, _request: &ChatRequest) -> Result<ChatReply, WorkerFailure> {
            self.started.send(()).expect("the test waits for the start");
            self.release.recv().expect("the test releases the chat");
            Ok(ChatReply {
                text: "slow".to_owned(),
                stop: StopReason::Eos,
            })
        }

        fn transcribe(
            &mut self,
            _request: &TranscribeRequest,
        ) -> Result<Transcript, WorkerFailure> {
            Err(WorkerFailure::Unsupported {
                op: "transcribe".to_owned(),
            })
        }

        fn speak(&mut self, _request: &SpeakRequest) -> Result<Audio, WorkerFailure> {
            Err(WorkerFailure::Unsupported {
                op: "speak".to_owned(),
            })
        }
    }

    async fn connect(socket: &std::path::Path) -> crate::election::Connection {
        match probe(socket).await {
            Met::Pong { connection, .. } => connection,
            Met::Missing | Met::Unreachable(_) | Met::Odd(_) | Met::Garbled(_) | Met::Hung => {
                panic!("no worker on {}", socket.display())
            }
        }
    }

    /// A shutdown from one client (a replacing process) lets the request
    /// another client has in flight finish with its full answer.
    #[tokio::test]
    async fn a_shutdown_lets_the_requests_in_flight_finish() {
        let dir = tempfile::tempdir().unwrap();
        let home = TinyHome::under(dir.path());
        let Bound::Listening(listening) = bind(&home, &ECHO, Backend::Onnx).await.unwrap() else {
            panic!("a fresh run dir has no live worker");
        };
        let socket = home.socket(ECHO.id, Backend::Onnx);
        let (started, chat_started) = mpsc::channel();
        let (release, released) = mpsc::channel();
        let engine = Box::new(Gated {
            started,
            release: released,
        });
        let server = tokio::spawn(serve(
            listening,
            "tag".to_owned(),
            engine,
            Duration::from_mins(5),
        ));
        let mut a = connect(&socket).await;
        let mut b = connect(&socket).await;
        let chat = tokio::spawn(async move {
            a.call(&Request::Chat(ChatRequest {
                messages: vec![ChatMessage {
                    role: ChatRole::User,
                    content: "hi".to_owned(),
                }],
                prefill: String::new(),
                stop: Vec::new(),
                max_tokens: 8,
            }))
            .await
        });
        tokio::task::spawn_blocking(move || chat_started.recv())
            .await
            .unwrap()
            .unwrap();
        let bye = b.call(&Request::Shutdown).await.unwrap();
        release.send(()).unwrap();
        assert_eq!(
            (
                bye,
                chat.await.unwrap().unwrap(),
                server.await.unwrap().unwrap(),
                socket.exists()
            ),
            (
                Response::Ok { reply: Reply::Bye },
                Response::Ok {
                    reply: Reply::Chat(ChatReply {
                        text: "slow".to_owned(),
                        stop: StopReason::Eos,
                    }),
                },
                Exit::Shutdown,
                false,
            )
        );
    }

    #[tokio::test]
    async fn binding_adopts_an_existing_worker() {
        let dir = tempfile::tempdir().unwrap();
        let home = TinyHome::under(dir.path());
        let Bound::Listening(listening) = bind(&home, &ECHO, Backend::Onnx).await.unwrap() else {
            panic!("a fresh run dir has no live worker");
        };
        let socket = home.socket(ECHO.id, Backend::Onnx);
        let server = tokio::spawn(serve(
            listening,
            "tag".to_owned(),
            Box::new(Echo),
            Duration::from_secs(60),
        ));
        assert!(matches!(
            bind(&home, &ECHO, Backend::Onnx).await,
            Ok(Bound::Adopted)
        ));
        let mut connection = connect(&socket).await;
        assert_eq!(
            connection.call(&Request::Shutdown).await.unwrap(),
            Response::Ok { reply: Reply::Bye }
        );
        assert_eq!(server.await.unwrap().unwrap(), Exit::Shutdown);
    }

    /// A run dir that exists with looser permissions is made 0700.
    #[tokio::test]
    async fn binding_makes_an_existing_run_dir_private() {
        let dir = tempfile::tempdir().unwrap();
        let home = TinyHome::under(dir.path());
        std::fs::create_dir_all(&home.run).unwrap();
        std::fs::set_permissions(&home.run, std::fs::Permissions::from_mode(0o755)).unwrap();
        let bound = bind(&home, &ECHO, Backend::Onnx).await.unwrap();
        assert!(matches!(bound, Bound::Listening(_)));
        let mode = std::fs::metadata(&home.run).unwrap().permissions().mode() & 0o777;
        assert_eq!(mode, 0o700);
    }

    #[test]
    fn worker_args_preserve_scan_order_and_flag_values() {
        assert_eq!(
            WorkerArgs::parse(&words("--idle-secs bad")),
            Err(WorkerArgsError::IdleSecs {
                value: "bad".to_owned(),
                source: "bad".parse::<u64>().unwrap_err(),
            })
        );
        assert_eq!(
            WorkerArgs::parse(&words("-x --backend onnx --agent-dir /a")),
            Ok(WorkerArgs {
                model: "-x".to_owned(),
                backend: Backend::Onnx,
                agent_dir: PathBuf::from("/a"),
                options: EngineOptions {
                    device: "cpu".to_owned(),
                    dtype: String::new(),
                    runtime_library: PathBuf::new(),
                },
                idle_secs: DEFAULT_IDLE_SECS,
            })
        );
        assert_eq!(
            WorkerArgs::parse(&words("m --backend onnx --agent-dir /a --device --dtype"))
                .unwrap()
                .options
                .device,
            "--dtype"
        );
        assert_eq!(
            WorkerArgs::parse(&words(
                "m --backend onnx --agent-dir /a --device first --device last --idle-secs 1 --idle-secs 2"
            )),
            Ok(WorkerArgs {
                model: "m".to_owned(),
                backend: Backend::Onnx,
                agent_dir: PathBuf::from("/a"),
                options: EngineOptions {
                    device: "last".to_owned(),
                    dtype: String::new(),
                    runtime_library: PathBuf::new(),
                },
                idle_secs: 2,
            })
        );
        assert_eq!(
            WorkerArgs::parse(&words("--unknown --idle-secs bad"))
                .unwrap_err()
                .to_string(),
            "unknown option --unknown"
        );
    }

    #[test]
    fn idle_window_invalid_value_falls_back_to_argument() {
        assert_eq!(
            idle_window(17, Err(std::env::VarError::NotPresent)).0,
            Duration::from_secs(17)
        );
        assert_eq!(
            idle_window(17, Ok("bad".to_owned())).0,
            Duration::from_secs(17)
        );
        assert_eq!(
            idle_window(17, Ok("23".to_owned())).0,
            Duration::from_millis(23)
        );
        let non_unicode = std::ffi::OsString::from_vec(vec![0xff]);
        assert_eq!(
            idle_window(17, Err(std::env::VarError::NotUnicode(non_unicode))).0,
            Duration::from_secs(17)
        );
    }

    #[test]
    fn activity_deadline_tracks_busy_requests_and_idle_since() {
        let now = Instant::now();
        let idle = Activity::Idle { since: now };
        assert_eq!(
            deadline(&idle, Duration::from_secs(2), now),
            now + Duration::from_secs(2)
        );
        let busy = idle.start();
        assert_eq!(
            deadline(&busy, Duration::from_secs(2), now),
            now + Duration::from_secs(2)
        );
        let twice = busy.start();
        let once = twice.finish(now + Duration::from_secs(1));
        assert!(!is_idle(
            &once,
            Duration::from_secs(2),
            now + Duration::from_secs(3)
        ));
        let finished = once.finish(now + Duration::from_secs(2));
        assert!(is_idle(
            &finished,
            Duration::from_secs(2),
            now + Duration::from_secs(4)
        ));
    }

    #[test]
    fn a_too_long_request_line_keeps_its_bad_request_text() {
        let error = parse_request(Err(RequestLineError::TooLong)).unwrap_err();
        assert_eq!(
            error.to_string(),
            format!("the request line is over {MAX_LINE_BYTES} bytes")
        );
    }

    #[tokio::test]
    async fn too_long_request_gets_a_bad_request_response() {
        let (events, _received) = tokio::sync::mpsc::unbounded_channel();
        let shared = Arc::new(Shared {
            tag: "tag".to_owned(),
            socket: PathBuf::new(),
            engine: Mutex::new(Box::new(Echo)),
            events,
            closing: watch::Sender::new(Serving::Open),
        });
        assert_eq!(
            answer(&shared, Err(RequestLineError::TooLong)).await,
            (
                Response::Err {
                    error: WorkerFailure::BadRequest {
                        message: format!("the request line is over {MAX_LINE_BYTES} bytes"),
                    },
                },
                After::Continue,
            )
        );
    }

    #[tokio::test]
    async fn run_worker_exit_codes_match_stage() {
        assert_eq!(run_worker(&[], unused_factory).await, ExitCode::from(2));
        assert_eq!(
            run_worker(
                &words("unknown --backend onnx --agent-dir /tmp"),
                unused_factory
            )
            .await,
            ExitCode::from(2)
        );
        assert_eq!(
            run_worker(
                &words("lfm2.5-230m --backend onnx --agent-dir /tmp"),
                unused_factory
            )
            .await,
            ExitCode::FAILURE
        );
    }

    fn unused_factory(
        _model: &'static CatalogModel,
        _path: PathBuf,
        _options: &EngineOptions,
    ) -> Result<Box<dyn Engine>, WorkerFailure> {
        Err(WorkerFailure::Unsupported {
            op: "test".to_owned(),
        })
    }
}
