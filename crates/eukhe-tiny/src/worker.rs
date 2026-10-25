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

/// The idle window: `idle_secs`, unless `EUKHE_TINY_WORKER_IDLE_MS` is set.
pub(crate) fn idle_window(idle_secs: u64) -> Duration {
    match std::env::var(IDLE_MS_ENV) {
        Ok(value) => match value.parse() {
            Ok(millis) => Duration::from_millis(millis),
            Err(error) => {
                tracing::warn!("ignoring {IDLE_MS_ENV}={value:?}: {error}");
                Duration::from_secs(idle_secs)
            }
        },
        Err(std::env::VarError::NotPresent) => Duration::from_secs(idle_secs),
        Err(error @ std::env::VarError::NotUnicode(_)) => {
            tracing::warn!("ignoring {IDLE_MS_ENV}: {error}");
            Duration::from_secs(idle_secs)
        }
    }
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

impl WorkerArgs {
    fn parse(args: &[String]) -> Result<WorkerArgs, String> {
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
                    .ok_or_else(|| format!("{word} needs a value"))
            };
            match word.as_str() {
                "--backend" => {
                    let id = value()?;
                    backend =
                        Some(Backend::parse(&id).ok_or_else(|| format!("unknown backend {id:?}"))?);
                }
                "--agent-dir" => agent_dir = Some(PathBuf::from(value()?)),
                "--device" => options.device = value()?,
                "--dtype" => options.dtype = value()?,
                "--runtime-library" => options.runtime_library = PathBuf::from(value()?),
                "--idle-secs" => {
                    let secs = value()?;
                    idle_secs = secs
                        .parse()
                        .map_err(|error| format!("--idle-secs {secs:?}: {error}"))?;
                }
                flag if flag.starts_with("--") => return Err(format!("unknown option {flag}")),
                id => match model {
                    None => model = Some(id.to_owned()),
                    Some(_) => return Err(format!("unexpected argument {id:?}")),
                },
            }
        }
        Ok(WorkerArgs {
            model: model.ok_or("missing <model>")?,
            backend: backend.ok_or("missing --backend")?,
            agent_dir: agent_dir.ok_or("missing --agent-dir")?,
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
        Err(message) => {
            eprintln!("tiny-worker: {message}\n{USAGE}");
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
    match serve(listening, tag, engine, idle_window(args.idle_secs)).await {
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

/// When the worker last finished a request, and how many are in flight.
struct Activity {
    last: Instant,
    busy: u32,
}

/// What every connection of one worker shares.
struct Shared {
    tag: String,
    socket: PathBuf,
    engine: Mutex<Box<dyn Engine>>,
    activity: Mutex<Activity>,
    /// Set by a [`Request::Shutdown`]: the worker takes no new connection
    /// or request, and exits once the requests in flight are answered.
    closing: watch::Sender<bool>,
}

impl Shared {
    fn activity(&self) -> std::sync::MutexGuard<'_, Activity> {
        self.activity.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Runs `infer` on the engine on the blocking pool, one at a time.
    async fn infer(
        self: &Arc<Shared>,
        infer: impl FnOnce(&mut dyn Engine) -> Result<Reply, WorkerFailure> + Send + 'static,
    ) -> Response {
        let shared = Arc::clone(self);
        let ran = tokio::task::spawn_blocking(move || {
            let mut engine = shared.engine.lock().unwrap_or_else(PoisonError::into_inner);
            infer(engine.as_mut())
        })
        .await;
        match ran {
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

/// Serves `listening` with `engine`, answering ping with `tag`, until a
/// [`Request::Shutdown`] or `idle` without a request. On a shutdown the
/// socket is unlinked at once (a new worker may bind it), no connection or
/// request is taken any more, and the requests in flight (of other
/// clients) get their answers before it returns. The idle exit unlinks the
/// socket before it returns.
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
    let shared = Arc::new(Shared {
        tag,
        socket,
        engine: Mutex::new(engine),
        activity: Mutex::new(Activity {
            last: Instant::now(),
            busy: 0,
        }),
        closing: watch::Sender::new(false),
    });
    let mut closing = shared.closing.subscribe();
    let mut connections = JoinSet::new();
    loop {
        let deadline = {
            let activity = shared.activity();
            if activity.busy == 0 {
                activity.last + idle
            } else {
                Instant::now() + idle
            }
        };
        tokio::select! {
            accepted = listener.accept() => match accepted {
                Ok((stream, _)) => {
                    connections.spawn(connection(Arc::clone(&shared), stream));
                }
                Err(error) => {
                    remove_socket(&shared.socket)?;
                    return Err(error);
                }
            },
            _ = closing.wait_for(|closing| *closing) => break,
            () = tokio::time::sleep_until(deadline) => {
                let idle_now = {
                    let activity = shared.activity();
                    activity.busy == 0 && activity.last + idle <= Instant::now()
                };
                if idle_now {
                    remove_socket(&shared.socket)?;
                    return Ok(Exit::Idle);
                }
            },
            Some(_) = connections.join_next() => {}
        }
    }
    // The shutdown unlinked the socket; a new worker may hold that path by
    // now, so it is not unlinked again. Each connection ends once its
    // request in flight is answered.
    drop(listener);
    while connections.join_next().await.is_some() {}
    Ok(Exit::Shutdown)
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
            _ = closing.wait_for(|closing| *closing) => return,
            line = read_line(&mut reader, MAX_LINE_BYTES) => match line {
                Ok(Line::Text(line)) => Some(line),
                Ok(Line::TooLong) => None,
                Ok(Line::End) => return,
                Err(error) => {
                    tracing::debug!("client connection failed: {error}");
                    return;
                }
            },
        };
        shared.activity().busy += 1;
        let mut shutdown = false;
        let parsed = match &line {
            Some(line) => serde_json::from_str::<Request>(line).map_err(|error| error.to_string()),
            None => Err(format!("the request line is over {MAX_LINE_BYTES} bytes")),
        };
        let response = match parsed {
            Err(message) => Response::Err {
                error: WorkerFailure::BadRequest { message },
            },
            Ok(Request::Ping) => Response::Ok {
                reply: Reply::Pong {
                    tag: shared.tag.clone(),
                },
            },
            Ok(Request::Shutdown) => {
                shutdown = true;
                if let Err(error) = remove_socket(&shared.socket) {
                    tracing::warn!("cannot unlink {}: {error}", shared.socket.display());
                }
                Response::Ok { reply: Reply::Bye }
            }
            Ok(Request::Load) => {
                shared
                    .infer(|engine| engine.load().map(|()| Reply::Loaded))
                    .await
            }
            Ok(Request::Chat(request)) => {
                shared
                    .infer(move |engine| engine.chat(&request).map(Reply::Chat))
                    .await
            }
            Ok(Request::Transcribe(request)) => {
                shared
                    .infer(move |engine| engine.transcribe(&request).map(Reply::Transcript))
                    .await
            }
            Ok(Request::Speak(request)) => {
                shared
                    .infer(move |engine| engine.speak(&request).map(Reply::Speech))
                    .await
            }
        };
        let written = async {
            let mut line = serde_json::to_vec(&response).map_err(io::Error::other)?;
            line.push(b'\n');
            write.write_all(&line).await?;
            write.flush().await
        }
        .await;
        {
            let mut activity = shared.activity();
            activity.busy -= 1;
            activity.last = Instant::now();
        }
        if shutdown {
            shared.closing.send_replace(true);
            return;
        }
        if let Err(error) = written {
            tracing::debug!("cannot answer the client: {error}");
            return;
        }
    }
}

#[cfg(test)]
mod tests {
    use std::os::unix::fs::PermissionsExt;
    use std::sync::mpsc;

    use super::*;
    use crate::election::{probe, Met};
    use crate::protocol::{
        Audio, ChatMessage, ChatReply, ChatRequest, ChatRole, SpeakRequest, StopReason,
        TranscribeRequest, Transcript,
    };
    use crate::testing::ECHO;

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
            WorkerArgs::parse(&words("kokoro --agent-dir /a")),
            Err("missing --backend".to_owned())
        );
        assert_eq!(
            WorkerArgs::parse(&words("kokoro --backend onnx")),
            Err("missing --agent-dir".to_owned())
        );
        assert_eq!(
            WorkerArgs::parse(&words("kokoro --backend llama")),
            Err("unknown backend \"llama\"".to_owned())
        );
        assert_eq!(
            WorkerArgs::parse(&words("kokoro --backend onnx --idle-secs")),
            Err("--idle-secs needs a value".to_owned())
        );
        assert_eq!(
            WorkerArgs::parse(&words("kokoro whisper-base --backend onnx")),
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
}
