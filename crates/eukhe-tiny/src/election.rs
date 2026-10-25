//! The election of a model's worker: a process that needs the model pings
//! the worker's socket; a worker with its launch tag is joined, a worker
//! with another tag is shut down and replaced, and with no live worker one
//! is started. The run of the election, and of a started worker's seat
//! (bend/tiny.bend section 4), is a stepper of the compiled Bend core
//! (`bend/ffi_tiny_run.bend`, laws `laws/tiny/run.bend`): it decides what
//! each outcome means and what to do next. This module only does it
//! (connect and ping, shut down, launch, take the bind lock), reports each
//! outcome to the run as it arrives, and keeps what an outcome left to act
//! on (the connection a ping opened, the error it met).

use std::future::Future;
use std::io;
use std::path::Path;

use eukhe_bend::wire::{Reader, WireError, Writer, STR_MAX};
use eukhe_bend::{expect_core, Entry, Error, Stepper};
use tokio::io::{AsyncWriteExt, BufReader};
use tokio::net::unix::{OwnedReadHalf, OwnedWriteHalf};
use tokio::net::UnixStream;

use crate::catalog::{installed, CatalogModel};
use crate::client::TinyError;
use crate::paths::{Backend, TinyHome};
use crate::protocol::{read_line, Line, Reply, Request, Response, MAX_LINE_BYTES};

/// The backend every worker runs on.
pub(crate) const BACKEND: Backend = Backend::Onnx;

/// What a need ended in (`Got` in bend/tiny.bend).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Got {
    /// No worker was live: this process started one.
    Started,
    /// A worker with this process's tag was live: the process joined it.
    Joined,
    /// A worker with another tag was live: this process shut it down and
    /// started one with its tag.
    Replaced,
}

/// How a started worker came up.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Launched {
    /// It bound the socket and serves.
    Ready,
    /// Another worker took the socket first; the started one exited.
    Adopted,
}

/// Starts the worker of one model (and [`BACKEND`]) for the election.
///
/// An implementation returns once the worker is reachable on
/// [`TinyHome::socket`] ([`Launched::Ready`]), or once the worker it
/// started found another live worker on the socket and left it in place
/// ([`Launched::Adopted`]). A worker that fails before either is a
/// [`TinyError::Spawn`]. It never waits for the worker to exit.
pub(crate) trait Launcher: Sync {
    fn launch(
        &self,
        home: &TinyHome,
        model: &'static CatalogModel,
    ) -> impl Future<Output = Result<Launched, TinyError>> + Send;
}

/// One client connection to a worker: [`Request`] lines out, one
/// [`Response`] line back for each.
pub(crate) struct Connection {
    reader: BufReader<OwnedReadHalf>,
    writer: OwnedWriteHalf,
}

impl Connection {
    /// Sends `request` and reads its response. EOF is
    /// [`io::ErrorKind::UnexpectedEof`]; a line that is not a [`Response`],
    /// or one over [`MAX_LINE_BYTES`], is [`io::ErrorKind::InvalidData`].
    #[tracing::instrument(level = "debug", skip_all)]
    pub(crate) async fn call(&mut self, request: &Request) -> io::Result<Response> {
        let mut line = serde_json::to_vec(request).map_err(io::Error::other)?;
        line.push(b'\n');
        self.writer.write_all(&line).await?;
        self.writer.flush().await?;
        match read_line(&mut self.reader, MAX_LINE_BYTES).await? {
            Line::Text(answer) => serde_json::from_str(&answer)
                .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error)),
            Line::TooLong => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("the response line is over {MAX_LINE_BYTES} bytes"),
            )),
            Line::End => Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "the worker closed the connection",
            )),
        }
    }
}

/// What a ping of a worker's socket met (`Probe` in `bend/tiny.bend`): the
/// fact the compiled core decides on, with what Rust keeps to act on it.
pub(crate) enum Met {
    /// No socket, or a refused one.
    Missing,
    /// The connect failed otherwise.
    Unreachable(io::Error),
    /// A worker answered the ping with its launch tag.
    Pong { connection: Connection, tag: String },
    /// A worker answered the ping with another response.
    Odd(Response),
    /// The answer was no line of the protocol.
    Garbled(io::Error),
    /// The connection closed or failed on the ping.
    Hung,
}

impl Met {
    /// The probe on the wire (`Probe` of `bend/ffi_tiny_run.bend`): a launch
    /// tag longer than the wire carries is no line of the protocol.
    fn spell(&self, writer: &mut Writer) {
        match self {
            Met::Missing => writer.tag(0),
            Met::Unreachable(_) => writer.tag(1),
            Met::Pong { tag, .. } if tag.chars().count() <= STR_MAX => writer.tag(2).str(tag),
            Met::Garbled(_) | Met::Pong { .. } => writer.tag(4),
            Met::Odd(_) => writer.tag(3),
            Met::Hung => writer.tag(5),
        };
    }

    /// The IO error of a probe the run calls failed.
    fn into_error(self) -> io::Error {
        match self {
            Met::Unreachable(error) | Met::Garbled(error) => error,
            Met::Odd(other) => io::Error::new(
                io::ErrorKind::InvalidData,
                format!("the worker answered a ping with {other:?}"),
            ),
            Met::Pong { tag, .. } if tag.chars().count() > STR_MAX => io::Error::new(
                io::ErrorKind::InvalidData,
                "the worker's launch tag is longer than the core reads",
            ),
            Met::Missing | Met::Pong { .. } | Met::Hung => inconsistent("a failed probe"),
        }
    }
}

/// Connects to `socket` and pings it; what it met.
#[tracing::instrument(level = "debug")]
pub(crate) async fn probe(socket: &Path) -> Met {
    let stream = match UnixStream::connect(socket).await {
        Ok(stream) => stream,
        Err(error) => {
            return match error.kind() {
                io::ErrorKind::NotFound | io::ErrorKind::ConnectionRefused => Met::Missing,
                _ => Met::Unreachable(error),
            };
        }
    };
    let (read, writer) = stream.into_split();
    let mut connection = Connection {
        reader: BufReader::new(read),
        writer,
    };
    match connection.call(&Request::Ping).await {
        Ok(Response::Ok {
            reply: Reply::Pong { tag },
        }) => Met::Pong { connection, tag },
        Ok(other) => Met::Odd(other),
        Err(error) if error.kind() == io::ErrorKind::InvalidData => Met::Garbled(error),
        Err(_) => Met::Hung,
    }
}

/// A reply of the compiled core that its laws rule out: only an
/// inconsistent build answers it.
fn inconsistent<T>(expected: &'static str) -> T {
    expect_core(
        Entry::TinyRun,
        Err::<T, Error>(Error::Wire(WireError::Malformed { at: 0, expected })),
    )
}

/// Why a run failed (`Why` in bend/tiny.bend).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Why {
    Io,
    Protocol,
    Mistagged,
    Vacant,
    Spawn,
}

/// What the run tells Rust to do next (`Do` in bend/tiny.bend).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Do {
    Ping,
    Shutdown,
    Launch,
    Use(Got),
    Fail(Why),
    Lock,
    Adopt,
    Take,
    Fault,
    Nothing,
}

/// An outcome Rust reports to the run (`Seen` in bend/tiny.bend).
enum Seen<'a> {
    Pinged(&'a Met),
    Heard(&'a io::Result<Response>),
    Came(Launched),
    NoSpawn,
    Locked,
}

fn read_do(reply: &str) -> Result<Do, WireError> {
    let mut reader = Reader::reply(reply)?;
    let next = match reader.tag_of(10, "what to do next")? {
        0 => Do::Ping,
        1 => Do::Shutdown,
        2 => Do::Launch,
        3 => Do::Use(match reader.tag_of(3, "what a need got")? {
            0 => Got::Started,
            1 => Got::Joined,
            2.. => Got::Replaced,
        }),
        4 => Do::Fail(match reader.tag_of(5, "why a need failed")? {
            0 => Why::Io,
            1 => Why::Protocol,
            2 => Why::Mistagged,
            3 => Why::Vacant,
            4.. => Why::Spawn,
        }),
        5 => Do::Lock,
        6 => Do::Adopt,
        7 => Do::Take,
        8 => Do::Fault,
        9.. => Do::Nothing,
    };
    reader.end()?;
    Ok(next)
}

/// One run in the compiled core: a process's election, or a started
/// worker's seat.
struct Run {
    core: Stepper,
}

impl Run {
    fn open(request: Result<String, WireError>) -> (Run, Do) {
        let opened = || -> Result<(Run, Do), Error> {
            let (core, reply) = Stepper::open(Entry::TinyRun, &request?)?;
            Ok((Run { core }, read_do(&reply)?))
        };
        expect_core(Entry::TinyRun, opened())
    }

    /// The election of a process with launch tag `tag`, and its first step.
    fn need(tag: &str) -> (Run, Do) {
        let mut writer = Writer::new();
        writer.tag(0).str(tag);
        Run::open(writer.finish())
    }

    /// A started worker's seat, and its first step.
    fn seat() -> (Run, Do) {
        let mut writer = Writer::new();
        writer.tag(1);
        Run::open(writer.finish())
    }

    /// Reports `seen`; what to do next.
    fn step(&mut self, seen: &Seen<'_>) -> Do {
        let mut writer = Writer::new();
        match seen {
            Seen::Pinged(met) => {
                writer.tag(0);
                met.spell(&mut writer);
            }
            Seen::Heard(heard) => {
                writer.tag(1).tag(match heard {
                    Ok(Response::Ok { reply: Reply::Bye }) => 0,
                    Ok(_) => 1,
                    Err(error) if error.kind() == io::ErrorKind::UnexpectedEof => 2,
                    Err(_) => 3,
                });
            }
            Seen::Came(launched) => {
                writer.tag(2).tag(match launched {
                    Launched::Ready => 0,
                    Launched::Adopted => 1,
                });
            }
            Seen::NoSpawn => {
                writer.tag(3);
            }
            Seen::Locked => {
                writer.tag(4);
            }
        }
        let mut stepped = || -> Result<Do, Error> {
            let reply = self.core.step(&writer.finish()?)?;
            Ok(read_do(&reply)?)
        };
        expect_core(Entry::TinyRun, stepped())
    }
}

/// A connection to the worker of `model` with launch tag `tag`, and how
/// the election got it: join a live worker with `tag`, else shut down a
/// live worker of another tag, else start one with `launcher`.
///
/// # Errors
///
/// The launcher's [`TinyError::Spawn`]; [`TinyError::Spawn`] too when the
/// started worker is not reachable with `tag`; [`TinyError::Io`] and
/// [`TinyError::Protocol`] for a socket that fails or answers out of
/// protocol.
#[tracing::instrument(level = "debug", skip(home, model, launcher), fields(model = model.id))]
pub(crate) async fn ensure(
    home: &TinyHome,
    model: &'static CatalogModel,
    tag: &str,
    launcher: &impl Launcher,
) -> Result<(Connection, Got), TinyError> {
    let socket = home.socket(model.id, BACKEND);
    let (mut run, mut next) = Run::need(tag);
    // What the outcomes left to act on: the last ping's (a shutdown takes
    // its connection), the shutdown's answer, the launch's failure.
    let mut met = None;
    let mut heard = None;
    let mut spawn_failure = None;
    loop {
        next = match next {
            Do::Ping => {
                let pinged = probe(&socket).await;
                let next = run.step(&Seen::Pinged(&pinged));
                met = Some(pinged);
                next
            }
            Do::Shutdown => {
                let Some(Met::Pong { mut connection, .. }) = met.take() else {
                    return inconsistent("a shutdown after a pong");
                };
                let answer = connection.call(&Request::Shutdown).await;
                let next = run.step(&Seen::Heard(&answer));
                heard = Some(answer);
                next
            }
            Do::Launch => match launcher.launch(home, model).await {
                Ok(came) => run.step(&Seen::Came(came)),
                Err(error) => {
                    spawn_failure = Some(error);
                    run.step(&Seen::NoSpawn)
                }
            },
            Do::Use(got) => {
                return match met {
                    Some(Met::Pong { connection, .. }) => Ok((connection, got)),
                    _ => inconsistent("a use after a pong"),
                };
            }
            Do::Fail(why) => return Err(failure(home, model, tag, why, met, heard, spawn_failure)),
            Do::Lock | Do::Adopt | Do::Take | Do::Fault | Do::Nothing => {
                return inconsistent("a need's next step");
            }
        };
    }
}

/// The error of a need whose run failed for `why`, from what its outcomes
/// left: the last ping, else the shutdown's answer; the launch's failure.
fn failure(
    home: &TinyHome,
    model: &'static CatalogModel,
    tag: &str,
    why: Why,
    met: Option<Met>,
    heard: Option<io::Result<Response>>,
    spawn_failure: Option<TinyError>,
) -> TinyError {
    let socket = home.socket(model.id, BACKEND);
    let spawn = |message: String| TinyError::Spawn {
        model: model.id,
        message,
        log: home.log(model.id, BACKEND),
    };
    match (why, met, heard) {
        (Why::Io, Some(met), _) => TinyError::io(model, &met.into_error()),
        (Why::Io, None, Some(Err(error))) => TinyError::io(model, &error),
        (Why::Protocol, _, Some(Ok(other))) => TinyError::Protocol {
            model: model.id,
            message: format!("the worker answered a shutdown with {other:?}"),
        },
        (Why::Mistagged, Some(Met::Pong { tag: theirs, .. }), _) => spawn(format!(
            "the worker on {} answers with tag {theirs}, not {tag}",
            socket.display()
        )),
        (Why::Vacant, Some(Met::Missing | Met::Hung), _) => spawn(format!(
            "no worker listens on {} after the start",
            socket.display()
        )),
        (Why::Spawn, _, _) => match spawn_failure {
            Some(error) => error,
            None => inconsistent("a failed launch"),
        },
        (Why::Io | Why::Protocol | Why::Mistagged | Why::Vacant, _, _) => {
            inconsistent("a failure its outcomes allow")
        }
    }
}

/// What a started worker does with the socket, as its seat run decides:
/// take the bind lock (`lock` takes it and answers it held), ping the
/// socket under it, then leave a live worker in place, take the socket,
/// or fail.
pub(crate) enum Seated<L> {
    /// A live worker answers: leave it in place.
    Adopt,
    /// No live worker: remove a stale socket and bind it, still holding
    /// the lock.
    Take(L),
}

/// The seat of a started worker on `socket`: its run decides; `lock`
/// takes the bind lock.
///
/// # Errors
///
/// The lock or the probe fails.
pub(crate) async fn seat<L, F>(socket: &Path, lock: impl FnOnce() -> F) -> io::Result<Seated<L>>
where
    F: Future<Output = io::Result<L>>,
{
    let (mut run, mut next) = Run::seat();
    let mut lock = Some(lock);
    let mut held = None;
    let mut met = None;
    loop {
        next = match next {
            Do::Lock => {
                let Some(take) = lock.take() else {
                    return inconsistent("one lock per seat");
                };
                held = Some(take().await?);
                run.step(&Seen::Locked)
            }
            Do::Ping => {
                let pinged = probe(socket).await;
                let next = run.step(&Seen::Pinged(&pinged));
                met = Some(pinged);
                next
            }
            Do::Adopt => return Ok(Seated::Adopt),
            Do::Take => {
                return match held {
                    Some(held) => Ok(Seated::Take(held)),
                    None => inconsistent("a take under the lock"),
                };
            }
            Do::Fault => {
                return match met {
                    Some(met) => Err(met.into_error()),
                    None => inconsistent("a fault after a ping"),
                };
            }
            Do::Shutdown | Do::Launch | Do::Use(_) | Do::Fail(_) | Do::Nothing => {
                return inconsistent("a seat's next step");
            }
        };
    }
}

/// Serves `request` on the worker of `model` with launch tag `tag`,
/// electing the worker first ([`ensure`]); returns the reply and how the
/// election went.
///
/// # Errors
///
/// [`TinyError::NotInstalled`] before any connection when a file of
/// `model` is missing; the errors of [`ensure`]; the worker's
/// [`TinyError::Worker`] failure; [`TinyError::Crashed`] when the worker
/// closes or fails mid-request; [`TinyError::Protocol`] for an answer out
/// of protocol.
#[tracing::instrument(level = "debug", skip(home, model, launcher, request), fields(model = model.id))]
pub(crate) async fn request(
    home: &TinyHome,
    model: &'static CatalogModel,
    tag: &str,
    launcher: &impl Launcher,
    request: &Request,
) -> Result<(Reply, Got), TinyError> {
    if !installed(home, model) {
        return Err(TinyError::NotInstalled { model: model.id });
    }
    let (mut connection, got) = ensure(home, model, tag, launcher).await?;
    match connection.call(request).await {
        Ok(Response::Ok { reply }) => Ok((reply, got)),
        Ok(Response::Err { error }) => Err(TinyError::Worker(error)),
        Err(error) if error.kind() == io::ErrorKind::InvalidData => Err(TinyError::Protocol {
            model: model.id,
            message: error.to_string(),
        }),
        Err(_) => Err(TinyError::Crashed {
            model: model.id,
            log: home.log(model.id, BACKEND),
        }),
    }
}
