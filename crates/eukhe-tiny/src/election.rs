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

/// Why a call to a worker got no response: the socket failed, the worker
/// closed it, or its answer was no line of the protocol.
#[derive(Debug)]
pub(crate) enum CallError {
    Io(io::Error),
    Closed,
    TooLong,
    Garbled(serde_json::Error),
    NotUtf8(io::Error),
}

impl std::fmt::Display for CallError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CallError::Io(error) | CallError::NotUtf8(error) => {
                std::fmt::Display::fmt(error, formatter)
            }
            CallError::Closed => formatter.write_str("the worker closed the connection"),
            CallError::TooLong => write!(
                formatter,
                "the response line is over {MAX_LINE_BYTES} bytes"
            ),
            CallError::Garbled(error) => std::fmt::Display::fmt(error, formatter),
        }
    }
}

impl std::error::Error for CallError {}

impl CallError {
    /// The IO error the run's callers report (same text and kind as the
    /// call answered before it had its own error type).
    fn into_io(self) -> io::Error {
        match self {
            CallError::Io(error) => error,
            CallError::Closed => io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "the worker closed the connection",
            ),
            CallError::TooLong => io::Error::new(
                io::ErrorKind::InvalidData,
                format!("the response line is over {MAX_LINE_BYTES} bytes"),
            ),
            CallError::Garbled(error) => io::Error::new(io::ErrorKind::InvalidData, error),
            CallError::NotUtf8(error) => io::Error::new(io::ErrorKind::InvalidData, error),
        }
    }
}

impl Connection {
    /// Sends `request` and reads its response. EOF is
    /// [`CallError::Closed`]; a line that is not a [`Response`], over
    /// [`MAX_LINE_BYTES`] or not UTF-8 is `Garbled`, `TooLong` or `NotUtf8`.
    #[tracing::instrument(level = "debug", skip_all)]
    pub(crate) async fn call(&mut self, request: &Request) -> Result<Response, CallError> {
        let mut line = Vec::with_capacity(256);
        serde_json::to_writer(&mut line, request)
            .map_err(|error| CallError::Io(io::Error::other(error)))?;
        line.push(b'\n');
        self.writer.write_all(&line).await.map_err(CallError::Io)?;
        self.writer.flush().await.map_err(CallError::Io)?;
        match read_line(&mut self.reader, MAX_LINE_BYTES).await {
            Ok(Line::Text(answer)) => serde_json::from_str(&answer).map_err(CallError::Garbled),
            Ok(Line::TooLong) => Err(CallError::TooLong),
            Ok(Line::End) => Err(CallError::Closed),
            Err(error) if error.kind() == io::ErrorKind::InvalidData => {
                Err(CallError::NotUtf8(error))
            }
            Err(error) => Err(CallError::Io(error)),
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
    Garbled(CallError),
    /// The connection closed or failed on the ping.
    Hung,
}

/// A pong's launch tag against what the run's wire carries.
enum ProbeTag<'a> {
    Fits(&'a str),
    TooLong,
}

/// Whether `tag` fits the run's string (in chars, as the core counts).
fn probe_tag(tag: &str) -> ProbeTag<'_> {
    if tag.chars().count() <= STR_MAX {
        ProbeTag::Fits(tag)
    } else {
        ProbeTag::TooLong
    }
}

impl Met {
    /// The probe on the wire (`Probe` of `bend/ffi_tiny_run.bend`): a launch
    /// tag longer than the wire carries is no line of the protocol.
    fn probe_wire(&self) -> ProbeWire<'_> {
        match self {
            Met::Missing => ProbeWire { tag: 0, text: None },
            Met::Unreachable(_) => ProbeWire { tag: 1, text: None },
            Met::Pong { tag, .. } => match probe_tag(tag) {
                ProbeTag::Fits(tag) => ProbeWire {
                    tag: 2,
                    text: Some(tag),
                },
                ProbeTag::TooLong => ProbeWire { tag: 4, text: None },
            },
            Met::Garbled(_) => ProbeWire { tag: 4, text: None },
            Met::Odd(_) => ProbeWire { tag: 3, text: None },
            Met::Hung => ProbeWire { tag: 5, text: None },
        }
    }

    /// The IO error of a probe the run calls failed.
    fn into_error(self) -> io::Error {
        let fault = match self {
            Met::Unreachable(error) => ProbeFault::Connect(error),
            Met::Garbled(error) => ProbeFault::Garbled(error),
            Met::Odd(other) => ProbeFault::Odd(other),
            Met::Pong { tag, .. } => match probe_tag(&tag) {
                ProbeTag::Fits(_) => inconsistent("a failed probe"),
                ProbeTag::TooLong => ProbeFault::TagTooLong,
            },
            Met::Missing | Met::Hung => inconsistent("a failed probe"),
        };
        fault.into_io()
    }
}

/// Why a probe the run calls failed.
#[derive(Debug)]
enum ProbeFault {
    Connect(io::Error),
    Garbled(CallError),
    Odd(Response),
    TagTooLong,
}

impl std::fmt::Display for ProbeFault {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProbeFault::Connect(error) => std::fmt::Display::fmt(error, formatter),
            ProbeFault::Garbled(error) => std::fmt::Display::fmt(error, formatter),
            ProbeFault::Odd(other) => {
                write!(formatter, "the worker answered a ping with {other:?}")
            }
            ProbeFault::TagTooLong => {
                formatter.write_str("the worker's launch tag is longer than the core reads")
            }
        }
    }
}

impl std::error::Error for ProbeFault {}

impl ProbeFault {
    /// The IO error with the text and kind the probe reported before.
    fn into_io(self) -> io::Error {
        match self {
            ProbeFault::Connect(error) => error,
            ProbeFault::Garbled(error) => error.into_io(),
            ProbeFault::Odd(other) => io::Error::new(
                io::ErrorKind::InvalidData,
                format!("the worker answered a ping with {other:?}"),
            ),
            ProbeFault::TagTooLong => io::Error::new(
                io::ErrorKind::InvalidData,
                "the worker's launch tag is longer than the core reads",
            ),
        }
    }
}

/// A probe as the run reads it: its tag, and the pong's launch tag.
struct ProbeWire<'a> {
    tag: u32,
    text: Option<&'a str>,
}

/// What a failed connect met: no worker, or an unreachable socket.
fn connect_failure(error: io::Error) -> Met {
    match error.kind() {
        io::ErrorKind::NotFound | io::ErrorKind::ConnectionRefused => Met::Missing,
        _ => Met::Unreachable(error),
    }
}

/// What a ping's answer met.
fn after_ping(connection: Connection, answer: Result<Response, CallError>) -> Met {
    match answer {
        Ok(Response::Ok {
            reply: Reply::Pong { tag },
        }) => Met::Pong { connection, tag },
        Ok(other) => Met::Odd(other),
        Err(error @ (CallError::Garbled(_) | CallError::TooLong | CallError::NotUtf8(_))) => {
            Met::Garbled(error)
        }
        Err(CallError::Io(error)) if error.kind() == io::ErrorKind::InvalidData => {
            Met::Garbled(CallError::Io(error))
        }
        Err(CallError::Io(_) | CallError::Closed) => Met::Hung,
    }
}

/// Connects to `socket` and pings it; what it met.
#[tracing::instrument(level = "debug")]
pub(crate) async fn probe(socket: &Path) -> Met {
    let stream = match UnixStream::connect(socket).await {
        Ok(stream) => stream,
        Err(error) => return connect_failure(error),
    };
    let (read, writer) = stream.into_split();
    let mut connection = Connection {
        reader: BufReader::new(read),
        writer,
    };
    let answer = connection.call(&Request::Ping).await;
    after_ping(connection, answer)
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
    Heard(&'a Result<Response, CallError>),
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

/// A shutdown's answer as the run reads it (`ShutHeard`): 0 bye, 1 any
/// other response, 2 the worker closed, 3 a failure or garbled line.
fn heard_tag(heard: &Result<Response, CallError>) -> u32 {
    match heard {
        Ok(Response::Ok { reply: Reply::Bye }) => 0,
        Ok(
            Response::Ok {
                reply:
                    Reply::Pong { .. }
                    | Reply::Loaded
                    | Reply::Chat(_)
                    | Reply::Transcript(_)
                    | Reply::Speech(_),
            }
            | Response::Err { .. },
        ) => 1,
        Err(CallError::Closed) => 2,
        Err(CallError::Io(error)) if error.kind() == io::ErrorKind::UnexpectedEof => 2,
        Err(
            CallError::Io(_) | CallError::TooLong | CallError::Garbled(_) | CallError::NotUtf8(_),
        ) => 3,
    }
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
                let probe = met.probe_wire();
                writer.tag(0).tag(probe.tag);
                if let Some(text) = probe.text {
                    writer.str(text);
                }
            }
            Seen::Heard(heard) => {
                writer.tag(1).tag(heard_tag(heard));
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

/// The last outcome of an election: each `Fail` and `Use` of the run
/// (`bend/tiny.bend`) follows the outcome that decided it, so the last one
/// is the one to act on.
enum Left {
    Nothing,
    Pinged(Met),
    Heard(io::Result<Response>),
    NoSpawn(TinyError),
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
    let mut left = Left::Nothing;
    loop {
        next = match next {
            Do::Ping => {
                let pinged = probe(&socket).await;
                let next = run.step(&Seen::Pinged(&pinged));
                left = Left::Pinged(pinged);
                next
            }
            Do::Shutdown => {
                let Left::Pinged(Met::Pong { mut connection, .. }) = left else {
                    return inconsistent("a shutdown after a pong");
                };
                let answer = connection.call(&Request::Shutdown).await;
                let next = run.step(&Seen::Heard(&answer));
                left = Left::Heard(answer.map_err(CallError::into_io));
                next
            }
            Do::Launch => match launcher.launch(home, model).await {
                Ok(came) => run.step(&Seen::Came(came)),
                Err(error) => {
                    left = Left::NoSpawn(error);
                    run.step(&Seen::NoSpawn)
                }
            },
            Do::Use(got) => {
                return match left {
                    Left::Pinged(Met::Pong { connection, .. }) => Ok((connection, got)),
                    Left::Nothing
                    | Left::Pinged(
                        Met::Missing
                        | Met::Unreachable(_)
                        | Met::Odd(_)
                        | Met::Garbled(_)
                        | Met::Hung,
                    )
                    | Left::Heard(_)
                    | Left::NoSpawn(_) => inconsistent("a use after a pong"),
                };
            }
            Do::Fail(why) => return Err(failure(home, model, tag, why, left)),
            Do::Lock | Do::Adopt | Do::Take | Do::Fault | Do::Nothing => {
                return inconsistent("a need's next step");
            }
        };
    }
}

/// The error of a need whose run failed for `why`, from its last outcome.
fn failure(
    home: &TinyHome,
    model: &'static CatalogModel,
    tag: &str,
    why: Why,
    left: Left,
) -> TinyError {
    let socket = home.socket(model.id, BACKEND);
    let spawn = |message: String| TinyError::Spawn {
        model: model.id,
        message,
        log: home.log(model.id, BACKEND),
    };
    match (why, left) {
        (Why::Io, Left::Pinged(met)) => TinyError::io(model, &met.into_error()),
        (Why::Io, Left::Heard(Err(error))) => TinyError::io(model, &error),
        (Why::Protocol, Left::Heard(Ok(other))) => TinyError::Protocol {
            model: model.id,
            message: format!("the worker answered a shutdown with {other:?}"),
        },
        (Why::Mistagged, Left::Pinged(Met::Pong { tag: theirs, .. })) => spawn(format!(
            "the worker on {} answers with tag {theirs}, not {tag}",
            socket.display()
        )),
        (Why::Vacant, Left::Pinged(Met::Missing | Met::Hung)) => spawn(format!(
            "no worker listens on {} after the start",
            socket.display()
        )),
        (Why::Spawn, Left::NoSpawn(error)) => error,
        (
            Why::Io,
            Left::Nothing
            | Left::NoSpawn(_)
            | Left::Heard(Ok(
                Response::Ok {
                    reply:
                        Reply::Pong { .. }
                        | Reply::Loaded
                        | Reply::Chat(_)
                        | Reply::Transcript(_)
                        | Reply::Speech(_)
                        | Reply::Bye,
                }
                | Response::Err { .. },
            )),
        )
        | (
            Why::Protocol,
            Left::Nothing
            | Left::Heard(Err(_))
            | Left::NoSpawn(_)
            | Left::Pinged(
                Met::Missing
                | Met::Unreachable(_)
                | Met::Pong { .. }
                | Met::Odd(_)
                | Met::Garbled(_)
                | Met::Hung,
            ),
        )
        | (Why::Mistagged | Why::Vacant, Left::Nothing | Left::Heard(_) | Left::NoSpawn(_))
        | (
            Why::Spawn,
            Left::Nothing
            | Left::Heard(_)
            | Left::Pinged(
                Met::Missing
                | Met::Unreachable(_)
                | Met::Pong { .. }
                | Met::Odd(_)
                | Met::Garbled(_)
                | Met::Hung,
            ),
        )
        | (
            Why::Mistagged,
            Left::Pinged(
                Met::Missing | Met::Unreachable(_) | Met::Odd(_) | Met::Garbled(_) | Met::Hung,
            ),
        )
        | (
            Why::Vacant,
            Left::Pinged(Met::Unreachable(_) | Met::Pong { .. } | Met::Odd(_) | Met::Garbled(_)),
        ) => inconsistent("a failure its outcomes allow"),
    }
}

/// A seat run's state: the lock not yet taken, held, held after the ping.
enum SeatState<F, L> {
    Unlocked(F),
    Held(L),
    HeldPinged(L, Met),
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
    let mut state = SeatState::Unlocked(lock);
    loop {
        next = match next {
            Do::Lock => {
                state = match state {
                    SeatState::Unlocked(take) => SeatState::Held(take().await?),
                    SeatState::Held(_) | SeatState::HeldPinged(_, _) => {
                        return inconsistent("one lock per seat")
                    }
                };
                run.step(&Seen::Locked)
            }
            Do::Ping => {
                let held = match state {
                    SeatState::Held(held) => held,
                    SeatState::Unlocked(_) | SeatState::HeldPinged(_, _) => {
                        return inconsistent("a ping under the lock")
                    }
                };
                let pinged = probe(socket).await;
                let next = run.step(&Seen::Pinged(&pinged));
                state = SeatState::HeldPinged(held, pinged);
                next
            }
            Do::Adopt => return Ok(Seated::Adopt),
            Do::Take => {
                return match state {
                    SeatState::Held(held) | SeatState::HeldPinged(held, _) => {
                        Ok(Seated::Take(held))
                    }
                    SeatState::Unlocked(_) => inconsistent("a take under the lock"),
                }
            }
            Do::Fault => {
                return match state {
                    SeatState::HeldPinged(_, met) => Err(met.into_error()),
                    SeatState::Unlocked(_) | SeatState::Held(_) => {
                        inconsistent("a fault after a ping")
                    }
                }
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
        Err(error @ (CallError::TooLong | CallError::Garbled(_) | CallError::NotUtf8(_))) => {
            Err(TinyError::Protocol {
                model: model.id,
                message: error.to_string(),
            })
        }
        Err(CallError::Io(error)) if error.kind() == io::ErrorKind::InvalidData => {
            Err(TinyError::Protocol {
                model: model.id,
                message: error.to_string(),
            })
        }
        Err(CallError::Io(_) | CallError::Closed) => Err(TinyError::Crashed {
            model: model.id,
            log: home.log(model.id, BACKEND),
        }),
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::testing::ECHO;

    fn connection() -> Connection {
        let (stream, _peer) = UnixStream::pair().unwrap();
        let (read, writer) = stream.into_split();
        Connection {
            reader: BufReader::new(read),
            writer,
        }
    }

    #[tokio::test]
    async fn pong_tag_length_uses_unicode_characters() {
        let exact = "é".repeat(STR_MAX);
        let long = format!("{exact}é");
        let exact_met = Met::Pong {
            connection: connection(),
            tag: exact.clone(),
        };
        let exact_probe = exact_met.probe_wire();
        assert_eq!(exact_probe.tag, 2);
        assert_eq!(exact_probe.text, Some(exact.as_str()));
        let long_met = Met::Pong {
            connection: connection(),
            tag: long,
        };
        let long_probe = long_met.probe_wire();
        assert_eq!(long_probe.tag, 4);
        assert_eq!(long_probe.text, None);
    }

    #[tokio::test]
    async fn probe_classifies_connect_and_call_failures() {
        assert!(matches!(
            connect_failure(io::Error::from(io::ErrorKind::NotFound)),
            Met::Missing
        ));
        assert!(matches!(
            connect_failure(io::Error::from(io::ErrorKind::ConnectionRefused)),
            Met::Missing
        ));
        assert!(matches!(
            connect_failure(io::Error::from(io::ErrorKind::PermissionDenied)),
            Met::Unreachable(_)
        ));
        let malformed = serde_json::from_str::<Response>("{").unwrap_err();
        assert!(matches!(
            after_ping(connection(), Err(CallError::Garbled(malformed))),
            Met::Garbled(_)
        ));
        assert!(matches!(
            after_ping(connection(), Err(CallError::TooLong)),
            Met::Garbled(_)
        ));
        assert!(matches!(
            after_ping(
                connection(),
                Err(CallError::NotUtf8(io::Error::from(
                    io::ErrorKind::InvalidData
                )))
            ),
            Met::Garbled(_)
        ));
        assert!(matches!(
            after_ping(
                connection(),
                Err(CallError::Io(io::Error::from(io::ErrorKind::InvalidData)))
            ),
            Met::Garbled(_)
        ));
        assert!(matches!(
            after_ping(connection(), Err(CallError::Closed)),
            Met::Hung
        ));
        assert!(matches!(
            after_ping(
                connection(),
                Err(CallError::Io(io::Error::from(io::ErrorKind::UnexpectedEof)))
            ),
            Met::Hung
        ));
        assert!(matches!(
            after_ping(
                connection(),
                Err(CallError::Io(io::Error::from(io::ErrorKind::BrokenPipe)))
            ),
            Met::Hung
        ));
        assert!(matches!(
            after_ping(
                connection(),
                Err(CallError::Io(io::Error::other("serialize")))
            ),
            Met::Hung
        ));
    }

    #[test]
    fn heard_outcomes_keep_the_worker_wire_tags() {
        assert_eq!(heard_tag(&Ok(Response::Ok { reply: Reply::Bye })), 0);
        assert_eq!(
            heard_tag(&Ok(Response::Err {
                error: crate::protocol::WorkerFailure::BadRequest {
                    message: "bad".to_owned()
                }
            })),
            1
        );
        assert_eq!(heard_tag(&Err(CallError::Closed)), 2);
        assert_eq!(
            heard_tag(&Err(CallError::Garbled(
                serde_json::from_str::<Response>("{").unwrap_err()
            ))),
            3
        );
        assert_eq!(
            heard_tag(&Err(CallError::Io(io::Error::from(
                io::ErrorKind::BrokenPipe
            )))),
            3
        );
    }
    #[tokio::test]
    async fn failure_uses_the_last_outcome_for_each_why() {
        let dir = tempfile::tempdir().unwrap();
        let home = TinyHome::under(dir.path());
        let ping_error = io::Error::new(io::ErrorKind::PermissionDenied, "ping");
        assert_eq!(
            failure(
                &home,
                &ECHO,
                "ours",
                Why::Io,
                Left::Pinged(Met::Unreachable(ping_error))
            ),
            TinyError::Io {
                model: ECHO.id,
                message: "ping".to_owned()
            },
        );
        let shutdown_error = io::Error::new(io::ErrorKind::BrokenPipe, "shutdown");
        assert_eq!(
            failure(
                &home,
                &ECHO,
                "ours",
                Why::Io,
                Left::Heard(Err(shutdown_error))
            ),
            TinyError::Io {
                model: ECHO.id,
                message: "shutdown".to_owned()
            },
        );
        assert_eq!(
            failure(
                &home,
                &ECHO,
                "ours",
                Why::Protocol,
                Left::Heard(Ok(Response::Ok {
                    reply: Reply::Loaded
                }))
            ),
            TinyError::Protocol {
                model: ECHO.id,
                message: "the worker answered a shutdown with Ok { reply: Loaded }".to_owned()
            },
        );
        let pong = Met::Pong {
            connection: connection(),
            tag: "theirs".to_owned(),
        };
        let mistagged = failure(&home, &ECHO, "ours", Why::Mistagged, Left::Pinged(pong));
        assert!(mistagged.to_string().contains("tag theirs, not ours"));
        let vacant = failure(
            &home,
            &ECHO,
            "ours",
            Why::Vacant,
            Left::Pinged(Met::Missing),
        );
        assert!(vacant.to_string().contains("no worker listens"));
        let launched = TinyError::Spawn {
            model: ECHO.id,
            message: "launch failed".to_owned(),
            log: home.log(ECHO.id, BACKEND),
        };
        assert_eq!(
            failure(
                &home,
                &ECHO,
                "ours",
                Why::Spawn,
                Left::NoSpawn(launched.clone())
            ),
            launched
        );
    }
}
