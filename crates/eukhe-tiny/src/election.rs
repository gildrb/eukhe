//! The election of a model's worker: a process that needs the model pings
//! the worker's socket; a worker with its launch tag is joined, a worker
//! with another tag is shut down and replaced, and with no live worker one
//! is started. Every choice (`elect`, `shut`, `launched`, `confirm`, `bind`
//! in bend/tiny.bend section 3) runs as the compiled Bend core
//! (`bend/ffi_tiny_elect.bend`); this module connects, pings, shuts down,
//! launches and reports what it met.

use std::future::Future;
use std::io;
use std::path::Path;

use eukhe_bend::wire::{Reader, WireError, Writer};
use eukhe_bend::{call, expect_core, Entry, Error};
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
    /// The probe on the wire (`Probe` of `bend/ffi_tiny_elect.bend`).
    fn spell(&self, writer: &mut Writer) {
        match self {
            Met::Missing => writer.tag(0),
            Met::Unreachable(_) => writer.tag(1),
            Met::Pong { tag, .. } => writer.tag(2).str(tag),
            Met::Odd(_) => writer.tag(3),
            Met::Garbled(_) => writer.tag(4),
            Met::Hung => writer.tag(5),
        };
    }

    /// The IO error of a probe the core calls failed.
    fn into_error(self) -> io::Error {
        match self {
            Met::Unreachable(error) | Met::Garbled(error) => error,
            Met::Odd(other) => io::Error::new(
                io::ErrorKind::InvalidData,
                format!("the worker answered a ping with {other:?}"),
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
        Entry::TinyElect,
        Err::<T, Error>(Error::Wire(WireError::Malformed { at: 0, expected })),
    )
}

/// The request in `writer`, which holds a worker's launch tag: a tag too
/// long for the wire is the worker's protocol fault.
fn holding_tag(writer: &mut Writer) -> io::Result<String> {
    writer.finish().map_err(|error| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!("the worker's launch tag cannot be read: {error}"),
        )
    })
}

/// The compiled core's choice on `request`: a tag below `choices`.
fn ask(request: &str, choices: u32, what: &'static str) -> u32 {
    let choice = || -> Result<u32, Error> {
        let reply = call(Entry::TinyElect, request)?;
        let mut reader = Reader::reply(&reply)?;
        let choice = reader.tag_of(choices, what)?;
        reader.end()?;
        Ok(choice)
    };
    expect_core(Entry::TinyElect, choice())
}

/// The first choice of a process (`elect`).
enum Elected {
    Join(Connection),
    Replace(Connection),
    Start,
    Broken(io::Error),
}

fn elect(met: Met, tag: &str) -> io::Result<Elected> {
    let mut writer = Writer::new();
    writer.tag(0);
    met.spell(&mut writer);
    writer.str(tag);
    let choice = ask(&holding_tag(&mut writer)?, 4, "an election choice");
    Ok(match (choice, met) {
        (0, Met::Pong { connection, .. }) => Elected::Join(connection),
        (1, Met::Pong { connection, .. }) => Elected::Replace(connection),
        (2, Met::Missing | Met::Hung) => Elected::Start,
        (3.., met) => Elected::Broken(met.into_error()),
        (
            0..=2,
            Met::Missing
            | Met::Unreachable(_)
            | Met::Pong { .. }
            | Met::Odd(_)
            | Met::Garbled(_)
            | Met::Hung,
        ) => inconsistent("an election choice the probe allows"),
    })
}

/// What the shutdown of a worker of another tag heard (`shut`).
enum Shutdown {
    Down,
    Spoke(Response),
    Cut(io::Error),
}

fn shut(heard: io::Result<Response>) -> Shutdown {
    let fact = match &heard {
        Ok(Response::Ok { reply: Reply::Bye }) => 0,
        Ok(_) => 1,
        Err(error) if error.kind() == io::ErrorKind::UnexpectedEof => 2,
        Err(_) => 3,
    };
    let mut writer = Writer::new();
    writer.tag(1).tag(fact);
    match (
        ask(
            &expect_core(Entry::TinyElect, writer.finish()),
            3,
            "a shutdown choice",
        ),
        heard,
    ) {
        (0, _) => Shutdown::Down,
        (1, Ok(other)) => Shutdown::Spoke(other),
        (2.., Err(error)) => Shutdown::Cut(error),
        (1, Err(_)) | (2.., Ok(_)) => inconsistent("a shutdown choice the answer allows"),
    }
}

/// A start the process made: of a first worker, or of a replacement.
#[derive(Debug, Clone, Copy)]
enum Fresh {
    First,
    Again,
}

/// What a need that started a worker got (`launched`).
fn launched(fresh: Fresh, launch: Launched) -> Got {
    let mut writer = Writer::new();
    writer
        .tag(2)
        .tag(match fresh {
            Fresh::First => 0,
            Fresh::Again => 1,
        })
        .tag(match launch {
            Launched::Ready => 0,
            Launched::Adopted => 1,
        });
    match ask(
        &expect_core(Entry::TinyElect, writer.finish()),
        3,
        "a launch outcome",
    ) {
        0 => Got::Started,
        1 => Got::Joined,
        2.. => Got::Replaced,
    }
}

/// What the ping after a start met, for the process (`confirm`).
enum Confirmed {
    Serving(Connection),
    Mistagged(String),
    Vacant,
    Faulty(io::Error),
}

fn confirm(met: Met, tag: &str) -> io::Result<Confirmed> {
    let mut writer = Writer::new();
    writer.tag(3);
    met.spell(&mut writer);
    writer.str(tag);
    let choice = ask(&holding_tag(&mut writer)?, 4, "a start check");
    Ok(match (choice, met) {
        (0, Met::Pong { connection, .. }) => Confirmed::Serving(connection),
        (1, Met::Pong { tag: theirs, .. }) => Confirmed::Mistagged(theirs),
        (2, Met::Missing | Met::Hung) => Confirmed::Vacant,
        (3.., met) => Confirmed::Faulty(met.into_error()),
        (
            0..=2,
            Met::Missing
            | Met::Unreachable(_)
            | Met::Pong { .. }
            | Met::Odd(_)
            | Met::Garbled(_)
            | Met::Hung,
        ) => inconsistent("a start check the probe allows"),
    })
}

/// What a started worker does with the socket (`bind`).
pub(crate) enum Seat {
    /// A live worker answers: leave it in place.
    Adopt,
    /// No live worker: remove a stale socket and bind it.
    Take,
    /// The socket failed or spoke out of protocol.
    Fault(io::Error),
}

/// The choice of a started worker whose own ping met `met`.
pub(crate) fn seat(met: Met) -> Seat {
    let mut writer = Writer::new();
    writer.tag(4);
    met.spell(&mut writer);
    let request = match holding_tag(&mut writer) {
        Ok(request) => request,
        Err(error) => return Seat::Fault(error),
    };
    match (ask(&request, 3, "a seat"), met) {
        (0, Met::Pong { .. }) => Seat::Adopt,
        (1, Met::Missing | Met::Hung) => Seat::Take,
        (2.., met) => Seat::Fault(met.into_error()),
        (
            0 | 1,
            Met::Missing
            | Met::Unreachable(_)
            | Met::Pong { .. }
            | Met::Odd(_)
            | Met::Garbled(_)
            | Met::Hung,
        ) => inconsistent("a seat the probe allows"),
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
    let io = |error: io::Error| TinyError::io(model, &error);
    let fresh = match elect(probe(&socket).await, tag).map_err(io)? {
        Elected::Join(connection) => return Ok((connection, Got::Joined)),
        Elected::Replace(mut connection) => match shut(connection.call(&Request::Shutdown).await) {
            Shutdown::Down => Fresh::Again,
            Shutdown::Spoke(other) => {
                return Err(TinyError::Protocol {
                    model: model.id,
                    message: format!("the worker answered a shutdown with {other:?}"),
                });
            }
            Shutdown::Cut(error) => return Err(io(error)),
        },
        Elected::Start => Fresh::First,
        Elected::Broken(error) => return Err(io(error)),
    };
    let got = launched(fresh, launcher.launch(home, model).await?);
    let spawn = |message: String| TinyError::Spawn {
        model: model.id,
        message,
        log: home.log(model.id, BACKEND),
    };
    match confirm(probe(&socket).await, tag).map_err(io)? {
        Confirmed::Serving(connection) => Ok((connection, got)),
        Confirmed::Mistagged(theirs) => Err(spawn(format!(
            "the worker on {} answers with tag {theirs}, not {tag}",
            socket.display()
        ))),
        Confirmed::Vacant => Err(spawn(format!(
            "no worker listens on {} after the start",
            socket.display()
        ))),
        Confirmed::Faulty(error) => Err(io(error)),
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
