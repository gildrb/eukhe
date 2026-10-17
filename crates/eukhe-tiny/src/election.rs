//! The election of a model's worker (`step` and `got` in bend/tiny.bend):
//! a process that needs the model pings the worker's socket; a worker with
//! its launch tag is joined, a worker with another tag is shut down and
//! replaced, and with no live worker one is started.

use std::future::Future;
use std::io;
use std::path::Path;

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

/// What answers on a worker socket.
pub(crate) enum Probe {
    /// No socket, a stale one, or a worker that closed on the ping.
    Absent,
    /// A worker answered the ping with its launch tag.
    Live { connection: Connection, tag: String },
}

/// Connects to `socket` and pings it.
///
/// # Errors
///
/// A connect error other than a missing or refused socket, or an answer
/// that is not a pong ([`io::ErrorKind::InvalidData`]).
#[tracing::instrument(level = "debug")]
pub(crate) async fn probe(socket: &Path) -> io::Result<Probe> {
    let stream = match UnixStream::connect(socket).await {
        Ok(stream) => stream,
        Err(error) => {
            return match error.kind() {
                io::ErrorKind::NotFound | io::ErrorKind::ConnectionRefused => Ok(Probe::Absent),
                _ => Err(error),
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
        }) => Ok(Probe::Live { connection, tag }),
        Ok(other) => Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("the worker answered a ping with {other:?}"),
        )),
        Err(error) if error.kind() == io::ErrorKind::InvalidData => Err(error),
        Err(_) => Ok(Probe::Absent),
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
    let probed = |result: io::Result<Probe>| result.map_err(|error| TinyError::io(model, &error));
    let got = match probed(probe(&socket).await)? {
        Probe::Live {
            connection,
            tag: theirs,
        } if theirs == tag => {
            return Ok((connection, Got::Joined));
        }
        Probe::Live { mut connection, .. } => {
            match connection.call(&Request::Shutdown).await {
                Ok(Response::Ok { reply: Reply::Bye }) => {}
                Ok(other) => {
                    return Err(TinyError::Protocol {
                        model: model.id,
                        message: format!("the worker answered a shutdown with {other:?}"),
                    });
                }
                // It exited on its own meanwhile (idle): it is gone too.
                Err(error) if error.kind() == io::ErrorKind::UnexpectedEof => {}
                Err(error) => return Err(TinyError::io(model, &error)),
            }
            Got::Replaced
        }
        Probe::Absent => Got::Started,
    };
    let got = match launcher.launch(home, model).await? {
        Launched::Ready => got,
        Launched::Adopted => Got::Joined,
    };
    let spawn = |message: String| TinyError::Spawn {
        model: model.id,
        message,
        log: home.log(model.id, BACKEND),
    };
    match probed(probe(&socket).await)? {
        Probe::Live {
            connection,
            tag: theirs,
        } if theirs == tag => Ok((connection, got)),
        Probe::Live { tag: theirs, .. } => Err(spawn(format!(
            "the worker on {} answers with tag {theirs}, not {tag}",
            socket.display()
        ))),
        Probe::Absent => Err(spawn(format!(
            "no worker listens on {} after the start",
            socket.display()
        ))),
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
