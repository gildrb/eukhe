//! The client of a model's worker: finds, starts, joins or replaces it
//! ([`crate::election`]), then sends it one request.

use std::os::unix::process::CommandExt;
use std::path::PathBuf;
use std::process::Stdio;

use tokio::io::{AsyncBufReadExt, BufReader};
use tokio::process::Child;

use crate::catalog::CatalogModel;
use crate::election::{self, Launched, Launcher, BACKEND};
use crate::engine::EngineOptions;
use crate::paths::TinyHome;
use crate::protocol::{
    Audio, ChatReply, ChatRequest, Reply, Request, SpeakRequest, TranscribeRequest, Transcript,
    WorkerFailure,
};
use crate::worker::launch_tag;

/// Why a request to a local model failed.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum TinyError {
    /// A file of the model is missing (or has another size than its pin).
    #[error("the local model {model} is not installed (eukhe tiny-models download {model})")]
    NotInstalled { model: &'static str },
    /// The worker could not be started.
    #[error("could not start the worker of {model}: {message} (log: {})", log.display())]
    Spawn {
        model: &'static str,
        message: String,
        log: PathBuf,
    },
    /// The worker closed or failed mid-request.
    #[error("the worker of {model} exited mid-request (log: {})", log.display())]
    Crashed { model: &'static str, log: PathBuf },
    /// The worker could not serve the request.
    #[error(transparent)]
    Worker(#[from] WorkerFailure),
    /// The worker's socket failed.
    #[error("the socket of the worker of {model} failed: {message}")]
    Io {
        model: &'static str,
        message: String,
    },
    /// The worker answered out of protocol.
    #[error("the worker of {model} answered out of protocol: {message}")]
    Protocol {
        model: &'static str,
        message: String,
    },
}

impl TinyError {
    pub(crate) fn io(model: &CatalogModel, error: &std::io::Error) -> TinyError {
        TinyError::Io {
            model: model.id,
            message: error.to_string(),
        }
    }
}

/// The client of the local models' workers: each request elects the
/// model's worker (joins it, replaces a worker of another launch tag, or
/// starts one) and sends it the request.
#[derive(Debug, Clone)]
pub struct TinyClient {
    home: TinyHome,
    tag: String,
    launcher: WorkerLauncher,
}

impl TinyClient {
    /// A client whose workers run `worker_exe tiny-worker ...` with
    /// `options` (the eukhe binary).
    #[must_use]
    pub fn new(home: TinyHome, options: EngineOptions, worker_exe: PathBuf) -> TinyClient {
        TinyClient {
            home,
            tag: launch_tag(BACKEND, &options),
            launcher: WorkerLauncher {
                exe: worker_exe,
                options,
            },
        }
    }

    /// The reply of the worker of `model` to `request`.
    async fn reply(
        &self,
        model: &'static CatalogModel,
        request: &Request,
    ) -> Result<Reply, TinyError> {
        election::request(&self.home, model, &self.tag, &self.launcher, request)
            .await
            .map(|(reply, _got)| reply)
    }

    /// A greedy chat completion on a text model.
    ///
    /// # Errors
    ///
    /// See [`TinyError`].
    #[tracing::instrument(skip_all, fields(model = model.id))]
    pub async fn chat(
        &self,
        model: &'static CatalogModel,
        request: ChatRequest,
    ) -> Result<ChatReply, TinyError> {
        match self.reply(model, &Request::Chat(request)).await? {
            Reply::Chat(reply) => Ok(reply),
            other @ (Reply::Pong { .. }
            | Reply::Loaded
            | Reply::Transcript(_)
            | Reply::Speech(_)
            | Reply::Bye) => Err(unexpected(model, "chat", &other)),
        }
    }

    /// Speech to text on a speech-to-text model.
    ///
    /// # Errors
    ///
    /// See [`TinyError`].
    #[tracing::instrument(skip_all, fields(model = model.id))]
    pub async fn transcribe(
        &self,
        model: &'static CatalogModel,
        request: TranscribeRequest,
    ) -> Result<Transcript, TinyError> {
        match self.reply(model, &Request::Transcribe(request)).await? {
            Reply::Transcript(transcript) => Ok(transcript),
            other @ (Reply::Pong { .. }
            | Reply::Loaded
            | Reply::Chat(_)
            | Reply::Speech(_)
            | Reply::Bye) => Err(unexpected(model, "transcript", &other)),
        }
    }

    /// Text to speech on a text-to-speech model.
    ///
    /// # Errors
    ///
    /// See [`TinyError`].
    #[tracing::instrument(skip_all, fields(model = model.id))]
    pub async fn speak(
        &self,
        model: &'static CatalogModel,
        request: SpeakRequest,
    ) -> Result<Audio, TinyError> {
        match self.reply(model, &Request::Speak(request)).await? {
            Reply::Speech(audio) => Ok(audio),
            other @ (Reply::Pong { .. }
            | Reply::Loaded
            | Reply::Chat(_)
            | Reply::Transcript(_)
            | Reply::Bye) => Err(unexpected(model, "speech", &other)),
        }
    }
}

fn unexpected(model: &CatalogModel, expected: &str, reply: &Reply) -> TinyError {
    TinyError::Protocol {
        model: model.id,
        message: format!("expected a {expected} reply, got {reply:?}"),
    }
}

/// Starts workers as
/// `<exe> tiny-worker <model> --backend onnx --agent-dir <dir> ...`.
#[derive(Debug, Clone)]
struct WorkerLauncher {
    exe: PathBuf,
    options: EngineOptions,
}

impl WorkerLauncher {
    /// The worker command of `model` under `home`: the worker takes its
    /// agent dir from the command line, never from its environment.
    fn command(&self, home: &TinyHome, model: &'static CatalogModel) -> std::process::Command {
        let EngineOptions {
            device,
            dtype,
            runtime_library,
        } = &self.options;
        let mut command = std::process::Command::new(&self.exe);
        command
            .arg("tiny-worker")
            .arg(model.id)
            .args(["--backend", BACKEND.id()])
            .arg("--agent-dir")
            .arg(home.agent_dir())
            .args(["--device", device]);
        if !dtype.is_empty() {
            command.args(["--dtype", dtype]);
        }
        if !runtime_library.as_os_str().is_empty() {
            command.arg("--runtime-library").arg(runtime_library);
        }
        command
    }
}

impl Launcher for WorkerLauncher {
    #[tracing::instrument(skip_all, fields(model = model.id))]
    async fn launch(
        &self,
        home: &TinyHome,
        model: &'static CatalogModel,
    ) -> Result<Launched, TinyError> {
        // The worker outlives this process; dropping the child leaves it running.
        spawn_detached(self.command(home, model), home, model)
            .await
            .map(|(launched, _child)| launched)
    }
}

/// Runs `command` as a detached worker of `model`: in its own process
/// group (a terminal's Ctrl-C does not reach it), stdin null, stderr
/// appended to [`TinyHome::log`], and waits for its `ready` or `adopted`
/// line on stdout (earlier lines are skipped: a test harness prints its own
/// header first). Creates the run dir (0700) first.
///
/// # Errors
///
/// [`TinyError::Spawn`] when the run dir, the log or the process cannot be
/// created, or when the process closes stdout before either line.
#[tracing::instrument(level = "debug", skip_all, fields(model = model.id))]
pub(crate) async fn spawn_detached(
    mut command: std::process::Command,
    home: &TinyHome,
    model: &'static CatalogModel,
) -> Result<(Launched, Child), TinyError> {
    let log = home.log(model.id, BACKEND);
    let spawn = |message: String| TinyError::Spawn {
        model: model.id,
        message,
        log: log.clone(),
    };
    home.create_run_dir()
        .map_err(|error| spawn(format!("cannot create {}: {error}", home.run.display())))?;
    let stderr = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(&log)
        .map_err(|error| spawn(format!("cannot open {}: {error}", log.display())))?;
    command
        .process_group(0)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(stderr);
    let mut child = tokio::process::Command::from(command)
        .spawn()
        .map_err(|error| spawn(format!("cannot run the worker: {error}")))?;
    let Some(stdout) = child.stdout.take() else {
        return Err(spawn("the worker has no stdout pipe".to_owned()));
    };
    let mut lines = BufReader::new(stdout).lines();
    loop {
        match lines.next_line().await {
            Ok(Some(line)) => match line.as_str() {
                "ready" => return Ok((Launched::Ready, child)),
                "adopted" => return Ok((Launched::Adopted, child)),
                _ => {}
            },
            Ok(None) => return Err(spawn("the worker exited before it was ready".to_owned())),
            Err(error) => return Err(spawn(format!("cannot read the worker's stdout: {error}"))),
        }
    }
}

#[cfg(test)]
mod tests;
