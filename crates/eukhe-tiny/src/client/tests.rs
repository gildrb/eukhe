//! The election with real worker processes: this test binary re-runs
//! itself as the worker (`worker_helper`, which runs [`run_worker`] with
//! the [`Echo`] engine) on the command line [`WorkerLauncher`] builds, in a
//! temp agent dir. The worker child has no agent dir variable and another
//! `HOME`: only its command line points it at the client's agent dir.

use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::{Mutex, PoisonError};

use eukhe_types::platform::dirs::ENV_AGENT_DIR;
use tokio::process::Child;

use super::{spawn_detached, TinyError, WorkerLauncher};
use crate::catalog::{find, CatalogModel};
use crate::election::{self, probe, Got, Launched, Launcher, Met, BACKEND};
use crate::engine::EngineOptions;
use crate::paths::TinyHome;
use crate::protocol::{ChatMessage, ChatReply, ChatRequest, ChatRole, Reply, Request, StopReason};
use crate::testing::{Echo, CRASH};
use crate::worker::{launch_tag, run_worker};

/// Set in a worker child: its `tiny-worker` arguments, one a line.
const HELPER_ARGS: &str = "EUKHE_TINY_TEST_WORKER_ARGS";

/// The full name of [`worker_helper`] in this test binary.
const HELPER: &str = "client::tests::worker_helper";

/// The idle window of a worker child that is not testing it: long enough
/// for a test, short enough that a failed test leaves no worker behind
/// for long.
const TEST_IDLE_MS: u64 = 120_000;

/// The worker process of the tests: inert in a normal test run.
#[tokio::test]
async fn worker_helper() {
    let Ok(args) = std::env::var(HELPER_ARGS) else {
        return;
    };
    let args: Vec<String> = args.lines().map(str::to_owned).collect();
    // Exits here: libtest would print its result to the stdout pipe the
    // client closed.
    let code = run_worker(&args, |_model, _dir, _options| Ok(Box::new(Echo))).await;
    std::process::exit(i32::from(code != ExitCode::SUCCESS));
}

/// Starts this test binary as the worker, with `device` (the tag) and an
/// idle window; keeps the children so the tests can wait on them.
struct Helper<'a> {
    device: &'a str,
    idle_ms: u64,
    children: Mutex<Vec<Child>>,
}

impl<'a> Helper<'a> {
    fn new(device: &'a str, idle_ms: u64) -> Helper<'a> {
        Helper {
            device,
            idle_ms,
            children: Mutex::new(Vec::new()),
        }
    }

    fn tag(&self) -> String {
        launch_tag(BACKEND, &options(self.device))
    }

    fn children(&self) -> Vec<Child> {
        std::mem::take(&mut *self.children.lock().unwrap_or_else(PoisonError::into_inner))
    }
}

impl Launcher for Helper<'_> {
    async fn launch(
        &self,
        home: &TinyHome,
        model: &'static CatalogModel,
    ) -> Result<Launched, TinyError> {
        let worker = WorkerLauncher {
            exe: PathBuf::from("eukhe"),
            options: options(self.device),
        }
        .command(home, model);
        let args: Vec<String> = worker
            .get_args()
            .skip(1)
            .map(|arg| arg.to_str().expect("UTF-8 argument").to_owned())
            .collect();
        let mut command = std::process::Command::new(std::env::current_exe().unwrap());
        command
            .args(["--exact", HELPER, "--nocapture"])
            .env(HELPER_ARGS, args.join("\n"))
            .env_remove(ENV_AGENT_DIR)
            .env("HOME", home.agent_dir().join("not-the-agent-dir"))
            .env("EUKHE_TINY_WORKER_IDLE_MS", self.idle_ms.to_string());
        let (launched, child) = spawn_detached(command, home, model).await?;
        self.children
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(child);
        Ok(launched)
    }
}

fn options(device: &str) -> EngineOptions {
    EngineOptions {
        device: device.to_owned(),
        dtype: String::new(),
        runtime_library: PathBuf::new(),
    }
}

fn model() -> &'static CatalogModel {
    find("lfm2.5-230m").unwrap()
}

/// An agent dir with `model` installed (sparse files of the pinned sizes).
fn installed_home(model: &CatalogModel) -> (tempfile::TempDir, TinyHome) {
    let dir = tempfile::tempdir().unwrap();
    let home = TinyHome::under(dir.path());
    for file in model.files {
        let path = home.model_dir(model.id).join(file.path);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::File::create(&path)
            .unwrap()
            .set_len(file.size)
            .unwrap();
    }
    (dir, home)
}

fn chat(text: &str) -> Request {
    Request::Chat(ChatRequest {
        messages: vec![ChatMessage {
            role: ChatRole::User,
            content: text.to_owned(),
        }],
        prefill: String::new(),
        stop: Vec::new(),
        max_tokens: 8,
    })
}

fn echoed(text: &str) -> Reply {
    Reply::Chat(ChatReply {
        text: text.to_owned(),
        stop: StopReason::Eos,
    })
}

async fn live_tag(socket: &Path) -> Option<String> {
    match probe(socket).await {
        Met::Pong { tag, .. } => Some(tag),
        Met::Missing | Met::Hung => None,
        Met::Unreachable(_) | Met::Odd(_) | Met::Garbled(_) => panic!("the socket failed"),
    }
}

/// One client starts the worker, a second client with the same tag joins
/// it (starting nothing), a client with another tag replaces it: the old
/// process exits and the new tag answers.
#[tokio::test]
async fn the_election_starts_joins_and_replaces_real_workers() {
    let model = model();
    let (_dir, home) = installed_home(model);
    let socket = home.socket(model.id, BACKEND);

    let first = Helper::new("a", TEST_IDLE_MS);
    let started = election::request(&home, model, &first.tag(), &first, &chat("one")).await;
    assert_eq!(started, Ok((echoed("one"), Got::Started)));

    let second = Helper::new("a", TEST_IDLE_MS);
    let joined = election::request(&home, model, &second.tag(), &second, &chat("two")).await;
    assert_eq!(joined, Ok((echoed("two"), Got::Joined)));
    assert_eq!(second.children().len(), 0);

    let other = Helper::new("b", TEST_IDLE_MS);
    let replaced = election::request(&home, model, &other.tag(), &other, &chat("three")).await;
    assert_eq!(replaced, Ok((echoed("three"), Got::Replaced)));
    for mut old in first.children() {
        old.wait().await.unwrap();
    }
    assert_eq!(live_tag(&socket).await, Some(other.tag()));

    let bye = election::request(&home, model, &other.tag(), &other, &Request::Shutdown).await;
    assert_eq!(bye, Ok((Reply::Bye, Got::Joined)));
    for mut new in other.children() {
        new.wait().await.unwrap();
    }
    assert_eq!(live_tag(&socket).await, None);
}

/// The worker command carries the client's agent dir, so a worker started
/// without an agent dir variable (a supervisor given `--agent-dir`) and
/// with another `HOME` binds and serves under the client's agent dir.
#[tokio::test]
async fn the_worker_serves_the_clients_agent_dir() {
    let model = model();
    let (dir, home) = installed_home(model);
    let launcher = WorkerLauncher {
        exe: PathBuf::from("eukhe"),
        options: options("a"),
    };
    let args: Vec<std::ffi::OsString> = launcher
        .command(&home, model)
        .get_args()
        .map(std::ffi::OsStr::to_owned)
        .collect();
    let helper = Helper::new("a", TEST_IDLE_MS);
    let started = election::request(&home, model, &helper.tag(), &helper, &chat("hi")).await;
    let bye = election::request(&home, model, &helper.tag(), &helper, &Request::Shutdown).await;
    for mut child in helper.children() {
        child.wait().await.unwrap();
    }
    let expected_args: Vec<std::ffi::OsString> = [
        "tiny-worker".as_ref(),
        model.id.as_ref(),
        "--backend".as_ref(),
        "onnx".as_ref(),
        "--agent-dir".as_ref(),
        dir.path().as_os_str(),
        "--device".as_ref(),
        "a".as_ref(),
    ]
    .map(std::ffi::OsStr::to_owned)
    .into();
    assert_eq!(
        (
            args,
            started,
            bye,
            dir.path().join("not-the-agent-dir").exists()
        ),
        (
            expected_args,
            Ok((echoed("hi"), Got::Started)),
            Ok((Reply::Bye, Got::Joined)),
            false
        )
    );
}

/// A worker with no request for its idle window exits and unlinks its
/// socket.
#[tokio::test]
async fn an_idle_worker_exits_and_unlinks_its_socket() {
    let model = model();
    let (_dir, home) = installed_home(model);
    let launcher = Helper::new("a", 200);
    let started = election::request(&home, model, &launcher.tag(), &launcher, &chat("hi")).await;
    assert_eq!(started, Ok((echoed("hi"), Got::Started)));
    let mut exits = Vec::new();
    for mut child in launcher.children() {
        exits.push(child.wait().await.unwrap().code());
    }
    assert_eq!(
        (exits, home.socket(model.id, BACKEND).exists()),
        (vec![Some(0)], false)
    );
}

/// A worker that dies mid-request is a crash, with the worker's log.
#[tokio::test]
async fn a_worker_that_dies_mid_request_is_a_crash() {
    let model = model();
    let (_dir, home) = installed_home(model);
    let launcher = Helper::new("a", TEST_IDLE_MS);
    let crashed = election::request(&home, model, &launcher.tag(), &launcher, &chat(CRASH)).await;
    assert_eq!(
        crashed,
        Err(TinyError::Crashed {
            model: model.id,
            log: home.log(model.id, BACKEND),
        })
    );
    for mut child in launcher.children() {
        child.wait().await.unwrap();
    }
}

/// A model with a missing file fails before any worker starts.
#[tokio::test]
async fn a_model_not_installed_starts_no_worker() {
    let model = model();
    let dir = tempfile::tempdir().unwrap();
    let home = TinyHome::under(dir.path());
    let launcher = Helper::new("a", TEST_IDLE_MS);
    let refused = election::request(&home, model, &launcher.tag(), &launcher, &chat("hi")).await;
    assert_eq!(
        (refused, launcher.children().len()),
        (Err(TinyError::NotInstalled { model: model.id }), 0)
    );
}
