//! The bridge from the tiny-model service's worker election to its Bend
//! model (`bend/tiny.bend`, docs/inference.md S9): generated needs run
//! through the Rust code, and `bend/bridge_tiny.bend` must print the same
//! transcript, byte for byte. (The pick runs as the compiled model itself:
//! `roles::pick`.)
//!
//! Part `w`: each line is a need `n P TAG` (process P needs the model with
//! launch tag `tTAG`) or an exit `g`. A need is a real request through the
//! election ([`election::request`]) on real sockets, whose launcher runs
//! the real worker ([`bind`], [`serve`] with the [`Echo`] engine) in a
//! tokio task; an exit of a live worker is a [`Request::Shutdown`] or a
//! crash (its task aborted, its socket left stale). After each line it
//! prints what the need got (`S`, `J`, `R`; `-` for an exit), then the
//! worker that answers on the socket: ` w OWNER TAG` (OWNER: the process
//! whose need started it) or ` none`.

use std::fmt::Write;
use std::io;
use std::sync::{Mutex, PoisonError};
use std::time::Duration;

use tokio::task::JoinHandle;

use crate::catalog::CatalogModel;
use crate::client::TinyError;
use crate::election::{self, probe, Got, Launched, Launcher, Probe, BACKEND};
use crate::paths::TinyHome;
use crate::protocol::{ChatMessage, ChatRequest, ChatRole, Reply, Request, Response};
use crate::testing::{compare, Echo, Rng, Scenario, ECHO};
use crate::worker::{bind, serve, Bound, Exit};

const MODEL: &str = "bend/bridge_tiny.bend";

/// Longer than any scenario: the bridge's workers exit by its events only.
const IDLE: Duration = Duration::from_secs(3600);

/// The worker tasks one scenario started, the last one current.
type Workers = Mutex<Vec<JoinHandle<io::Result<Exit>>>>;

/// Starts the worker in this process: the real [`bind`] and [`serve`] with
/// the [`Echo`] engine, in a tokio task.
struct InProcess<'a> {
    tag: String,
    workers: &'a Workers,
}

impl Launcher for InProcess<'_> {
    async fn launch(
        &self,
        home: &TinyHome,
        model: &'static CatalogModel,
    ) -> Result<Launched, TinyError> {
        match bind(home, model, BACKEND)
            .await
            .map_err(|error| TinyError::io(model, &error))?
        {
            Bound::Adopted => Ok(Launched::Adopted),
            Bound::Listening(listening) => {
                let task = tokio::spawn(serve(listening, self.tag.clone(), Box::new(Echo), IDLE));
                self.workers
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push(task);
                Ok(Launched::Ready)
            }
        }
    }
}

/// One generated event of part `w`.
#[derive(Debug, Clone, Copy)]
enum Event {
    Need {
        process: u64,
        tag: u64,
    },
    /// The worker exits through the protocol.
    Shutdown,
    /// The worker dies: its task is aborted, its socket left behind.
    Crash,
}

fn tag(n: u64) -> String {
    format!("t{n}")
}

/// The current worker task (the last started).
fn current(workers: &Workers) -> Option<JoinHandle<io::Result<Exit>>> {
    workers.lock().unwrap_or_else(PoisonError::into_inner).pop()
}

/// Runs `events` through the election and the worker; the transcript.
async fn run(events: &[Event]) -> String {
    let dir = tempfile::tempdir().unwrap();
    let home = TinyHome::under(dir.path());
    std::fs::create_dir_all(home.model_dir(ECHO.id)).unwrap();
    let socket = home.socket(ECHO.id, BACKEND);
    let workers = Workers::default();
    let mut owner = None;
    let mut transcript = String::new();
    for event in events {
        match *event {
            Event::Need { process, tag: t } => {
                let launcher = InProcess {
                    tag: tag(t),
                    workers: &workers,
                };
                let request = Request::Chat(ChatRequest {
                    messages: vec![ChatMessage {
                        role: ChatRole::User,
                        content: format!("p{process}"),
                    }],
                    prefill: String::new(),
                    stop: Vec::new(),
                    max_tokens: 1,
                });
                match election::request(&home, &ECHO, &tag(t), &launcher, &request).await {
                    Ok((Reply::Chat(_), got)) => {
                        let letter = match got {
                            Got::Started => {
                                owner = Some(process);
                                "S"
                            }
                            Got::Joined => "J",
                            Got::Replaced => {
                                owner = Some(process);
                                "R"
                            }
                        };
                        transcript.push_str(letter);
                    }
                    other => write!(transcript, "{other:?}").unwrap(),
                }
            }
            Event::Shutdown => {
                transcript.push('-');
                if let Probe::Live { mut connection, .. } = probe(&socket).await.unwrap() {
                    let bye = connection.call(&Request::Shutdown).await.unwrap();
                    assert_eq!(bye, Response::Ok { reply: Reply::Bye });
                    let exit = current(&workers).unwrap().await.unwrap().unwrap();
                    assert_eq!(exit, Exit::Shutdown);
                }
            }
            Event::Crash => {
                transcript.push('-');
                if matches!(probe(&socket).await.unwrap(), Probe::Live { .. }) {
                    let worker = current(&workers).unwrap();
                    worker.abort();
                    assert!(worker.await.unwrap_err().is_cancelled());
                }
            }
        }
        match probe(&socket).await.unwrap() {
            Probe::Live { tag: live, .. } => writeln!(
                transcript,
                " w {} {}",
                owner.map_or_else(|| "?".to_owned(), |owner| owner.to_string()),
                live.trim_start_matches('t')
            )
            .unwrap(),
            Probe::Absent => transcript.push_str(" none\n"),
        }
    }
    for worker in std::mem::take(&mut *workers.lock().unwrap_or_else(PoisonError::into_inner)) {
        worker.abort();
    }
    transcript
}

/// The election and the worker do what the model does on 60 scenarios of
/// 1 to 12 events: needs of 3 processes with 3 tags, exits through the
/// protocol and crashes, with and without a live worker.
#[test]
fn the_rust_election_equals_the_bend_model() {
    let mut rng = Rng(0x7e1c_e1ec_7000_0009);
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .unwrap();
    let scenarios: Vec<Scenario> = (0..60)
        .map(|at| {
            let events: Vec<Event> = (0..rng.range(1, 12))
                .map(|_| match rng.below(6) {
                    0 => Event::Shutdown,
                    1 => Event::Crash,
                    2.. => Event::Need {
                        process: rng.below(3),
                        tag: rng.below(3),
                    },
                })
                .collect();
            let mut lines = vec!["w".to_owned()];
            lines.extend(events.iter().map(|event| match event {
                Event::Need { process, tag } => format!("n {process} {tag}"),
                Event::Shutdown | Event::Crash => "g".to_owned(),
            }));
            Scenario {
                name: format!("worker-{at}"),
                events: lines.join("\n"),
                transcript: runtime.block_on(run(&events)),
            }
        })
        .collect();
    compare(MODEL, scenarios);
}
