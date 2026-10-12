//! The `signal-cli jsonRpc` child: one request per stdin line, responses
//! matched by id, `receive` notifications forwarded. A supervisor restarts
//! the child with backoff; requests fail fast while it is down.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::Stdio;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Duration;

use anyhow::{anyhow, bail, Context, Result};
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader, Lines};
use tokio::process::{Child, ChildStdout, Command};
use tokio::sync::{mpsc, oneshot, Mutex};
use tokio::task::JoinHandle;
use tokio::time::Instant;

const REQUEST_TIMEOUT: Duration = Duration::from_secs(30);
const BACKOFF_MIN: Duration = Duration::from_secs(1);
const BACKOFF_MAX: Duration = Duration::from_mins(1);
/// A child that ran this long was healthy: the next restart waits the
/// shortest backoff again.
const HEALTHY_RUN: Duration = Duration::from_mins(5);
/// Requests waiting for the stdin writer.
const WRITE_QUEUE: usize = 64;

/// A JSON-RPC notification of `signal-cli` (`receive`).
#[derive(Debug, Deserialize)]
pub(super) struct Notification {
    pub(super) method: String,
    pub(super) params: Value,
}

/// A handle to the supervised `signal-cli` child. Cheap to clone.
#[derive(Clone)]
pub(super) struct Rpc {
    shared: Arc<Shared>,
}

struct Shared {
    next_id: AtomicU64,
    link: Mutex<Link>,
}

/// The current child, or why there is none.
enum Link {
    Up {
        writer: mpsc::Sender<String>,
        pending: HashMap<u64, oneshot::Sender<Result<Value>>>,
    },
    Down {
        reason: String,
    },
}

/// One running child and the tasks that serve it.
struct Running {
    child: Child,
    stdout: Lines<BufReader<ChildStdout>>,
    writer: JoinHandle<Result<()>>,
}

#[derive(Serialize)]
struct Request<'a, P> {
    jsonrpc: &'static str,
    id: u64,
    method: &'static str,
    params: &'a P,
}

/// One stdout line of `signal-cli`.
#[derive(Deserialize)]
#[serde(untagged)]
enum Frame {
    Notification(Notification),
    Response(Response),
}

#[derive(Deserialize)]
struct Response {
    /// Null when `signal-cli` could not read the request's id.
    id: Option<u64>,
    #[serde(flatten)]
    outcome: Outcome,
}

#[derive(Deserialize)]
#[serde(rename_all = "lowercase")]
enum Outcome {
    Result(Value),
    Error(RpcError),
}

#[derive(Deserialize)]
struct RpcError {
    code: i64,
    message: String,
}

impl Shared {
    /// Marks the link down and fails every request still waiting on it.
    async fn go_down(&self, reason: &str) {
        let previous = std::mem::replace(
            &mut *self.link.lock().await,
            Link::Down {
                reason: reason.to_owned(),
            },
        );
        match previous {
            Link::Up { pending, .. } => {
                for waiter in pending.into_values() {
                    // A closed receiver is a request that already gave up.
                    let _ = waiter.send(Err(anyhow!(
                        "signal-cli stopped before it answered: {reason}"
                    )));
                }
            }
            Link::Down { .. } => {}
        }
    }
}

impl Rpc {
    /// Starts `<cli_path> -a <account> jsonRpc` and its supervisor.
    /// Notifications go to `notifications`; the supervisor stops when that
    /// channel closes.
    #[tracing::instrument(skip_all, fields(cli_path = %cli_path.display()))]
    pub(super) async fn start(
        cli_path: PathBuf,
        account: String,
        notifications: mpsc::UnboundedSender<Notification>,
    ) -> Result<Rpc> {
        let shared = Arc::new(Shared {
            next_id: AtomicU64::new(1),
            link: Mutex::new(Link::Down {
                reason: "signal-cli is starting".to_owned(),
            }),
        });
        let running = launch(&shared, &cli_path, &account).await?;
        tokio::spawn(supervise(
            Arc::clone(&shared),
            cli_path,
            account,
            running,
            notifications,
        ));
        Ok(Rpc { shared })
    }

    /// Sends one request and waits up to 30 s for its result.
    #[tracing::instrument(level = "debug", skip(self, params))]
    pub(super) async fn call<P, R>(&self, method: &'static str, params: &P) -> Result<R>
    where
        P: Serialize + Sync,
        R: DeserializeOwned,
    {
        let id = self.shared.next_id.fetch_add(1, Ordering::Relaxed);
        let mut line = serde_json::to_string(&Request {
            jsonrpc: "2.0",
            id,
            method,
            params,
        })
        .with_context(|| format!("failed to encode the signal-cli {method} request"))?;
        line.push('\n');
        let (waiter, answer) = oneshot::channel();
        let writer = match &mut *self.shared.link.lock().await {
            Link::Up { writer, pending } => {
                pending.insert(id, waiter);
                writer.clone()
            }
            Link::Down { reason } => bail!("signal-cli is not running: {reason}"),
        };
        let exchange = async {
            writer
                .send(line)
                .await
                .map_err(|_| anyhow!("signal-cli stopped before the request was written"))?;
            answer
                .await
                .map_err(|_| anyhow!("signal-cli dropped the request"))?
        };
        match tokio::time::timeout(REQUEST_TIMEOUT, exchange).await {
            Ok(result) => {
                let result = result.with_context(|| format!("signal-cli {method} failed"))?;
                serde_json::from_value(result)
                    .with_context(|| format!("signal-cli {method} returned an unexpected result"))
            }
            Err(_elapsed) => {
                match &mut *self.shared.link.lock().await {
                    Link::Up { pending, .. } => {
                        pending.remove(&id);
                    }
                    Link::Down { .. } => {}
                }
                bail!(
                    "signal-cli did not answer {method} within {} s",
                    REQUEST_TIMEOUT.as_secs()
                )
            }
        }
    }
}

/// Spawns one child, its stdin writer and stderr forwarder, and marks the
/// link up.
#[tracing::instrument(skip_all)]
async fn launch(shared: &Shared, cli_path: &Path, account: &str) -> Result<Running> {
    let mut child = Command::new(cli_path)
        .arg("-a")
        .arg(account)
        .arg("jsonRpc")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .kill_on_drop(true)
        .spawn()
        .with_context(|| format!("failed to start {}", cli_path.display()))?;
    let mut stdin = child.stdin.take().context("signal-cli has no stdin pipe")?;
    let stdout = child
        .stdout
        .take()
        .context("signal-cli has no stdout pipe")?;
    let stderr = child
        .stderr
        .take()
        .context("signal-cli has no stderr pipe")?;
    tokio::spawn(async move {
        let mut lines = BufReader::new(stderr).lines();
        loop {
            match lines.next_line().await {
                Ok(Some(line)) => tracing::warn!(target: "signal_cli", "{line}"),
                Ok(None) => break,
                Err(error) => {
                    tracing::warn!(%error, "failed to read signal-cli stderr");
                    break;
                }
            }
        }
    });
    let (writer, mut requests) = mpsc::channel::<String>(WRITE_QUEUE);
    let writer_task = tokio::spawn(async move {
        while let Some(line) = requests.recv().await {
            stdin
                .write_all(line.as_bytes())
                .await
                .context("failed to write to signal-cli stdin")?;
            stdin
                .flush()
                .await
                .context("failed to flush signal-cli stdin")?;
        }
        Ok(())
    });
    *shared.link.lock().await = Link::Up {
        writer,
        pending: HashMap::new(),
    };
    tracing::info!(pid = ?child.id(), "signal-cli started");
    Ok(Running {
        child,
        stdout: BufReader::new(stdout).lines(),
        writer: writer_task,
    })
}

/// Serves the child until it exits, then restarts it with exponential
/// backoff (1 s to 60 s, reset after 5 healthy minutes). Returns when the
/// notification receiver closes.
#[tracing::instrument(skip_all)]
async fn supervise(
    shared: Arc<Shared>,
    cli_path: PathBuf,
    account: String,
    mut running: Running,
    notifications: mpsc::UnboundedSender<Notification>,
) {
    let mut backoff = BACKOFF_MIN;
    loop {
        let started = Instant::now();
        let reason = loop {
            tokio::select! {
                () = notifications.closed() => {
                    shared.go_down("the gateway stopped").await;
                    return;
                }
                line = running.stdout.next_line() => match line {
                    Ok(Some(line)) => match serde_json::from_str::<Frame>(&line) {
                        Ok(Frame::Response(Response { id: Some(id), outcome })) => {
                            let waiter = match &mut *shared.link.lock().await {
                                Link::Up { pending, .. } => pending.remove(&id),
                                Link::Down { .. } => None,
                            };
                            let result = match outcome {
                                Outcome::Result(value) => Ok(value),
                                Outcome::Error(error) => {
                                    Err(anyhow!("{} (code {})", error.message, error.code))
                                }
                            };
                            if let Some(waiter) = waiter {
                                // A closed receiver is a request that already gave up.
                                let _ = waiter.send(result);
                            } else {
                                tracing::debug!(id, "signal-cli answered an abandoned request");
                            }
                        }
                        Ok(Frame::Response(Response { id: None, outcome })) => match outcome {
                            Outcome::Result(_) => {
                                tracing::warn!("signal-cli sent a result without a request id");
                            }
                            Outcome::Error(error) => tracing::warn!(
                                code = error.code,
                                "signal-cli rejected a request: {}",
                                error.message
                            ),
                        },
                        Ok(Frame::Notification(notification)) => {
                            if notifications.send(notification).is_err() {
                                shared.go_down("the gateway stopped").await;
                                return;
                            }
                        }
                        // The line may hold message text: log only the parse error.
                        Err(error) => tracing::warn!(%error, "unrecognized signal-cli output line"),
                    },
                    Ok(None) => break match running.child.wait().await {
                        Ok(status) => format!("it exited with {status}"),
                        Err(error) => format!("waiting for it failed: {error}"),
                    },
                    Err(error) => {
                        if let Err(kill) = running.child.kill().await {
                            tracing::warn!(error = %kill, "failed to kill signal-cli");
                        }
                        break format!("reading its output failed: {error}");
                    }
                },
                written = &mut running.writer => {
                    if let Err(kill) = running.child.kill().await {
                        tracing::warn!(error = %kill, "failed to kill signal-cli");
                    }
                    break match written {
                        Ok(Ok(())) => "its request queue closed".to_owned(),
                        Ok(Err(error)) => format!("{error:#}"),
                        Err(error) => format!("its stdin writer failed: {error}"),
                    };
                }
            }
        };
        shared.go_down(&reason).await;
        if started.elapsed() >= HEALTHY_RUN {
            backoff = BACKOFF_MIN;
        }
        tracing::warn!("signal-cli stopped ({reason}); restarting in {backoff:?}");
        running = loop {
            tokio::select! {
                () = notifications.closed() => return,
                () = tokio::time::sleep(backoff) => {}
            }
            backoff = (backoff * 2).min(BACKOFF_MAX);
            match launch(&shared, &cli_path, &account).await {
                Ok(running) => break running,
                Err(error) => {
                    tracing::warn!(
                        "restarting signal-cli failed: {error:#}; retrying in {backoff:?}"
                    );
                }
            }
        };
    }
}
