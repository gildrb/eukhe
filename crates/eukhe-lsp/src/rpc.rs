//! JSON-RPC 2.0 over Content-Length framed stdio (the LSP base protocol):
//! request/response correlation, notifications, and dispatch of the
//! server's own requests and notifications to an [`Inbound`] handler.

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Duration;

use parking_lot::Mutex;
use serde_json::{json, Value};
use tokio::io::{AsyncBufReadExt, AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt, BufReader};
use tokio::sync::{mpsc, oneshot, watch};
use tokio::task::JoinHandle;

/// Largest accepted message body.
const MAX_MESSAGE_BYTES: usize = 64 * 1024 * 1024;

/// JSON-RPC `MethodNotFound`.
pub(crate) const METHOD_NOT_FOUND: i64 = -32601;
/// JSON-RPC `InvalidParams`.
pub(crate) const INVALID_PARAMS: i64 = -32602;

/// A JSON-RPC error object.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ResponseError {
    pub(crate) code: i64,
    pub(crate) message: String,
}

/// Why a request got no result.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub(crate) enum RpcFailure {
    #[error("the server connection closed: {0}")]
    Closed(String),
    #[error("timed out")]
    Timeout,
    #[error("{} (code {})", .0.message, .0.code)]
    Response(ResponseError),
}

/// Handles what a server sends on its own initiative.
///
/// Implementations answer each server request synchronously (the reader
/// task waits for the answer before reading on) and must not block.
pub(crate) trait Inbound: Send + Sync + 'static {
    /// A server notification (`textDocument/publishDiagnostics`,
    /// `$/progress`, ...).
    fn notification(&self, method: &str, params: Value);
    /// A server request; the result or error is sent back to the server.
    fn request(&self, method: &str, params: Value) -> Result<Value, ResponseError>;
}

type Pending = Mutex<HashMap<u64, oneshot::Sender<Result<Value, ResponseError>>>>;

/// One live JSON-RPC connection. Dropping it stops its reader and writer
/// tasks.
pub(crate) struct Transport {
    outbound: mpsc::UnboundedSender<Vec<u8>>,
    pending: Arc<Pending>,
    next_id: AtomicU64,
    closed: watch::Receiver<Option<String>>,
    tasks: [JoinHandle<()>; 2],
}

impl Drop for Transport {
    fn drop(&mut self) {
        for task in &self.tasks {
            task.abort();
        }
    }
}

impl Transport {
    /// Start the reader and writer tasks over a server's stdout and stdin.
    pub(crate) fn start<R, W>(reader: R, writer: W, inbound: Arc<dyn Inbound>) -> Self
    where
        R: AsyncRead + Unpin + Send + 'static,
        W: AsyncWrite + Unpin + Send + 'static,
    {
        let (outbound, queue) = mpsc::unbounded_channel();
        let pending: Arc<Pending> = Arc::default();
        let (closed_tx, closed) = watch::channel(None);
        let closed_tx = Arc::new(closed_tx);
        let writer_task = tokio::spawn(write_loop(
            writer,
            queue,
            Arc::clone(&closed_tx),
            Arc::clone(&pending),
        ));
        let reader_task = tokio::spawn(read_loop(
            BufReader::new(reader),
            outbound.clone(),
            inbound,
            closed_tx,
            Arc::clone(&pending),
        ));
        Self {
            outbound,
            pending,
            next_id: AtomicU64::new(1),
            closed,
            tasks: [reader_task, writer_task],
        }
    }

    /// Why the connection closed, once it has.
    pub(crate) fn closed(&self) -> Option<String> {
        self.closed.borrow().clone()
    }

    /// Send a request and wait at most `timeout` for its result; a timed-out
    /// request is cancelled on the server (`$/cancelRequest`).
    pub(crate) async fn request(
        &self,
        method: &str,
        params: Value,
        timeout: Duration,
    ) -> Result<Value, RpcFailure> {
        let id = self.next_id.fetch_add(1, Ordering::Relaxed);
        let (sender, receiver) = oneshot::channel();
        self.pending.lock().insert(id, sender);
        if let Err(failure) =
            self.send(&json!({ "jsonrpc": "2.0", "id": id, "method": method, "params": params }))
        {
            self.pending.lock().remove(&id);
            return Err(failure);
        }
        match tokio::time::timeout(timeout, receiver).await {
            Ok(Ok(Ok(result))) => Ok(result),
            Ok(Ok(Err(error))) => Err(RpcFailure::Response(error)),
            Ok(Err(_)) => Err(RpcFailure::Closed(
                self.closed()
                    .unwrap_or_else(|| "connection dropped".to_owned()),
            )),
            Err(_) => {
                self.pending.lock().remove(&id);
                // The server may already be gone; the timeout is the answer.
                let _ = self.notify("$/cancelRequest", &json!({ "id": id }));
                Err(RpcFailure::Timeout)
            }
        }
    }

    /// Send a notification.
    pub(crate) fn notify(&self, method: &str, params: &Value) -> Result<(), RpcFailure> {
        self.send(&json!({ "jsonrpc": "2.0", "method": method, "params": params }))
    }

    fn send(&self, message: &Value) -> Result<(), RpcFailure> {
        if let Some(reason) = self.closed() {
            return Err(RpcFailure::Closed(reason));
        }
        self.outbound
            .send(frame(message))
            .map_err(|_| RpcFailure::Closed("the writer stopped".to_owned()))
    }
}

fn frame(message: &Value) -> Vec<u8> {
    let body = message.to_string();
    let mut bytes = format!("Content-Length: {}\r\n\r\n", body.len()).into_bytes();
    bytes.extend_from_slice(body.as_bytes());
    bytes
}

fn close(closed: &watch::Sender<Option<String>>, pending: &Pending, reason: String) {
    closed.send_if_modified(|current| {
        if current.is_some() {
            return false;
        }
        *current = Some(reason);
        true
    });
    // Dropping the senders fails every waiter with `Closed`.
    pending.lock().clear();
}

async fn write_loop<W: AsyncWrite + Unpin>(
    mut writer: W,
    mut queue: mpsc::UnboundedReceiver<Vec<u8>>,
    closed: Arc<watch::Sender<Option<String>>>,
    pending: Arc<Pending>,
) {
    while let Some(bytes) = queue.recv().await {
        let written = async {
            writer.write_all(&bytes).await?;
            writer.flush().await
        }
        .await;
        if let Err(error) = written {
            close(&closed, &pending, format!("write failed: {error}"));
            return;
        }
    }
}

async fn read_loop<R: AsyncRead + Unpin>(
    mut reader: BufReader<R>,
    outbound: mpsc::UnboundedSender<Vec<u8>>,
    inbound: Arc<dyn Inbound>,
    closed: Arc<watch::Sender<Option<String>>>,
    pending: Arc<Pending>,
) {
    let reason = loop {
        let body = match read_frame(&mut reader).await {
            Ok(Some(body)) => body,
            Ok(None) => break "the server exited".to_owned(),
            Err(error) => break format!("read failed: {error}"),
        };
        let Ok(message) = serde_json::from_slice::<Value>(&body) else {
            tracing::warn!("dropping a non-JSON LSP message");
            continue;
        };
        let method = message.get("method").and_then(Value::as_str);
        let id = message.get("id").cloned();
        match (method, id) {
            (Some(method), Some(id)) => {
                let params = message.get("params").cloned().unwrap_or(Value::Null);
                let reply = match inbound.request(method, params) {
                    Ok(result) => json!({ "jsonrpc": "2.0", "id": id, "result": result }),
                    Err(error) => json!({
                        "jsonrpc": "2.0",
                        "id": id,
                        "error": { "code": error.code, "message": error.message },
                    }),
                };
                if outbound.send(frame(&reply)).is_err() {
                    break "the writer stopped".to_owned();
                }
            }
            (Some(method), None) => {
                inbound.notification(
                    method,
                    message.get("params").cloned().unwrap_or(Value::Null),
                );
            }
            (None, Some(id)) => {
                let Some(id) = id.as_u64() else {
                    tracing::warn!(%id, "dropping an LSP response with a foreign id");
                    continue;
                };
                let Some(waiter) = pending.lock().remove(&id) else {
                    continue;
                };
                let outcome = match message.get("error") {
                    Some(error) => Err(ResponseError {
                        code: error
                            .get("code")
                            .and_then(Value::as_i64)
                            .unwrap_or_default(),
                        message: error
                            .get("message")
                            .and_then(Value::as_str)
                            .unwrap_or_default()
                            .to_owned(),
                    }),
                    None => Ok(message.get("result").cloned().unwrap_or(Value::Null)),
                };
                // The requester may have timed out and left.
                let _ = waiter.send(outcome);
            }
            (None, None) => tracing::warn!("dropping an LSP message without method or id"),
        }
    };
    close(&closed, &pending, reason);
}

/// One framed message body; `None` at a clean end of stream. Lines before
/// a `Content-Length` header that are not headers (a server banner on
/// stdout) are skipped.
async fn read_frame<R: AsyncRead + Unpin>(
    reader: &mut BufReader<R>,
) -> std::io::Result<Option<Vec<u8>>> {
    let mut length = None;
    loop {
        let mut line = String::new();
        if reader.read_line(&mut line).await? == 0 {
            return Ok(None);
        }
        let line = line.trim_end_matches(['\r', '\n']);
        if line.is_empty() {
            if let Some(length) = length {
                if length > MAX_MESSAGE_BYTES {
                    return Err(std::io::Error::other(format!(
                        "message of {length} bytes exceeds the limit"
                    )));
                }
                let mut body = vec![0; length];
                reader.read_exact(&mut body).await?;
                return Ok(Some(body));
            }
            continue;
        }
        if let Some((name, value)) = line.split_once(':') {
            if name.trim().eq_ignore_ascii_case("content-length") {
                length = Some(value.trim().parse::<usize>().map_err(|error| {
                    std::io::Error::other(format!("bad Content-Length: {error}"))
                })?);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Silent;

    impl Inbound for Silent {
        fn notification(&self, _method: &str, _params: Value) {}
        fn request(&self, method: &str, _params: Value) -> Result<Value, ResponseError> {
            Err(ResponseError {
                code: METHOD_NOT_FOUND,
                message: method.to_owned(),
            })
        }
    }

    #[tokio::test]
    async fn frames_skip_banners_and_keep_trailing_bytes() {
        let bytes = b"server banner\r\nContent-Length: 7\r\nContent-Type: x\r\n\r\n{\"a\":1}Content-Length: 2\r\n\r\n{}";
        let mut reader = BufReader::new(&bytes[..]);
        assert_eq!(
            read_frame(&mut reader).await.unwrap(),
            Some(b"{\"a\":1}".to_vec())
        );
        assert_eq!(read_frame(&mut reader).await.unwrap(), Some(b"{}".to_vec()));
        assert_eq!(read_frame(&mut reader).await.unwrap(), None);
    }

    #[tokio::test]
    async fn responses_correlate_and_server_exit_fails_waiters() {
        let (client, server) = tokio::io::duplex(4096);
        let (client_read, client_write) = tokio::io::split(client);
        let (server_read, mut server_write) = tokio::io::split(server);
        let transport = Transport::start(client_read, client_write, Arc::new(Silent));
        let server = tokio::spawn(async move {
            let mut reader = BufReader::new(server_read);
            let request: Value =
                serde_json::from_slice(&read_frame(&mut reader).await.unwrap().unwrap()).unwrap();
            let reply = json!({ "jsonrpc": "2.0", "id": request["id"], "result": { "echo": request["params"] } });
            server_write.write_all(&frame(&reply)).await.unwrap();
            let _second = read_frame(&mut reader).await.unwrap();
        });
        let result = transport
            .request("echo", json!([1, 2]), Duration::from_secs(5))
            .await
            .unwrap();
        assert_eq!(result, json!({ "echo": [1, 2] }));
        let second = transport.request("hang", Value::Null, Duration::from_secs(5));
        let (second, server_done) = tokio::join!(second, server);
        server_done.unwrap();
        assert_eq!(
            second,
            Err(RpcFailure::Closed("the server exited".to_owned()))
        );
    }
}
