//! The runtime WebSocket (TS global `WebSocket`, Bun flavor with proxy
//! support) over tokio-tungstenite. The failure texts follow the Bun
//! runtime surface the old eukhe port probe-verified: connect failures are
//! `error` events `WebSocket connection to '<url>' failed: <cause>`, socket
//! and frame failures are `close` events with Bun's codes and reasons.

use std::sync::atomic::{AtomicU16, Ordering};
use std::sync::Arc;

use eukhe_types::pi_ai::IndexMap;
use eukhe_types::pi_ai::ProviderEnv;
use futures::{SinkExt, StreamExt};
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};
use tokio::net::TcpStream;
use tokio::sync::mpsc;
use tokio_tungstenite::tungstenite::client::IntoClientRequest;
use tokio_tungstenite::tungstenite::error::{CapacityError, ProtocolError};
use tokio_tungstenite::tungstenite::handshake::client::Request;
use tokio_tungstenite::tungstenite::http::{HeaderName, HeaderValue};
use tokio_tungstenite::tungstenite::protocol::frame::coding::CloseCode;
use tokio_tungstenite::tungstenite::protocol::CloseFrame;
use tokio_tungstenite::tungstenite::{Error as WsError, Message};
use tokio_tungstenite::WebSocketStream;
use url::Url;

use crate::utils::diagnostics::{ErrorObject, Thrown};
use crate::utils::node_http_proxy::resolve_http_proxy_url_for_target;

use super::websocket::{
    WebSocketData, WebSocketEvent, WebSocketLike, WebSocketListener, WebSocketListeners,
};

const READY_STATE_CONNECTING: u16 = 0;
const READY_STATE_OPEN: u16 = 1;
const READY_STATE_CLOSING: u16 = 2;
const READY_STATE_CLOSED: u16 = 3;

/// Close code the runtime reports for a close frame without a status.
const CLOSE_CODE_NO_STATUS: u16 = 1005;
/// Close code the runtime reports for a socket death without a close frame.
const CLOSE_CODE_ABNORMAL: u16 = 1006;
/// Close code the runtime reports for frames it cannot parse.
const CLOSE_CODE_PROTOCOL: u16 = 1002;
/// Close code for a message the runtime refuses as too big.
const CLOSE_CODE_TOO_BIG: u16 = 1009;
/// The runtime's close reason for an abrupt socket death.
const CONNECTION_ENDED_REASON: &str = "Connection ended";

enum Command {
    Send(String),
    Close(u16, String),
}

struct Shared {
    ready_state: AtomicU16,
    listeners: WebSocketListeners,
}

impl Shared {
    fn closed(&self, code: u16, reason: &str, was_clean: bool) {
        self.ready_state.store(READY_STATE_CLOSED, Ordering::SeqCst);
        self.listeners.dispatch(&WebSocketEvent::Close {
            code: Some(code),
            reason: Some(reason.to_owned()),
            was_clean: Some(was_clean),
        });
    }
}

/// A tokio-tungstenite socket driven by a worker task.
pub(crate) struct TungsteniteWebSocket {
    shared: Arc<Shared>,
    commands: mpsc::UnboundedSender<Command>,
}

impl TungsteniteWebSocket {
    /// `new WebSocket(url, { headers })`: starts connecting in the
    /// background; `open` (or `error` + `close`) follows.
    pub(crate) fn connect(
        url: &str,
        headers: IndexMap<String, String>,
        env: Option<&ProviderEnv>,
    ) -> Result<Arc<dyn WebSocketLike>, Thrown> {
        let syntax_error = |message: String| ErrorObject::named("SyntaxError", message).thrown();
        let mut request = url
            .into_client_request()
            .map_err(|error| syntax_error(format!("Failed to construct 'WebSocket': {error}")))?;
        for (name, value) in headers {
            let name = HeaderName::from_bytes(name.as_bytes())
                .map_err(|_| syntax_error(format!("Invalid header name: \"{name}\"")))?;
            let value = HeaderValue::try_from(value)
                .map_err(|error| syntax_error(format!("Invalid header value: {error}")))?;
            request.headers_mut().insert(name, value);
        }
        let target = if let Some(rest) = url.strip_prefix("wss:") {
            format!("https:{rest}")
        } else if let Some(rest) = url.strip_prefix("ws:") {
            format!("http:{rest}")
        } else {
            url.to_owned()
        };
        let proxy = resolve_http_proxy_url_for_target(&target, env)
            .map_err(crate::utils::diagnostics::thrown)?;

        let shared = Arc::new(Shared {
            ready_state: AtomicU16::new(READY_STATE_CONNECTING),
            listeners: WebSocketListeners::default(),
        });
        let (commands, receiver) = mpsc::unbounded_channel();
        tokio::spawn(run(
            request,
            url.to_owned(),
            proxy,
            Arc::clone(&shared),
            receiver,
        ));
        Ok(Arc::new(Self { shared, commands }))
    }
}

impl WebSocketLike for TungsteniteWebSocket {
    fn send(&self, data: String) -> Result<(), Thrown> {
        match self.shared.ready_state.load(Ordering::SeqCst) {
            READY_STATE_CONNECTING => Err(ErrorObject::named(
                "InvalidStateError",
                "Failed to execute 'send' on 'WebSocket': Still in CONNECTING state.",
            )
            .thrown()),
            READY_STATE_OPEN => {
                // A closed worker drops the frame like a closed socket does.
                let _ = self.commands.send(Command::Send(data));
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn close(&self, code: u16, reason: &str) {
        let state = self.shared.ready_state.load(Ordering::SeqCst);
        if state == READY_STATE_CLOSING || state == READY_STATE_CLOSED {
            return;
        }
        self.shared
            .ready_state
            .store(READY_STATE_CLOSING, Ordering::SeqCst);
        // The worker is gone once the socket closed on its own.
        let _ = self.commands.send(Command::Close(code, reason.to_owned()));
    }

    fn ready_state(&self) -> Option<u16> {
        Some(self.shared.ready_state.load(Ordering::SeqCst))
    }

    fn listen(&self) -> WebSocketListener {
        self.shared.listeners.subscribe()
    }
}

trait Io: AsyncRead + AsyncWrite + Unpin + Send {}
impl<T: AsyncRead + AsyncWrite + Unpin + Send> Io for T {}

type Socket = WebSocketStream<tokio_tungstenite::MaybeTlsStream<Box<dyn Io>>>;

/// HTTP `CONNECT` tunnel through `proxy` to the request's host.
async fn tunnel(proxy: &Url, host: &str, port: u16) -> std::io::Result<TcpStream> {
    let proxy_host = proxy.host_str().unwrap_or_default();
    let proxy_port = proxy.port_or_known_default().unwrap_or(80);
    let mut stream = TcpStream::connect((proxy_host, proxy_port)).await?;
    let mut connect = format!("CONNECT {host}:{port} HTTP/1.1\r\nHost: {host}:{port}\r\n");
    if !proxy.username().is_empty() {
        use base64::Engine as _;
        let credentials = format!(
            "{}:{}",
            proxy.username(),
            proxy.password().unwrap_or_default()
        );
        let encoded = base64::engine::general_purpose::STANDARD.encode(credentials);
        connect.push_str("Proxy-Authorization: Basic ");
        connect.push_str(&encoded);
        connect.push_str("\r\n");
    }
    connect.push_str("\r\n");
    stream.write_all(connect.as_bytes()).await?;
    let mut response = Vec::new();
    let mut byte = [0u8; 1];
    while !response.ends_with(b"\r\n\r\n") {
        if stream.read(&mut byte).await? == 0 {
            return Err(std::io::ErrorKind::UnexpectedEof.into());
        }
        response.push(byte[0]);
    }
    let status_line = response
        .split(|&byte| byte == b'\n')
        .next()
        .unwrap_or_default();
    let ok = String::from_utf8_lossy(status_line)
        .split_whitespace()
        .nth(1)
        .is_some_and(|status| status == "200");
    if ok {
        Ok(stream)
    } else {
        Err(std::io::ErrorKind::ConnectionRefused.into())
    }
}

async fn open(request: Request, proxy: Option<Url>) -> Result<Socket, WsError> {
    let uri = request.uri().clone();
    let host = uri.host().unwrap_or_default().to_owned();
    let secure = uri.scheme_str() == Some("wss");
    let port = uri.port_u16().unwrap_or(if secure { 443 } else { 80 });
    let stream: Box<dyn Io> = match &proxy {
        Some(proxy) => Box::new(tunnel(proxy, &host, port).await?),
        None => Box::new(TcpStream::connect((host.as_str(), port)).await?),
    };
    let (socket, _response) = tokio_tungstenite::client_async_tls(request, stream).await?;
    Ok(socket)
}

/// The Bun connect-failure text.
fn connect_failure_message(url: &str, error: &WsError) -> String {
    let cause = match error {
        WsError::Io(io) => {
            if url.starts_with("wss://")
                && !matches!(
                    io.kind(),
                    std::io::ErrorKind::ConnectionRefused | std::io::ErrorKind::TimedOut
                )
            {
                "TLS handshake failed".to_owned()
            } else {
                "Failed to connect".to_owned()
            }
        }
        WsError::Tls(_) => "TLS handshake failed".to_owned(),
        WsError::Http(_)
        | WsError::Protocol(ProtocolError::WrongHttpVersion | ProtocolError::WrongHttpMethod) => {
            "Expected 101 status code".to_owned()
        }
        WsError::Protocol(ProtocolError::SecWebSocketAcceptKeyMismatch) => {
            "Mismatch websocket accept header".to_owned()
        }
        other => other.to_string(),
    };
    format!("WebSocket connection to '{url}' failed: {cause}")
}

/// The Bun close event for a socket or frame failure.
fn read_failure_close(error: &WsError) -> (u16, String) {
    match error {
        WsError::Capacity(CapacityError::MessageTooLong { .. }) => {
            (CLOSE_CODE_TOO_BIG, String::new())
        }
        WsError::Protocol(ProtocolError::ResetWithoutClosingHandshake)
        | WsError::Io(_)
        | WsError::ConnectionClosed
        | WsError::AlreadyClosed
        | WsError::WriteBufferFull(_)
        | WsError::Capacity(_) => (CLOSE_CODE_ABNORMAL, CONNECTION_ENDED_REASON.to_owned()),
        WsError::Protocol(ProtocolError::NonZeroReservedBits) => {
            (1011, "Compression not implemented yet".to_owned())
        }
        WsError::Protocol(
            ProtocolError::InvalidOpcode(_)
            | ProtocolError::UnknownDataFrameType(_)
            | ProtocolError::UnknownControlFrameType(_),
        ) => (
            CLOSE_CODE_PROTOCOL,
            "Protocol error - unsupported control frame".to_owned(),
        ),
        other => (CLOSE_CODE_PROTOCOL, format!("Protocol error - {other}")),
    }
}

async fn run(
    request: Request,
    url: String,
    proxy: Option<Url>,
    shared: Arc<Shared>,
    mut commands: mpsc::UnboundedReceiver<Command>,
) {
    let socket = tokio::select! {
        command = commands.recv() => {
            // `close()` (or dropping the socket) while connecting.
            if command.is_some() {
                shared.closed(CLOSE_CODE_ABNORMAL, "", false);
            }
            return;
        }
        result = open(request, proxy) => result,
    };
    let socket = match socket {
        Ok(socket) => socket,
        Err(error) => {
            shared
                .ready_state
                .store(READY_STATE_CLOSED, Ordering::SeqCst);
            shared.listeners.dispatch(&WebSocketEvent::Error {
                message: Some(connect_failure_message(&url, &error)),
            });
            shared.closed(CLOSE_CODE_ABNORMAL, "", false);
            return;
        }
    };
    if shared
        .ready_state
        .compare_exchange(
            READY_STATE_CONNECTING,
            READY_STATE_OPEN,
            Ordering::SeqCst,
            Ordering::SeqCst,
        )
        .is_err()
    {
        // Closed between the handshake and here.
        let (mut sink, _) = socket.split();
        let _ = sink.close().await;
        shared.closed(CLOSE_CODE_ABNORMAL, "", false);
        return;
    }
    shared.listeners.dispatch(&WebSocketEvent::Open);

    let (mut sink, mut stream) = socket.split();
    let mut commands_open = true;
    loop {
        tokio::select! {
            command = commands.recv(), if commands_open => match command {
                Some(Command::Send(text)) => {
                    if let Err(error) = sink.send(Message::text(text)).await {
                        let (code, reason) = read_failure_close(&error);
                        shared.closed(code, &reason, false);
                        return;
                    }
                }
                Some(Command::Close(code, reason)) => {
                    let frame = CloseFrame {
                        code: CloseCode::from(code),
                        reason: reason.into(),
                    };
                    if sink.send(Message::Close(Some(frame))).await.is_err() {
                        shared.closed(code, "", false);
                        return;
                    }
                }
                None => {
                    // Every handle is gone: nobody can observe the socket.
                    commands_open = false;
                    let _ = sink.close().await;
                }
            },
            frame = stream.next() => match frame {
                Some(Ok(Message::Text(text))) => {
                    shared.listeners.dispatch(&WebSocketEvent::Message(WebSocketData::Text(text.as_str().to_owned())));
                }
                Some(Ok(Message::Binary(bytes))) => {
                    shared.listeners.dispatch(&WebSocketEvent::Message(WebSocketData::Binary(bytes.to_vec())));
                }
                Some(Ok(Message::Close(frame))) => {
                    match frame {
                        Some(frame) => shared.closed(u16::from(frame.code), frame.reason.as_str(), true),
                        None => shared.closed(CLOSE_CODE_NO_STATUS, "", true),
                    }
                    return;
                }
                Some(Ok(Message::Ping(_) | Message::Pong(_) | Message::Frame(_))) => {}
                Some(Err(error)) => {
                    let (code, reason) = read_failure_close(&error);
                    shared.closed(code, &reason, false);
                    return;
                }
                None => {
                    shared.closed(CLOSE_CODE_ABNORMAL, CONNECTION_ENDED_REASON, false);
                    return;
                }
            },
        }
    }
}
