//! The loopback HTTP/1.1 server: the app's files, and the WebSocket
//! upgrade (`.../api/ws`) that starts one daemon bridge per tab.

use std::convert::Infallible;
use std::sync::Arc;

use futures::SinkExt;
use http_body_util::Full;
use hyper::body::{Bytes, Incoming};
use hyper::header::{self, HeaderValue};
use hyper::{Method, Request, Response, StatusCode};
use hyper_util::rt::TokioIo;
use tokio_tungstenite::tungstenite::handshake::derive_accept_key;
use tokio_tungstenite::tungstenite::protocol::Role;
use tokio_tungstenite::tungstenite::Message;
use tokio_tungstenite::WebSocketStream;

use crate::bridge::Bridge;
use crate::protocol::ServerFrame;
use crate::{DaemonLauncher, DashboardConfig};

/// The path suffix of the bridge's WebSocket.
const SOCKET_PATH: &str = "/api/ws";

/// The app's content policy: its own files and its own socket only.
const CONTENT_SECURITY_POLICY: &str = "default-src 'self'; script-src 'self'; style-src 'self'; img-src 'self' data:; connect-src 'self'; base-uri 'none'; frame-ancestors 'none'";

type Body = Full<Bytes>;

/// Accept connections until the task is dropped; each runs on its own
/// task.
#[tracing::instrument(skip_all)]
pub(crate) async fn serve<L: DaemonLauncher>(
    listener: tokio::net::TcpListener,
    config: Arc<DashboardConfig>,
    launcher: Arc<L>,
) -> anyhow::Result<()> {
    loop {
        let (stream, peer) = listener.accept().await?;
        let config = Arc::clone(&config);
        let launcher = Arc::clone(&launcher);
        tokio::spawn(async move {
            let service = hyper::service::service_fn(move |request| {
                let config = Arc::clone(&config);
                let launcher = Arc::clone(&launcher);
                async move { Ok::<_, Infallible>(route(request, config, launcher)) }
            });
            if let Err(error) = hyper::server::conn::http1::Builder::new()
                .serve_connection(TokioIo::new(stream), service)
                .with_upgrades()
                .await
            {
                tracing::debug!(%peer, %error, "an HTTP connection failed");
            }
        });
    }
}

/// The answer to one request.
fn route<L: DaemonLauncher>(
    request: Request<Incoming>,
    config: Arc<DashboardConfig>,
    launcher: Arc<L>,
) -> Response<Body> {
    let path = request.uri().path().to_string();
    if path.ends_with(SOCKET_PATH) {
        return upgrade(request, config, launcher);
    }
    if request.method() != Method::GET && request.method() != Method::HEAD {
        return plain(StatusCode::METHOD_NOT_ALLOWED, "method not allowed");
    }
    let Some(asset) = crate::assets::lookup(&path) else {
        return plain(StatusCode::NOT_FOUND, "not found");
    };
    let mut response = Response::new(Full::new(Bytes::from_static(asset.body.as_bytes())));
    let headers = response.headers_mut();
    headers.insert(
        header::CONTENT_TYPE,
        HeaderValue::from_static(asset.content_type),
    );
    // A new eukhe build serves new files under the same names.
    headers.insert(header::CACHE_CONTROL, HeaderValue::from_static("no-cache"));
    headers.insert(
        header::CONTENT_SECURITY_POLICY,
        HeaderValue::from_static(CONTENT_SECURITY_POLICY),
    );
    headers.insert(
        header::X_CONTENT_TYPE_OPTIONS,
        HeaderValue::from_static("nosniff"),
    );
    headers.insert(
        header::REFERRER_POLICY,
        HeaderValue::from_static("no-referrer"),
    );
    response
}

/// Upgrade the request to the bridge's WebSocket and start the bridge on
/// the upgraded connection.
fn upgrade<L: DaemonLauncher>(
    mut request: Request<Incoming>,
    config: Arc<DashboardConfig>,
    launcher: Arc<L>,
) -> Response<Body> {
    let headers = request.headers();
    let wants_websocket = headers
        .get(header::UPGRADE)
        .and_then(|value| value.to_str().ok())
        .is_some_and(|value| value.eq_ignore_ascii_case("websocket"));
    let version_13 = headers
        .get(header::SEC_WEBSOCKET_VERSION)
        .is_some_and(|value| value.as_bytes() == b"13");
    let key = headers.get(header::SEC_WEBSOCKET_KEY).cloned();
    let (Some(key), true, true, true) = (
        key,
        wants_websocket,
        version_13,
        request.method() == Method::GET,
    ) else {
        return plain(StatusCode::BAD_REQUEST, "expected a WebSocket upgrade");
    };
    let upgrading = hyper::upgrade::on(&mut request);
    tokio::spawn(async move {
        let upgraded = match upgrading.await {
            Ok(upgraded) => upgraded,
            Err(error) => {
                tracing::debug!(%error, "the WebSocket upgrade failed");
                return;
            }
        };
        let socket =
            WebSocketStream::from_raw_socket(TokioIo::new(upgraded), Role::Server, None).await;
        match Bridge::connect(config, launcher.as_ref()).await {
            Ok(bridge) => bridge.run(socket).await,
            Err(error) => {
                tracing::warn!(error = %format!("{error:#}"), "the daemon is not reachable");
                close_with_error(socket, &format!("{error:#}")).await;
            }
        }
    });
    let mut response = Response::new(Full::new(Bytes::new()));
    *response.status_mut() = StatusCode::SWITCHING_PROTOCOLS;
    let headers = response.headers_mut();
    headers.insert(header::UPGRADE, HeaderValue::from_static("websocket"));
    headers.insert(header::CONNECTION, HeaderValue::from_static("Upgrade"));
    match HeaderValue::from_str(&derive_accept_key(key.as_bytes())) {
        Ok(accept) => {
            headers.insert(header::SEC_WEBSOCKET_ACCEPT, accept);
            response
        }
        Err(error) => plain(StatusCode::INTERNAL_SERVER_ERROR, &error.to_string()),
    }
}

/// Close a tab's socket whose bridge could not start, with the reason
/// (the tab shows it and retries).
async fn close_with_error<S>(mut socket: WebSocketStream<S>, reason: &str)
where
    S: tokio::io::AsyncRead + tokio::io::AsyncWrite + Unpin,
{
    let frame = ServerFrame::Unavailable {
        error: reason.to_string(),
    }
    .to_text();
    if let Err(error) = socket.send(Message::text(frame)).await {
        tracing::debug!(%error, "telling the tab failed");
    }
    if let Err(error) = socket.close(None).await {
        tracing::debug!(%error, "closing the tab's socket failed");
    }
}

fn plain(status: StatusCode, text: &str) -> Response<Body> {
    let mut response = Response::new(Full::new(Bytes::from(text.to_string())));
    *response.status_mut() = status;
    response.headers_mut().insert(
        header::CONTENT_TYPE,
        HeaderValue::from_static("text/plain; charset=utf-8"),
    );
    response
}
