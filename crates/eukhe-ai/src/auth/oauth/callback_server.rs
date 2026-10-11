//! Loopback OAuth redirect handler shared by the browser sign-in flows. Port
//! of `auth/oauth/callback-server.ts`; a minimal HTTP/1.1 server on tokio
//! replaces `node:http`.

use std::fmt::{self, Write as _};
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use eukhe_chord::context::{AbortController, AbortSignal};
use futures::future::BoxFuture;
use tokio::io::{AsyncReadExt as _, AsyncWriteExt as _};
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::watch;
use tokio_util::sync::CancellationToken;

use crate::auth::errors::js_error;
use crate::auth::types::{AuthPrompt, AuthPromptKind, ProviderAuthInteraction};
use crate::utils::diagnostics::Thrown;
use crate::utils::oauth_page::{oauth_error_html, oauth_success_html};

/// Finishes the sign-in with the received code.
pub type CompleteFn<T> = Arc<dyn Fn(String) -> BoxFuture<'static, Result<T, Thrown>> + Send + Sync>;

/// Options of [`start_oauth_callback_server`].
pub struct OAuthCallbackServerOptions<T> {
    /// Provider name used on the browser page, for example `OpenAI`.
    pub provider_name: String,
    /// Address to listen on.
    pub host: String,
    /// Port to listen on; `0` picks a free port.
    pub port: u16,
    pub path: String,
    /// Host in `redirect_uri` when it differs from `host`, for example `localhost`.
    pub redirect_host: Option<String>,
    /// Expected `state` parameter. `None` when the provider does not send one.
    pub state: Option<String>,
    /// Finishes the sign-in with the received code before the browser page is
    /// sent, so the page can show exchange failures. Pass a function returning
    /// the code to exchange it later.
    pub complete: CompleteFn<T>,
    pub signal: Option<AbortSignal>,
    pub timeout_ms: Option<u64>,
}

type WaitResult<T> = Result<Option<T>, Thrown>;

struct Flags {
    claimed: bool,
    settled: bool,
}

struct Shared<T> {
    provider_name: String,
    path: String,
    state: Option<String>,
    complete: CompleteFn<T>,
    flags: Mutex<Flags>,
    result: watch::Sender<Option<WaitResult<T>>>,
    /// Stops the abort listener and the timeout timer.
    settled_token: CancellationToken,
    /// Stops accepting connections (node `server.close()`); requests already
    /// being handled finish.
    shutdown: CancellationToken,
    listener: ClosableListener,
}

/// A listener that [`ClosableListener::close`] closes at once, so the port
/// is free when `close()` returns (node closes the listening handle
/// synchronously).
pub(crate) struct ClosableListener {
    inner: Mutex<Option<TcpListener>>,
}

impl ClosableListener {
    pub(crate) fn new(listener: TcpListener) -> Self {
        Self {
            inner: Mutex::new(Some(listener)),
        }
    }

    /// Accept one connection; `None` once closed.
    pub(crate) async fn accept(&self) -> Option<std::io::Result<TcpStream>> {
        std::future::poll_fn(|cx| {
            let guard = self.inner.lock().unwrap_or_else(PoisonError::into_inner);
            match guard.as_ref() {
                Some(listener) => listener
                    .poll_accept(cx)
                    .map(|accepted| Some(accepted.map(|(stream, _)| stream))),
                None => std::task::Poll::Ready(None),
            }
        })
        .await
    }

    /// Close the listening socket.
    pub(crate) fn close(&self) {
        self.inner
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .take();
    }
}

impl<T> Shared<T> {
    fn flags(&self) -> std::sync::MutexGuard<'_, Flags> {
        self.flags.lock().unwrap_or_else(PoisonError::into_inner)
    }

    fn finish(&self, result: WaitResult<T>) {
        {
            let mut flags = self.flags();
            if flags.settled {
                return;
            }
            flags.settled = true;
        }
        self.settled_token.cancel();
        self.result.send_replace(Some(result));
    }
}

/// A running callback server. Clones share the server.
pub struct OAuthCallbackServer<T> {
    pub redirect_uri: String,
    shared: Arc<Shared<T>>,
}

impl<T> Clone for OAuthCallbackServer<T> {
    fn clone(&self) -> Self {
        Self {
            redirect_uri: self.redirect_uri.clone(),
            shared: Arc::clone(&self.shared),
        }
    }
}

impl<T> fmt::Debug for OAuthCallbackServer<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("OAuthCallbackServer")
            .field("redirect_uri", &self.redirect_uri)
            .finish_non_exhaustive()
    }
}

impl<T: Clone + Send + Sync + 'static> OAuthCallbackServer<T> {
    /// Resolves with the result of `complete`, or `None` after `cancel()`.
    /// Fails when the provider redirects with an error, `complete` fails, the
    /// signal aborts, or the timeout elapses.
    ///
    /// # Errors
    ///
    /// See above.
    pub async fn wait(&self) -> Result<Option<T>, Thrown> {
        let mut receiver = self.shared.result.subscribe();
        loop {
            if let Some(result) = receiver.borrow_and_update().clone() {
                return result;
            }
            if receiver.changed().await.is_err() {
                return Err(js_error("OAuth callback server closed"));
            }
        }
    }

    /// Stop waiting for the browser unless a callback is already being completed.
    pub fn cancel(&self) {
        let claimed = self.shared.flags().claimed;
        if !claimed {
            self.shared.finish(Ok(None));
        }
    }

    /// Fail the wait (if still pending) and stop the server.
    pub fn close(&self) {
        self.shared
            .finish(Err(js_error("OAuth callback server closed")));
        self.shared.shutdown.cancel();
        self.shared.listener.close();
    }
}

/// Start the loopback server.
///
/// # Errors
///
/// `Login cancelled` when the signal already aborted; the bind error (an
/// [`std::io::Error`], e.g. `AddrInUse`) when the port is taken.
pub async fn start_oauth_callback_server<T: Clone + Send + Sync + 'static>(
    options: OAuthCallbackServerOptions<T>,
) -> Result<OAuthCallbackServer<T>, Thrown> {
    if options.signal.as_ref().is_some_and(AbortSignal::aborted) {
        return Err(js_error("Login cancelled"));
    }

    let listener = TcpListener::bind((options.host.as_str(), options.port))
        .await
        .map_err(|error| -> Thrown { Arc::new(error) })?;
    let port = listener
        .local_addr()
        .map_err(|error| -> Thrown { Arc::new(error) })?
        .port();

    let (result, _) = watch::channel(None);
    let shared = Arc::new(Shared {
        provider_name: options.provider_name,
        path: options.path,
        state: options.state,
        complete: options.complete,
        flags: Mutex::new(Flags {
            claimed: false,
            settled: false,
        }),
        result,
        settled_token: CancellationToken::new(),
        shutdown: CancellationToken::new(),
        listener: ClosableListener::new(listener),
    });

    tokio::spawn(accept_loop(Arc::clone(&shared)));

    if let Some(signal) = options.signal {
        let listener_shared = Arc::clone(&shared);
        tokio::spawn(async move {
            tokio::select! {
                _ = signal.cancelled() => listener_shared.finish(Err(js_error("Login cancelled"))),
                () = listener_shared.settled_token.cancelled() => {}
            }
        });
    }
    if let Some(timeout_ms) = options.timeout_ms {
        let timer_shared = Arc::clone(&shared);
        tokio::spawn(async move {
            tokio::select! {
                () = tokio::time::sleep(Duration::from_millis(timeout_ms)) => {
                    let message = format!("{} sign-in timed out", timer_shared.provider_name);
                    timer_shared.finish(Err(js_error(message)));
                }
                () = timer_shared.settled_token.cancelled() => {}
            }
        });
    }

    let redirect_host = options.redirect_host.unwrap_or(options.host);
    let redirect_host = if redirect_host.contains(':') {
        format!("[{redirect_host}]")
    } else {
        redirect_host
    };
    Ok(OAuthCallbackServer {
        redirect_uri: format!("http://{redirect_host}:{port}{}", shared.path),
        shared,
    })
}

async fn accept_loop<T: Send + Sync + 'static>(shared: Arc<Shared<T>>) {
    loop {
        tokio::select! {
            biased;
            () = shared.shutdown.cancelled() => return,
            accepted = shared.listener.accept() => match accepted {
                None => return,
                Some(Ok(stream)) => {
                    // Like node's `server.close()`, closing only stops accepting:
                    // requests on accepted connections still complete.
                    tokio::spawn(handle_connection(stream, Arc::clone(&shared)));
                }
                Some(Err(error)) => {
                    // The node server's "error" event.
                    shared.finish(Err(Arc::new(error)));
                }
            },
        }
    }
}

/// A parsed request line.
pub(crate) struct HttpRequestHead {
    pub(crate) method: String,
    pub(crate) target: String,
}

/// Read one HTTP/1.1 request head; `None` when the peer closed first.
pub(crate) async fn read_request_head(stream: &mut TcpStream) -> Option<HttpRequestHead> {
    let mut buffer = Vec::new();
    let mut chunk = [0_u8; 4096];
    while !buffer.windows(4).any(|window| window == b"\r\n\r\n") {
        let read = stream.read(&mut chunk).await.ok()?;
        if read == 0 {
            return None;
        }
        buffer.extend_from_slice(&chunk[..read]);
        if buffer.len() > 64 * 1024 {
            return None;
        }
    }
    let head = String::from_utf8_lossy(&buffer);
    let mut parts = head.lines().next()?.split(' ');
    Some(HttpRequestHead {
        method: parts.next()?.to_owned(),
        target: parts.next()?.to_owned(),
    })
}

/// Write an HTML response and close the connection.
pub(crate) async fn send_html(
    stream: &mut TcpStream,
    status: u16,
    extra_headers: &[(&str, &str)],
    html: &str,
) {
    let reason = reqwest::StatusCode::from_u16(status)
        .ok()
        .and_then(|code| code.canonical_reason())
        .unwrap_or_default();
    let mut response = format!("HTTP/1.1 {status} {reason}\r\n");
    for (name, value) in extra_headers {
        let _ = write!(response, "{name}: {value}\r\n");
    }
    let _ = write!(
        response,
        "content-length: {}\r\nconnection: close\r\n\r\n{html}",
        html.len()
    );
    // The browser may already have gone away; there is nobody to report to.
    if stream.write_all(response.as_bytes()).await.is_ok() {
        let _ = stream.shutdown().await;
    }
}

async fn send_page(stream: &mut TcpStream, status: u16, html: &str) {
    send_html(
        stream,
        status,
        &[
            ("content-type", "text/html; charset=utf-8"),
            ("cache-control", "no-store"),
        ],
        html,
    )
    .await;
}

/// `searchParams.get(name)`.
pub(crate) fn query_param(url: &url::Url, name: &str) -> Option<String> {
    url.query_pairs()
        .find(|(key, _)| key == name)
        .map(|(_, value)| value.into_owned())
}

async fn handle_connection<T: Send + Sync + 'static>(
    mut stream: TcpStream,
    shared: Arc<Shared<T>>,
) {
    let Some(head) = read_request_head(&mut stream).await else {
        return;
    };
    let Ok(url) = url::Url::parse("http://localhost").and_then(|base| base.join(&head.target))
    else {
        send_page(
            &mut stream,
            404,
            &oauth_error_html("Callback route not found.", None),
        )
        .await;
        return;
    };
    if head.method != "GET" || url.path() != shared.path {
        send_page(
            &mut stream,
            404,
            &oauth_error_html("Callback route not found.", None),
        )
        .await;
        return;
    }
    if let Some(expected) = &shared.state {
        if query_param(&url, "state").as_deref() != Some(expected.as_str()) {
            send_page(&mut stream, 400, &oauth_error_html("State mismatch.", None)).await;
            return;
        }
    }
    let already_handled = {
        let flags = shared.flags();
        flags.claimed || flags.settled
    };
    if already_handled {
        send_page(
            &mut stream,
            409,
            &oauth_error_html("This sign-in has already been handled.", None),
        )
        .await;
        return;
    }
    if let Some(error) = query_param(&url, "error").filter(|error| !error.is_empty()) {
        let description = query_param(&url, "error_description").unwrap_or(error);
        let provider_name = &shared.provider_name;
        send_page(
            &mut stream,
            400,
            &oauth_error_html(
                &format!("{provider_name} authorization failed."),
                Some(&description),
            ),
        )
        .await;
        shared.finish(Err(js_error(format!(
            "{provider_name} authorization failed: {description}"
        ))));
        return;
    }
    let Some(code) = query_param(&url, "code").filter(|code| !code.is_empty()) else {
        send_page(
            &mut stream,
            400,
            &oauth_error_html("Missing authorization code.", None),
        )
        .await;
        return;
    };
    shared.flags().claimed = true;
    let provider_name = shared.provider_name.clone();
    match (shared.complete)(code).await {
        Ok(value) => {
            send_page(
                &mut stream,
                200,
                &oauth_success_html(&format!(
                    "Signed in to {provider_name}. You may now close this page."
                )),
            )
            .await;
            shared.finish(Ok(Some(value)));
        }
        Err(error) => {
            send_page(
                &mut stream,
                502,
                &oauth_error_html(
                    &format!("{provider_name} sign-in failed."),
                    Some(&error.to_string()),
                ),
            )
            .await;
            shared.finish(Err(error));
        }
    }
}

/// Outcome of [`wait_for_callback_or_manual_input`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CallbackOrManual<T> {
    Callback { value: T },
    Manual { input: String },
}

/// Aborts the manual prompt when dropped (the TS `finally`).
struct AbortOnDrop(AbortController);

impl Drop for AbortOnDrop {
    fn drop(&mut self) {
        self.0.abort(None);
    }
}

/// Wait for the browser callback, or for the user to paste the code or
/// redirect URL when the browser cannot reach the loopback server (for
/// example over SSH). Without a callback server only the manual prompt is used.
///
/// # Errors
///
/// The callback wait's failure, or the manual prompt's failure.
pub async fn wait_for_callback_or_manual_input<T: Clone + Send + Sync + 'static>(
    interaction: &ProviderAuthInteraction,
    callback: Option<&OAuthCallbackServer<T>>,
    message: &str,
    placeholder: &str,
) -> Result<CallbackOrManual<T>, Thrown> {
    let manual_abort = AbortOnDrop(AbortController::new());
    let manual_error: Arc<Mutex<Option<Thrown>>> = Arc::new(Mutex::new(None));
    let prompt = AuthPrompt {
        signal: Some(manual_abort.0.signal()),
        kind: AuthPromptKind::ManualCode {
            message: message.to_owned(),
            placeholder: Some(placeholder.to_owned()),
        },
    };
    let manual_interaction = interaction.clone();
    let manual_callback = callback.cloned();
    let manual_error_slot = Arc::clone(&manual_error);
    let manual = tokio::spawn(async move {
        match manual_interaction.prompt(prompt).await {
            Ok(input) => {
                if let Some(callback) = &manual_callback {
                    callback.cancel();
                }
                Some(input)
            }
            Err(error) => {
                *manual_error_slot
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner) = Some(error);
                if let Some(callback) = &manual_callback {
                    callback.cancel();
                }
                None
            }
        }
    });
    let take_manual_error = || {
        manual_error
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    };

    let value = match callback {
        Some(callback) => callback.wait().await?,
        None => None,
    };
    if let Some(error) = take_manual_error() {
        return Err(error);
    }
    if let Some(value) = value {
        return Ok(CallbackOrManual::Callback { value });
    }
    let input = manual.await.map_err(|error| js_error(error.to_string()))?;
    if let Some(error) = take_manual_error() {
        return Err(error);
    }
    drop(manual_abort);
    Ok(CallbackOrManual::Manual {
        input: input.unwrap_or_default(),
    })
}

#[cfg(test)]
#[path = "callback_server_tests.rs"]
mod tests;
